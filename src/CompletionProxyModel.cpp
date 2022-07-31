// SPDX-FileCopyrightText: 2021 Nheko Contributors
// SPDX-FileCopyrightText: 2022 Nheko Contributors
//
// SPDX-License-Identifier: GPL-3.0-or-later

#include "CompletionProxyModel.h"

#include <QRegularExpression>
#include <QTextBoundaryFinder>

#include "CompletionModelRoles.h"
#include "Logging.h"
#include "Utils.h"

#include "libsais16.h"

#include <fmt/ranges.h>
#include <optional>
#include <queue>
#include <ranges>
#include <set>
#include <span>

struct CompletionProxyModel::Index
{
    QString text;
    std::vector<int> item_starts;
    std::vector<int> SA;
    std::vector<int> invSA;

    struct index_range
    {
        std::size_t lo = 0;
        std::size_t hi = 0;

        [[nodiscard]] auto begin() const noexcept { return std::ranges::iota_view(lo, hi).begin(); }
        [[nodiscard]] auto end() const noexcept { return std::ranges::iota_view(lo, hi).end(); }
        [[nodiscard]] bool empty() const { return lo == hi; }
    };

    struct prefix_range : index_range
    {
        int m = 0;

        QString prefix;

        friend auto to_string(prefix_range p)
        {
            return fmt::format("{}:[{}..{})", p.m, p.lo, p.hi);
        };
    };

    Index(QString &&text_, std::vector<int> &&item_starts_)
      : text(std::move(text_))
      , item_starts(std::move(item_starts_))
    {
        item_starts.push_back(text.size());

        SA.resize(text.size());
        if (auto ec = libsais16(text.utf16(), SA.data(), text.size(), 0, nullptr); ec != 0) {
            nhlog::ui()->error("Failed to build autocomplete index! No completions for you!");
            text.clear();
            item_starts = {0};
            SA.clear();
            invSA.clear();
            return;
        }
        //         std::erase_if(SA, [&](int i){return text[i] != u8'\0' or
        //         QChar(text[i]).isLowSurrogate();});

        invSA.resize(text.size(), -1);
        for (auto i : index_range{0, SA.size()}) {
            invSA[SA[i]] = i;
        }
    }

    [[nodiscard]] static std::pair<char32_t, int> ucs4_at(QStringRef str, int i)
    {
        if (str[i].isHighSurrogate()) {
            if (i + 1 < str.size()) {
                return std::pair{QChar::surrogateToUcs4(str[i], str[i + 1]), 2};
            } else {
                return {QChar::Null, 1};
            }
        } else {
            return std::pair{str[i].unicode(), 1};
        }
    }

    [[nodiscard]] int item_at(int text_pos) const noexcept
    {
        assert(not item_starts.empty());
        assert(text_pos >= item_starts.front());
        return std::ranges::lower_bound(item_starts, text_pos, std::less_equal{}) -
               item_starts.begin() - 1;
    }

    [[nodiscard]] prefix_range empty_prefix() const noexcept
    {
        return {{.lo = 0, .hi = SA.size()}, 0, {}};
    }

    [[nodiscard]] prefix_range extend_prefix(prefix_range p, QChar c) const noexcept
    {
        auto next_char = [this, k = p.m](std::size_t i) { return text[SA[i] + k]; };
        p.lo           = *std::ranges::lower_bound(p, c, std::less{}, next_char);
        p.hi           = *std::ranges::upper_bound(p, c, std::less{}, next_char);
        p.m += 1;
        p.prefix.push_back(c);
        return p;
    }

    [[nodiscard]] prefix_range extend_prefix(prefix_range p, QStringRef str) const noexcept
    {
        for (auto c : str) {
            p = extend_prefix(p, c);
        }

        return p;
    }

    [[nodiscard]] prefix_range range_of(QStringRef str) const noexcept
    {
        return extend_prefix(empty_prefix(), str);
    }

    [[nodiscard]] prefix_range concat_prefix(prefix_range p1, prefix_range p2) const noexcept
    {
        auto pred = [this, k = p1.m](int x) { return invSA[SA[x] + k]; };
        p1.lo     = *std::ranges::lower_bound(p1, p2.lo, std::less{}, pred);
        p1.hi     = *std::ranges::upper_bound(p1, p2.hi - 1, std::less{}, pred);
        p1.m += p2.m;
        p1.prefix += p2.prefix;
        return p1;
    };

    [[nodiscard]] std::pair<prefix_range, QChar> first_subrange(prefix_range p) const noexcept
    {
        auto next_char = [this, k = p.m](std::size_t i) { return text[SA[i] + k]; };

        // skip null character range if present
        p.lo = *std::ranges::upper_bound(p, QChar(), std::less{}, next_char);

        if (p.empty()) {
            return {p, QChar()};
        }

        const auto c = next_char(p.lo);
        p.hi         = *std::ranges::upper_bound(p, c, std::less{}, next_char);
        p.m += 1;
        p.prefix.push_back(c);

        return {p, c};
    }

    [[nodiscard]] std::pair<prefix_range, QChar>
    next_subrange(prefix_range p, prefix_range s) const noexcept
    {
        p.lo = s.hi;
        return first_subrange(p);
    }

    [[nodiscard]] std::pair<prefix_range, char32_t>
    first_subrange_utf32(prefix_range p) const noexcept
    {
        auto [s, c] = first_subrange(p);

        if (c.isHighSurrogate()) {
            auto [s2, c2] = first_subrange(s);
            return {s2, QChar::surrogateToUcs4(c, c2)};
        }

        return {s, c.unicode()};
    }

    [[nodiscard]] std::pair<prefix_range, char32_t>
    next_subrange_utf32(prefix_range p, prefix_range s) const noexcept
    {
        p.lo = s.hi;
        return first_subrange_utf32(p);
    }

    struct result_item
    {
        prefix_range range;
        std::size_t distance = 0;
    };

    std::vector<result_item> search(QStringRef pattern, std::size_t max_edits)
    {
        // Approximate String Matching Using Compressed Suffix Arrays
        // DOI: 10.1007/978-3-540-27801-6_33

        nhlog::ui()->flush_on(spdlog::level::trace);
//         fmt::print(stderr, "index: search('{}', {})\n", pattern.toUtf8(), max_edits);

        auto F = std::vector<prefix_range>(pattern.size() + 1);
        for (auto i : index_range{0, static_cast<std::size_t>(pattern.size())}) {
            F[i] = range_of(pattern.mid(i));
//             fmt::print(stderr, "index: F[{}]: {}\n", i, to_string(F[i]));
        }

        auto results = std::vector<result_item>{};

        enum class edit
        {
            nop,
            ins,
            del,
            rep,
            swap
        };

        int ilevel = 0;
        auto kapproximate =
          [&](auto kapproximate, prefix_range p, int i, std::size_t edits, edit last_op) {
              ilevel += 1;
              const auto indent = std::string(ilevel, '=');
//               fmt::print(stderr, "index: {}kapproximate({}, {}, {})\n", indent, to_string(p), i, edits);

              if (auto r = concat_prefix(p, F[i]); not r.empty()) {
//                   fmt::print(stderr, "index:     report: {} . {} => {}\n", to_string(p), to_string(F[i]), to_string(r));
                  // TODO figure out result deduplication part from paper
                  results.push_back({r, edits});
              }

              if (p.empty() or edits == max_edits) {
                  ilevel -= 1;
                  return;
              }

              // TODO adjacent character swaps
              for (auto j = i; j < pattern.size() and not p.empty();) {
//                   fmt::print(stderr, "index: {}  j:{} p:{}\n", indent, j, to_string(p));
                  const auto [p_char, l] = ucs4_at(pattern, j);
                  const auto j_next      = j + l;

                  // deletion at j
                  // dont do del-ins, or ins-del since that pair is same as replace, but in 2 edits
                  if (last_op != edit::ins) {
                      kapproximate(kapproximate, p, j_next, edits + 1, edit::del);
                  }

                  assert(not p.empty());
                  for (auto [s, c]    = first_subrange_utf32(p); s.lo != p.hi;
                       std::tie(s, c) = next_subrange_utf32(p, s)) {
//                       fmt::print(stderr, "index: {}    subrange {} {} of {}\n", indent, to_string(s), uint32_t(c), to_string(p));

                      // also skip code point matching pattern since using that is not an edit
                      if (c == p_char) {
                          continue;
                      }

                      // replacemen at j
                      kapproximate(kapproximate, s, j_next, edits + 1, edit::rep);

                      // insertion at j
                      if (last_op != edit::del) {
                          kapproximate(kapproximate, s, j, edits + 1, edit::ins);
                      }
                  }

                  j = j_next;
                  p = extend_prefix(p, pattern.mid(j, l));
              }

              // try also inserions after patterns end
//               fmt::print(stderr, "index: {}  insertions at the end of pattern\n", indent, to_string(p), i, edits);
              if (last_op != edit::del) {
                  for (auto [s, c]    = first_subrange_utf32(p); s.lo != p.hi;
                       std::tie(s, c) = next_subrange_utf32(p, s)) {
//                       fmt::print(stderr, "index: {}    subrange {} {} of {}\n", indent, to_string(s), uint32_t(c), to_string(p));

                      // insertion at j
                      kapproximate(kapproximate, s, pattern.size(), edits + 1, edit::ins);
                  }
              }

              ilevel -= 1;
          };

        kapproximate(kapproximate, empty_prefix(), 0, 0, edit::nop);

        return results;
    }

    std::vector<int> top_items(QStringRef pattern, std::size_t max_distance, std::size_t max_items)
    {
        fmt::print(stderr,
                   "index: top_items(pattern='{}', max_distance={}, max_items={})\n",
                   std::string_view(reinterpret_cast<const char *>(pattern.data()), pattern.size()),
                   max_distance,
                   max_items);
        const auto t0 = std::chrono::steady_clock::now();

        const auto found_ranges = search(pattern, max_distance);

        const auto t1 = std::chrono::steady_clock::now();

        std::vector<uint8_t> weights;
        weights.resize(item_starts.size());

        // TODO rank something like this?
        // exact match to full text
        // exact match to partial text TODO need word boundaries
        // exact prefix match of full text
        // exact prefix match of partial text TODO need word boundaries
        // then by increasing edit_distance

        std::vector<int> items;

//         fmt::print(stderr, "index: CANDIDATES ranges:{}:\n", found_ranges.size());
        for (auto r : found_ranges) {
//             fmt::print(stderr, "index:   RANGE {} ~{}\n", to_string(r.range), r.distance);
            for (auto prefix_id : r.range) {
                const auto match_pos     = SA[prefix_id];
                const auto edit_distance = r.distance;
                const auto length        = r.range.m;
                const auto item          = item_at(match_pos);

                const bool is_exact        = (edit_distance == 0);
                const bool is_prefix_match = (match_pos == 0 or text[match_pos - 1].isNull());
                const bool is_full_string_match =
                  is_prefix_match and (text[match_pos + length].isNull());

                const uint8_t weight =
                  +1 + 2 * std::min(max_distance - edit_distance, std::size_t{7}) +
                  16 * is_prefix_match + 32 * is_exact + 64 * (is_exact and is_prefix_match) +
                  128 * (is_exact and is_full_string_match);

//                 const auto item_start_pos = item_starts[item];
//                 const auto item_length = item_starts[item + 1] - item_start_pos;
//                 auto full_text = std::string_view(reinterpret_cast<const
//                 char*>(text.data()), text.size()); auto item_text =
//                 full_text.substr(item_start_pos, item_length);
//
//                 const auto match_start_pos = match_pos - item_start_pos;
//                 const auto match_end_pos = match_start_pos + length;
//
//                 fmt::print(stderr,
//                     "index:     {} p:{} i:{}[{}] w:{} ~{}"
//                     " [..[{}..{}]..{}]"
//                     " '{}'"
//                     "\n",
//                     prefix_id, match_pos, item, item_starts[item], weight,
//                     edit_distance, match_start_pos, match_end_pos, item_length,
//                     item_text
//                 );
//                 fmt::print(stderr,
//                     "index:         [{}[{}]{}]\n",
//                     item_text.substr(0, match_start_pos),
//                     item_text.substr(match_start_pos, length),
//                     item_text.substr(match_end_pos)
//                 );

                if (weights[item] == 0) {
                    // found this item first time, add to item list
                    items.push_back(item);
                }
                weights[item] = std::max(weights[item], weight);
            }
        }

        const auto t2 = std::chrono::steady_clock::now();

        auto item_weight = [&](int i) { return weights[i]; };

        // get best max_items results
        if (items.size() > max_items) {
            std::ranges::nth_element(items, items.begin() + max_items, std::greater{}, item_weight);
            items.resize(max_items);
        }

        const auto t3 = std::chrono::steady_clock::now();

        // sort final results descending by weight, then ascending by prefix_id
        // TODO add static item weights to mix in ranking function
        auto sort_key = [&, this](int i) {
            return std::pair(256 - weights[i], invSA[item_starts[i]]);
        };
        std::ranges::sort(items, std::less{}, sort_key);

        const auto t4 = std::chrono::steady_clock::now();

//         fmt::print(stderr, "index: RESULTS {}:\n", items.size());
        //         for (auto item: items) {
        //             const auto item_text_pos = item_starts[item];
        //             auto first = std::string_view(reinterpret_cast<const char*>(text.data() +
        //             item_text_pos)); auto second = std::string_view(first.end() + 1);
        //             fmt::print(stderr, "index:     {} w:{} '{}' '{}'\n", item, weights[item],
        //             first, second);
        //         }

        using fmilli = std::chrono::duration<double, std::milli>;
        fmt::print(stderr, "index:     search: {} ms\n", fmilli(t1 - t0).count());
        fmt::print(stderr, "index:     rank&dedup: {} ms\n", fmilli(t2 - t1).count());
        fmt::print(stderr, "index:     nth_element: {} ms\n", fmilli(t3 - t2).count());
        fmt::print(stderr, "index:     sort: {} ms\n", fmilli(t4 - t3).count());
        fmt::print(stderr, "index:     totals: {} ms\n", fmilli(t4 - t0).count());

        return items;
    }
};

CompletionProxyModel::CompletionProxyModel(QAbstractItemModel *model,
                                           int max_mistakes,
                                           size_t max_completions,
                                           QObject *parent)
  : QAbstractProxyModel(parent)
  , maxMistakes_(max_mistakes)
  , max_completions_(max_completions)
{
    setSourceModel(model);

    max_completions_ = std::numeric_limits<size_t>::max();

    fmt::print(
      stderr,
      "CompletionProxyModel: =================================================================\n");

    {
        const auto start_at = std::chrono::steady_clock::now();

        const auto row_count = sourceModel()->rowCount();

        QString text;
        std::vector<int> item_starts;
        item_starts.reserve(row_count);

        for (int i = 0; i < row_count; i++) {
            auto string1 = sourceModel()
                             ->data(sourceModel()->index(i, 0), CompletionModel::SearchRole)
                             .toString()
                             .toLower();

            auto string2 = sourceModel()
                             ->data(sourceModel()->index(i, 0), CompletionModel::SearchRole2)
                             .toString()
                             .toLower();

            item_starts.push_back(text.size());
            text.append(string1);
            text.push_back('\0');
            text.append(string2);
            text.push_back('\0');
        }

        const auto concat_at = std::chrono::steady_clock::now();

        index_.reset(new Index(std::move(text), std::move(item_starts)));

        const auto build_at = std::chrono::steady_clock::now();

        using fmilli = std::chrono::duration<double, std::milli>;
        fmt::print(stderr,
                   "CompletionProxyModel: libsais: concat full text: {} ms\n",
                   fmilli(concat_at - start_at).count());
        fmt::print(stderr,
                   "CompletionProxyModel: libsais: build SA: {} ms\n",
                   fmilli(build_at - concat_at).count());
        fmt::print(stderr,
                   "CompletionProxyModel: libsais: total: {} ms\n",
                   fmilli(build_at - start_at).count());
        fmt::print(
          stderr, "CompletionProxyModel: item count: {}\n", index_->item_starts.size() - 1);
        fmt::print(stderr, "CompletionProxyModel: full_text size: {}\n", index_->text.size());
    }

    // initialize default mapping
    mapping.resize(std::min(max_completions_, static_cast<size_t>(model->rowCount())));
    std::iota(mapping.begin(), mapping.end(), 0);

    connect(
      this,
      &CompletionProxyModel::newSearchString,
      this,
      [this](QString s) {
          if (not s.isEmpty() and QStringLiteral("#@~:").contains(s.front())) {
              s = s.mid(1);
          }
          searchString_ = s.toLower();
          invalidate();
      },
      Qt::QueuedConnection);
}

CompletionProxyModel::~CompletionProxyModel() = default;

void
CompletionProxyModel::invalidate()
{
    beginResetModel();
    // return default model data, if no search string
    if (not searchString_.isEmpty()) {
        const auto start_at    = std::chrono::steady_clock::now();
        mapping                = index_->top_items(&searchString_,
                                    std::clamp(searchString_.length() / 3, 0, maxMistakes_),
                                    max_completions_);
        const auto end_at      = std::chrono::steady_clock::now();
        const auto search_time = std::chrono::duration<double, std::milli>(end_at - start_at);
        fmt::print(stderr,
                   "CompletionProxyModel: search '{}': {} ms, {} results\n",
                   searchString_.toUtf8(),
                   search_time.count(),
                   mapping.size());
    }
    endResetModel();
}

QHash<int, QByteArray>
CompletionProxyModel::roleNames() const
{
    return this->sourceModel()->roleNames();
}

int
CompletionProxyModel::rowCount(const QModelIndex &) const
{
    if (searchString_.isEmpty())
        return std::min(
          static_cast<int>(std::min<size_t>(max_completions_, std::numeric_limits<int>::max())),
          sourceModel()->rowCount());
    else
        return (int)mapping.size();
}

QModelIndex
CompletionProxyModel::mapFromSource(const QModelIndex &sourceIndex) const
{
    // return default model data, if no search string
    if (searchString_.isEmpty()) {
        return index(sourceIndex.row(), 0);
    }

    for (int i = 0; i < (int)mapping.size(); i++) {
        if (sourceIndex.row() >= 0 and mapping[i] == sourceIndex.row()) {
            return index(i, 0);
        }
    }
    return QModelIndex();
}

QModelIndex
CompletionProxyModel::mapToSource(const QModelIndex &proxyIndex) const
{
    auto row = proxyIndex.row();

    // return default model data, if no search string
    if (searchString_.isEmpty()) {
        return index(row, 0);
    }

    if (row < 0 || row >= (int)mapping.size())
        return QModelIndex();

    return sourceModel()->index(mapping[row], 0);
}

QModelIndex
CompletionProxyModel::index(int row, int column, const QModelIndex &) const
{
    return createIndex(row, column);
}

QModelIndex
CompletionProxyModel::parent(const QModelIndex &) const
{
    return QModelIndex{};
}
int
CompletionProxyModel::columnCount(const QModelIndex &) const
{
    return sourceModel()->columnCount();
}

QVariant
CompletionProxyModel::completionAt(int i) const
{
    if (i >= 0 && i < rowCount())
        return data(index(i, 0), CompletionModel::CompletionRole);
    else
        return {};
}

void
CompletionProxyModel::setSearchString(QString s)
{
    emit newSearchString(s);
}
