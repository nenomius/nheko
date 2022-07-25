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

#include <ranges>
#include <span>

struct CompletionProxyModel::Index
{
    // concatenated text of all searchable items
    // delimited by '\0' to exclude matches across item boundaries
    QString text;

    // bitmask indicating positions of word aboundaries according to QTextBoundaryFinder
    std::vector<bool> word_boundaries; // text.size + 1

    // positions in concatenated text where each item starts, plus size of whole text
    // text of item i is in half-open range [item_starts[i], item_starts[i+1])
    std::vector<int> item_starts; // item count + 1

    // suffix array of concatenated text and its inverse
    std::vector<int> SA;    // text.size
    std::vector<int> invSA; // text.size

    struct index_range
    {
        std::size_t lo = 0;
        std::size_t hi = 0;

        auto begin() const noexcept { return std::ranges::iota_view(lo, hi).begin(); }
        auto end() const noexcept { return std::ranges::iota_view(lo, hi).end(); }
        bool empty() const { return lo == hi; }
    };

    struct prefix_range : index_range
    {
        int length = 0;
    };

    struct match_range : prefix_range
    {
        int edits = 0;
    };

    Index(QString &&text_, std::vector<int> &&item_starts_)
      : text(std::move(text_))
      , item_starts(std::move(item_starts_))
    {
        assert(item_starts.front() == 0);
        item_starts.push_back(text.size());

        text.shrink_to_fit();
        item_starts.shrink_to_fit();

        SA.resize(text.size());
        if (auto ec = libsais16(text.utf16(), SA.data(), text.size(), 0, nullptr); ec != 0) {
            nhlog::ui()->error("Failed to build autocomplete index! No completions for you!");

            // reset to empty index
            text.clear();
            word_boundaries = {false};
            item_starts = {0};
            SA.clear();
            invSA.clear();

            return;
        }

        invSA.resize(text.size());
        for (auto i : index_range{0, SA.size()}) {
            invSA[SA[i]] = i;
        }

        word_boundaries.resize(text.size() + 1);
        auto bounds = QTextBoundaryFinder(QTextBoundaryFinder::BoundaryType::Word, text);
        bounds.toStart();
        do {
            word_boundaries[bounds.position()] = true;
        } while (bounds.toNextBoundary() != -1);
    }

    int item_at(int text_pos) const noexcept
    {
        assert(not item_starts.empty());
        assert(text_pos < text.size());
        return std::ranges::lower_bound(item_starts, text_pos, std::less_equal{}) -
               item_starts.begin() - 1;
    }

    prefix_range empty_prefix() const noexcept { return {{.lo = 0, .hi = SA.size()}, 0}; }

    prefix_range extend_prefix(prefix_range p, QChar c) const noexcept
    {
        auto next_char = [this, k = p.length](std::size_t i) { return text[SA[i] + k]; };

        p.lo = *std::ranges::lower_bound(p, c, std::less{}, next_char);
        p.hi = *std::ranges::upper_bound(p, c, std::less{}, next_char);
        p.length += 1;

        return p;
    }

    prefix_range extend_prefix(prefix_range p, uint c) const noexcept
    {
        if (not QChar::requiresSurrogates(c)) {
            return extend_prefix(p, QChar(c));
        } else {
            p = extend_prefix(p, QChar::highSurrogate(c));
            return extend_prefix(p, QChar::lowSurrogate(c));
        }
    }

    prefix_range extend_prefix(prefix_range p, std::span<const uint> str) const noexcept
    {
        for (auto c : str) {
            p = extend_prefix(p, c);
        }

        return p;
    }

    prefix_range range_of(std::span<const uint> str) const noexcept
    {
        return extend_prefix(empty_prefix(), str);
    }

    prefix_range concat_prefix(prefix_range p1, prefix_range p2) const noexcept
    {
        auto pred = [this, k = p1.length](int x) { return invSA[SA[x] + k]; };
        p1.lo     = *std::ranges::lower_bound(p1, p2.lo, std::less{}, pred);
        p1.hi     = *std::ranges::upper_bound(p1, p2.hi - 1, std::less{}, pred);
        p1.length += p2.length;
        return p1;
    };

    std::pair<prefix_range, QChar> first_subrange(prefix_range p) const noexcept
    {
        auto next_char = [this, k = p.length](std::size_t i) { return text[SA[i] + k]; };

        // skip null character range if present
        p.lo = *std::ranges::upper_bound(p, QChar(), std::less{}, next_char);

        if (p.empty()) {
            return {p, QChar()};
        }

        const auto c = next_char(p.lo);
        p.hi         = *std::ranges::upper_bound(p, c, std::less{}, next_char);
        p.length += 1;

        return {p, c};
    }

    std::pair<prefix_range, QChar> next_subrange(prefix_range p, prefix_range s) const noexcept
    {
        p.lo = s.hi;
        return first_subrange(p);
    }

    std::pair<prefix_range, uint> first_subrange_utf32(prefix_range p) const noexcept
    {
        auto [s, c] = first_subrange(p);

        if (c.isHighSurrogate()) {
            auto [s2, c2] = first_subrange(s);
            return {s2, QChar::surrogateToUcs4(c, c2)};
        }

        return {s, c.unicode()};
    }

    std::pair<prefix_range, uint> next_subrange_utf32(prefix_range p, prefix_range s) const noexcept
    {
        p.lo = s.hi;
        return first_subrange_utf32(p);
    }

    template<typename F>
    void for_each_succesor_of(prefix_range p, const F &f)
    {
        auto [s, c] = first_subrange_utf32(p);
        while (s.lo != p.hi) {
            f(s, c);
            std::tie(s, c) = next_subrange_utf32(p, s);
        }
    }

    std::vector<match_range> search(QStringView pattern, std::size_t max_edits)
    {
        return search(pattern.toUcs4(), max_edits);
    }

    std::vector<match_range> search(std::span<const uint> pattern, int max_edits)
    {
        // Approximate String Matching Using Compressed Suffix Arrays
        // DOI: 10.1007/978-3-540-27801-6_33

        auto pattern_suffixes = std::vector<prefix_range>(pattern.size() + 1);
        for (auto i : index_range{0, pattern.size()}) {
            pattern_suffixes[i] = range_of(pattern.subspan(i));
        }

        auto results = std::vector<match_range>{};

        enum class edit_op
        {
            noop,
            ins,
            del,
            rep,
            swap,
        };

        auto kapproximate =
          [&](auto self, prefix_range p, std::size_t i, int edits, edit_op last_op) {
              if (auto r = concat_prefix(p, pattern_suffixes[i]); not r.empty()) {
                  results.push_back({r, edits});
              }

              if (p.empty() or edits >= max_edits) {
                  return;
              }

              for (auto j = i; j < pattern.size() and not p.empty(); ++j) {
                  // deletion at j
                  // dont do del-ins, or ins-del since that pair is same as replace, but in 2 edits
                  if (last_op != edit_op::ins) {
                      self(self, p, j + 1, edits + 1, edit_op::del);
                  }

                  // swap at j with j+1
                  if (j + 1 < pattern.size()) {
                      auto p_next = extend_prefix(p, pattern[j + 1]);
                      p_next      = extend_prefix(p_next, pattern[j]);
                      self(self, p_next, j + 2, edits + 1, edit_op::swap);
                  }

                  for_each_succesor_of(p, [&](prefix_range s, uint c) {
                      if (c == pattern[j]) {
                          return;
                      }

                      // replacemen at j
                      self(self, s, j + 1, edits + 1, edit_op::rep);

                      // insertion at j
                      if (last_op != edit_op::del) {
                          self(self, s, j, edits + 1, edit_op::ins);
                      }
                  });

                  // step unedited
                  p = extend_prefix(p, pattern[j]);
              }

              // try also insertions at pattern end
              if (last_op != edit_op::del) {
                  auto j = pattern.size();
                  for_each_succesor_of(p, [&](prefix_range s, uint c) {
                      std::ignore = c;

                      // insertion at j
                      self(self, s, j, edits + 1, edit_op::ins);
                  });
              }
          };

        kapproximate(kapproximate, empty_prefix(), 0, 0, edit_op::noop);

        return results;
    }

    float match_weight(int item, QStringView item_text, int edits, int match_start, int match_end)
    {
        // TODO add static item weights to mix in ranking function

        const auto text_size      = item_text.size();
        const auto secondary_text = item_text.indexOf(QChar());

        const bool is_exact       = (edits == 0);
        const bool is_full_prefix = (match_start == 0 or item_text[match_start - 1].isNull());
        const bool is_full_suffix = (match_end == text_size or item_text[match_end].isNull());
        const bool is_full_match  = is_full_prefix and is_full_suffix;
        const bool is_word_prefix = word_boundaries[item_starts[item] + match_start];
        const bool is_word_suffix = word_boundaries[item_starts[item] + match_end];
        const bool is_word_match  = is_word_prefix and is_word_suffix;
        const bool is_secondary   = (match_start > secondary_text);

        const auto lexical_order =
          (1.0f - static_cast<float>(invSA[item_starts[item]]) / text.size());

        // WARNING i got these numbers by poking around in my ass
        auto w = 0.0f;
        w += 3.50f * is_exact;
        w += 2.00f * is_full_prefix;
        w += 1.00f * is_full_match;
        w += 1.10f * (is_word_prefix + 0.5 * is_word_match);
        w += 2.00f * (1.0f - static_cast<float>(match_start) / text_size);
        w -= 1.00f * is_secondary;
        w -= 1.50f * edits;
        w += 0.10f * lexical_order;

        return w;
    }

    std::vector<int> top_items(QStringView pattern, std::size_t max_distance, std::size_t max_items)
    {
        const auto found_ranges = search(pattern, max_distance);

        std::vector<float> weights;
        weights.resize(item_starts.size(), NAN);

        std::vector<int> items;

        std::size_t duplicates = 0;
        for (auto r : found_ranges) {
            for (auto prefix_id : r) {
                const auto edit_distance  = r.edits;
                const auto length         = r.length;
                const auto item           = item_at(SA[prefix_id]);
                const auto item_start_pos = item_starts[item];
                const auto item_text_size = item_starts[item + 1] - item_start_pos;
                const auto match_start    = SA[prefix_id] - item_start_pos;
                const auto match_end      = match_start + length;
                const auto item_text      = text.midRef(item_start_pos, item_text_size);

                const auto weight =
                  match_weight(item, item_text, edit_distance, match_start, match_end);

                if (std::isnan(weights[item])) {
                    // found this item first time, add to item list
                    items.push_back(item);
                    weights[item] = weight;
                } else {
                    ++duplicates;
                    weights[item] = std::max(weights[item], weight);
                }
            }
        }

        auto item_weight = [&](int i) { return weights[i]; };

        // get best max_items results
        if (items.size() > max_items) {
            std::ranges::nth_element(items, items.begin() + max_items, std::greater{}, item_weight);
            items.resize(max_items);
        }

        std::ranges::sort(items, std::greater{}, item_weight);

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

    index_.reset(new Index(std::move(text), std::move(item_starts)));

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
    const auto max_edits = std::clamp(searchString_.length() / 3, 0, maxMistakes_);

    beginResetModel();
    // return default model data, if no search string
    if (not searchString_.isEmpty()) {
        mapping = index_->top_items(searchString_, max_edits, max_completions_);
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
        if (mapping[i] == sourceIndex.row()) {
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
