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

#include <optional>
#include <queue>
#include <span>
#include <fmt/ranges.h>
#include <ranges>
#include <set>

struct CompletionProxyModel::Index
{
    std::u8string text;
    std::vector<int> SA;
    std::vector<int> invSA;
    std::vector<int> item_starts;

    struct prefix_range
    {
        std::size_t lo = 0;
        std::size_t hi = 0;
        int m = 0;

        friend auto to_string(prefix_range p)
        {
            return fmt::format("{}:[{}..{})", p.m, p.lo, p.hi);
        };

        struct iterator
        {
            using value_type = std::size_t;
            using difference_type = std::ptrdiff_t;

            value_type x = 0;

            iterator() {}
            explicit iterator(value_type x): x(x) {}

            value_type operator*() const noexcept {return x;}
            value_type operator[](difference_type n) const noexcept {return x + n;}
            iterator& operator++() noexcept {++x; return *this;}
            iterator& operator--() noexcept {--x; return *this;}
            iterator operator++(int) noexcept {auto tmp = *this; ++x; return tmp;}
            iterator operator--(int) noexcept {auto tmp = *this; --x; return tmp;}
            friend difference_type operator-(iterator l, iterator r) noexcept {return static_cast<difference_type>(l.x) - static_cast<difference_type>(r.x);}
            friend iterator operator-(iterator l, difference_type n) noexcept {return iterator{l.x - n};}
            friend iterator operator+(iterator i, difference_type n) noexcept {return iterator{i.x + n};}
            friend iterator operator+(difference_type n, iterator i) noexcept {return iterator{i.x + n};}
            iterator &operator-=(difference_type n) noexcept {x -= n; return *this;}
            iterator &operator+=(difference_type n) noexcept {x += n; return *this;}
            auto operator<=>(const iterator &rhs) const noexcept = default;
        };

        static_assert(std::random_access_iterator<iterator>);

        [[nodiscard]] auto begin() const noexcept {return iterator{lo};}
        [[nodiscard]] auto end() const noexcept {return iterator{hi};}
        [[nodiscard]] bool empty() const {return lo == hi;}
    };

    Index(std::u8string &&text_, std::vector<int> &&item_starts_)
        : text(std::move(text_))
        , item_starts(std::move(item_starts_))
    {
        SA.resize(text.size());
        item_starts.push_back(text.size());

        std::iota(SA.begin(), SA.end(), 0);
        sort_prefixes(SA, 0);

        invSA.resize(text.size());
        for (int i = 0, I = SA.size(); i < I; ++i) {
            invSA[SA[i]] = i;
        }
    }

    [[nodiscard]] int item_at(int text_pos) const noexcept
    {
        assert(not item_starts.empty());
        assert(text_pos >= item_starts.front());
        return std::ranges::lower_bound(item_starts, text_pos, std::less_equal{}) - item_starts.begin() - 1;
    }

    [[nodiscard]] prefix_range empty_prefix() const noexcept
    {
        return {.lo = 0, .hi = SA.size(), .m = 0};
    }

    [[nodiscard]] prefix_range extend_prefix(prefix_range p, char8_t c) const noexcept
    {
        auto next_char = [this, k = p.m](std::size_t i){return text[SA[i] + k];};
        p.lo = *std::ranges::lower_bound(p, c, std::less{}, next_char);
        p.hi = *std::ranges::upper_bound(p, c, std::less{}, next_char);
        p.m += 1;
        return p;
    }

    [[nodiscard]] prefix_range extend_prefix(prefix_range p, std::u8string_view str) const noexcept
    {
        for (auto c: str) {
            p = extend_prefix(p, c);
        }

        return p;
    }

    [[nodiscard]] prefix_range range_of(std::u8string_view str) const noexcept
    {
        return extend_prefix(empty_prefix(), str);
    }

    [[nodiscard]] prefix_range concat_prefix(prefix_range p1, prefix_range p2) const noexcept
    {
        auto pred = [this, k = p1.m](int x){return invSA[SA[x] + k];};
        p1.lo = *std::ranges::lower_bound(p1, p2.lo, std::less{}, pred);
        p1.hi = *std::ranges::upper_bound(p1, p2.hi - 1, std::less{}, pred);
        p1.m += p2.m;
        return p1;
    };

    [[nodiscard]] std::pair<prefix_range, char8_t> first_subrange(prefix_range p) const noexcept
    {
        auto next_char = [this, k = p.m](std::size_t i){return text[SA[i] + k];};
        const auto c = next_char(p.lo);
        p.hi = *std::ranges::upper_bound(p, c, std::less{}, next_char);
        p.m += 1;
        return {p, c};
    }

    [[nodiscard]] std::pair<prefix_range, char8_t> next_subrange(prefix_range p, prefix_range s) const noexcept
    {
        p.lo = s.hi;
        return first_subrange(p);
    }

    struct result_item
    {
        prefix_range range;
        std::size_t distance = 0;
    };

    std::vector<result_item> search(std::u8string_view pattern, std::size_t max_distance)
    {
//         nhlog::ui()->debug("index: search('{}', {})", std::string_view(reinterpret_cast<const char*>(pattern.data()), pattern.size()), max_distance);

        auto F = std::vector<prefix_range>(pattern.size());
        for (std::size_t i = 0; i < pattern.size(); ++i) {
            F[i] = range_of(pattern.substr(i));
//             nhlog::ui()->debug("index: F[{}]: {}", i, to_string(F[i]));
        }

        auto results = std::vector<result_item>{};

        auto kapproximate = [&](auto kapproximate, prefix_range p, std::size_t i, std::size_t distance)
        {
//             nhlog::ui()->debug("index: kapproximate({}, {}, {})", to_string(p), i, distance);

            if (auto r = concat_prefix(p, F[i]); not r.empty()) {
//                 nhlog::ui()->debug("index:     report: {} . {} => {}", to_string(p), to_string(F[i]), to_string(r));
                results.push_back({r, distance});
            }

            if (p.empty() or distance == max_distance) {
                return;
            }

            // FIXME account to UTF-8 multibyteness on edits
            // TODO adjacent character swaps
            for (auto j = i; j < pattern.size(); ++j, p = extend_prefix(p, pattern[j])) {
//                 nhlog::ui()->debug("index:     j:{} p:{}", j, to_string(p));

                // deletion at j
                if (j + 1 < pattern.size()) {
                    kapproximate(kapproximate, p, j + 1, distance + 1);
                }

                for (auto [s, c] = first_subrange(p); s.lo != p.hi; std::tie(s, c) = next_subrange(p, s)) {
                    if (c == u8'\0' or c == pattern[j]) {
                        // skip null character, thats for delimiting only
                        // also skip character matching pattern since using that is not an edit
                        continue;
                    }

                    // replacemen at j
                    if (j + 1 < pattern.size()) {
                        kapproximate(kapproximate, s, j + 1, distance + 1);
                    }

                    // insertion at j
                    kapproximate(kapproximate, s, j, distance + 1);
                }
            }
        };

        if (pattern.empty()) {
            results.push_back({empty_prefix(), 0});
        } else {
            kapproximate(kapproximate, empty_prefix(), 0, 0);
        }

        return results;
    }

    std::vector<int> top_items(std::u8string_view pattern, std::size_t max_distance, std::size_t max_items)
    {
        nhlog::ui()->debug("index: top_items(pattern='{}', max_distance={}, max_items={})", std::string_view(reinterpret_cast<const char*>(pattern.data()), pattern.size()), max_distance, max_items);
        const auto t0     = std::chrono::steady_clock::now();

        const auto found_ranges = search(pattern , max_distance);

        const auto t1     = std::chrono::steady_clock::now();

        std::vector<uint8_t> weights;
        weights.resize(item_starts.size());

        // TODO rank something like this?
        // exact match to full text
        // exact match to partial text TODO need word boundaries
        // exact prefix match of full text
        // exact prefix match of partial text TODO need word boundaries
        // then by increasing edit_distance

        std::vector<int> items;

//         nhlog::ui()->debug("index: CANDIDATES ranges:{}:", results.size());
        for (auto r: found_ranges) {
//             nhlog::ui()->debug("index:   RANGE {} ~{}", to_string(r.range), r.distance);
            for (auto prefix_id: r.range) {
                const auto match_pos = SA[prefix_id];
                const auto edit_distance = r.distance;
                const auto length = r.range.m;
                const auto item = item_at(match_pos);

                const bool is_exact = (edit_distance == 0);
                const bool is_prefix_match = (match_pos == 0 or text[match_pos - 1] == u8'\0');
                const bool is_full_string_match = is_prefix_match and (text[match_pos + length] == u8'\0');

                const uint8_t weight =
                    + 1
                    + 2 * std::min(max_distance - edit_distance, std::size_t{7})
                    + 16 * is_prefix_match
                    + 32 * is_exact
                    + 64 * (is_exact and is_prefix_match)
                    + 128 * (is_exact and is_full_string_match)
                ;

//                 const auto item_start_pos = item_starts[item];
//                 const auto item_length = item_starts[item + 1] - item_start_pos;
//                 auto full_text = std::string_view(reinterpret_cast<const char*>(text.data()), text.size());
//                 auto item_text = full_text.substr(item_start_pos, item_length);
// 
//                 const auto match_start_pos = match_pos - item_start_pos;
//                 const auto match_end_pos = match_start_pos + length;
// 
//                 nhlog::ui()->debug(
//                     "index:     {} p:{} i:{}[{}] w:{} ~{}"
//                     " [..[{}..{}]..{}]"
//                     " '{}'",
//                     prefix_id, match_pos, item, item_starts[item], weight, edit_distance,
//                     match_start_pos, match_end_pos, item_length,
//                     item_text
//                 );
//                 nhlog::ui()->debug(
//                     "index:         [{}[{}]{}]",
//                     item_text.substr(0, match_start_pos), item_text.substr(match_start_pos, length), item_text.substr(match_end_pos)
//                 );

                if (weights[item] == 0) {
                    // found this item first time, add to item list
                    items.push_back(item);
                }
                weights[item] = std::max(weights[item], weight);
            }
        }

        const auto t2     = std::chrono::steady_clock::now();

        auto item_weight = [&](int i){return weights[i];};

        // get best max_items results
        if (items.size() > max_items) {
            std::ranges::nth_element(items, items.begin() + max_items, std::greater{}, item_weight);
            items.resize(max_items);
        }

        const auto t3     = std::chrono::steady_clock::now();

        // if we found less than max_items, top will contain some garbage, remove it
        std::erase_if(items, [&](int i){return weights[i] == 0;});

        const auto t4     = std::chrono::steady_clock::now();

        // sort final results descending by weight, then ascending by prefix_id
        auto sort_key = [&, this](int i){return std::pair(256 - weights[i], invSA[item_starts[i]]);};
        std::ranges::sort(items, std::less{}, sort_key);

        const auto t5     = std::chrono::steady_clock::now();

//         nhlog::ui()->debug("index: RESULTS:");
//         for (auto item: items) {
//             const auto item_text_pos = item_starts[item];
//             auto first = std::string_view(reinterpret_cast<const char*>(text.data() + item_text_pos));
//             auto second = std::string_view(first.end() + 1);
//             nhlog::ui()->debug("index:     {} w:{} '{}' '{}'", item, weights[item], first, second);
//         }

        using fmilli = std::chrono::duration<double, std::milli>;
        nhlog::ui()->debug("index:     search: {} ms", fmilli(t1 - t0).count());
        nhlog::ui()->debug("index:     rank&dedup: {} ms", fmilli(t2 - t1).count());
        nhlog::ui()->debug("index:     nth_element: {} ms", fmilli(t3 - t2).count());
        nhlog::ui()->debug("index:     prune w=0: {} ms", fmilli(t4 - t3).count());
        nhlog::ui()->debug("index:     sort: {} ms", fmilli(t5 - t4).count());
        nhlog::ui()->debug("index:     totals: {} ms", fmilli(t5 - t0).count());

        return items;
    }

    // http://www.cs.yale.edu/homes/aspnes/classes/223/notes.html#MSB_radix_sort
    void sort_prefixes(std::span<int> prefixes, int k)
    {
        auto txt = std::u8string_view(text);

        while (prefixes.size() > 1) {
//             if (size <= 1024) { // 156 ms
//             if (size <= 512) { // 148 ms
//             if (size <= 256) { // 141 ms
//             if (size <= 128) { // 135 ms
            if (prefixes.size() <= 64) { // 132 ms
//             if (size <= 32) { // 142 ms
                std::ranges::sort(prefixes, [txt, k](int l, int r){return txt.substr(l + k) < txt.substr(r + k);});
                return;
            }

            uint32_t count[256] = {};
            std::ranges::for_each(prefixes, [&](int x){count[txt[x + k]] += 1;});
            const char8_t most_common_char = std::max_element(count + 1, std::end(count)) - count;

            if (count[most_common_char] == 0) {
                // no characters besides '\0' at position k
                return;
            }

            if (count[most_common_char] < prefixes.size()) {
                uint32_t bucket[256];
                uint32_t top[256];

                bucket[0] = top[0] = 0;
                for(uint32_t i = 1; i < 256; ++i) {
                    top[i] = bucket[i] = bucket[i - 1] + count[i - 1];
                }

                for (uint32_t i = 0; i < 256; ++i) {
                    while (top[i] < bucket[i] + count[i]) {
                        auto ch = txt[prefixes[top[i]] + k];
                        if (ch == i) {
                            // element already in its bucket, just advance top
                            ++top[i];
                        } else {
                            // swap with top char of bucket for ch
                            std::swap(prefixes[top[i]], prefixes[top[ch]]);
                            ++top[ch];
                        }
                    }
                }

                // recursion into all buckets, except most_common_char
                // this makes non-tail-recursive calls at most half N size and
                // reduces stack depth to O(log n)
                for(uint32_t i = 1; i < 256; ++i) {
                    if (i != most_common_char and count[i] != 0) {
                        sort_prefixes(prefixes.subspan(bucket[i], count[i]), k + 1);
                    }
                }

                // hobo-tail-recursion for most_common_char bucket
                prefixes = prefixes.subspan(bucket[most_common_char], count[most_common_char]);
                k = k + 1;
            } else { // count[most_common_char] == size
                // whole subarray has most_common_char at position k, tail-recurse whole subarray
                k = k + 1;
            }
        }
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

    nhlog::ui()->debug("CompletionProxyModel: =================================================================");

    std::u8string full_text;
    std::vector<int> item_starts;
    {
        const auto start_at = std::chrono::steady_clock::now();

        const auto row_count = sourceModel()->rowCount();

        item_starts.reserve(row_count);

        for (int i = 0; i < row_count; i++) {
            auto string1 = sourceModel()
                            ->data(sourceModel()->index(i, 0), CompletionModel::SearchRole)
                            .toString()
                            .toLower()
                            .toUtf8();

            auto string2 = sourceModel()
                            ->data(sourceModel()->index(i, 0), CompletionModel::SearchRole2)
                            .toString()
                            .toLower()
                            .toUtf8();

            // FIXME ACHTUNG UB replace by memcpy
            item_starts.push_back(full_text.size());
            full_text.append(reinterpret_cast<const char8_t*>(string1.constData()), string1.size());
            full_text.push_back('\0');
            full_text.append(reinterpret_cast<const char8_t*>(string2.constData()), string2.size());
            full_text.push_back('\0');
        }

        const auto concat_at     = std::chrono::steady_clock::now();

        index_.reset(new Index(std::move(full_text), std::move(item_starts)));

        const auto build_at     = std::chrono::steady_clock::now();

        using fmilli = std::chrono::duration<double, std::milli>;
        nhlog::ui()->debug("CompletionProxyModel: concat full text: {} ms", fmilli(concat_at - start_at).count());
        nhlog::ui()->debug("CompletionProxyModel: build SA: {} ms", fmilli(build_at - concat_at).count());
        nhlog::ui()->debug("CompletionProxyModel: total: {} ms", fmilli(build_at - start_at).count());
        nhlog::ui()->debug("CompletionProxyModel: item count: {}", index_->item_starts.size() - 1);
        nhlog::ui()->debug("CompletionProxyModel: full_text size: {}", index_->text.size());
    }

    // initialize default mapping
    mapping.resize(std::min(max_completions_, static_cast<size_t>(model->rowCount())));
    std::iota(mapping.begin(), mapping.end(), 0);

    connect(
      this,
      &CompletionProxyModel::newSearchString,
      this,
      [this](QString s) {
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
    if (not searchString_.isEmpty()) {
        // return default model data, if no search string
        auto key = searchString_.toUtf8();

        const auto start_at = std::chrono::steady_clock::now();
        mapping = index_->top_items(std::u8string_view(reinterpret_cast<const char8_t*>(key.data()), key.size()), std::clamp(searchString_.length() / 3, 0, maxMistakes_), max_completions_);
        const auto end_at     = std::chrono::steady_clock::now();
        const auto search_time = std::chrono::duration<double, std::milli>(end_at - start_at);
//         nhlog::ui()->debug("CompletionProxyModel: search '{}': {} ms, {} results", key, search_time.count(), mapping.size());
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
