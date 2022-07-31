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

#include <optional>
#include <queue>
#include <span>
#include <fmt/ranges.h>
#include <ranges>
#include <set>

namespace {

int utf8_sequence_length(char8_t lead)
{
    if (lead < 0x80)
        return 1;
    else if ((lead >> 5) == 0x6)
        return 2;
    else if ((lead >> 4) == 0xe)
        return 3;
    else if ((lead >> 3) == 0x1e)
        return 4;
    else
        return 0;
}

bool utf8_is_trail_byte(char8_t b)
{
    return (b >> 6) == 0b10;
}

std::pair<char32_t, int> utf8_decode(const char8_t* p)
{
    char32_t cp = *p;
    assert(not utf8_is_trail_byte(*p));
    const auto length = utf8_sequence_length(*p);
    switch (length) {
        case 1:
            break;
        case 2:
            cp = char32_t(cp & 0b0001'1111) << 6;
            cp |= char32_t(p[1] & 0b0011'1111);
            break;
        case 3:
            cp = char32_t(cp & 0b0000'1111) << 12;
            cp |= char32_t(p[1] & 0b0011'1111) << 6;
            cp |= char32_t(p[2] & 0b0011'1111);
            break;
        case 4:
            cp = char32_t(cp & 0b0000'0111) << 18;
            cp |= char32_t(p[1] & 0b0011'1111) << 12;
            cp |= char32_t(p[2] & 0b0011'1111) << 6;
            cp |= char32_t(p[3] & 0b0011'1111);
            break;
    }

    return {cp, length};
}

} // namespace

struct CompletionProxyModel::Index
{
    std::u8string text;
    std::vector<int> SA;
    std::vector<int> invSA;
    std::vector<int> item_starts;

    struct index_range
    {
        std::size_t lo = 0;
        std::size_t hi = 0;

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

    struct prefix_range: index_range
    {
        int m = 0;

        std::u8string prefix;

        friend auto to_string(prefix_range p)
        {
            return fmt::format("{}:[{}..{})", p.m, p.lo, p.hi);
        };
    };

    Index(std::u8string &&text_, std::vector<int> &&item_starts_)
        : text(std::move(text_))
        , item_starts(std::move(item_starts_))
    {
        item_starts.push_back(text.size());

        SA.reserve(text.size());
        for (std::size_t i = 0; i < text.size(); ++i) {
            if (text[i] != u8'\0' and not utf8_is_trail_byte(text[i])) {
                SA.push_back(i);
            }
        }

        sort_suffixes(SA, 0);

        invSA.resize(text.size(), -1);
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
        return {{.lo = 0, .hi = SA.size()}, 0, {}};
    }

    [[nodiscard]] prefix_range extend_prefix(prefix_range p, char8_t c) const noexcept
    {
        auto next_char = [this, k = p.m](std::size_t i){return text[SA[i] + k];};
        p.lo = *std::ranges::lower_bound(p, c, std::less{}, next_char);
        p.hi = *std::ranges::upper_bound(p, c, std::less{}, next_char);
        p.m += 1;
        p.prefix.push_back(c);
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
        p1.prefix += p2.prefix;
        return p1;
    };

//     [[nodiscard]] std::pair<prefix_range, char8_t> first_subrange(prefix_range p) const noexcept
//     {
//         auto next_char = [this, k = p.m](std::size_t i){return text[SA[i] + k];};
//         const auto c = next_char(p.lo);
//         p.hi = *std::ranges::upper_bound(p, c, std::less{}, next_char);
//         p.m += 1;
//         p.prefix.push_back(c);
//         return {p, c};
//     }
// 
//     [[nodiscard]] std::pair<prefix_range, char8_t> next_subrange(prefix_range p, prefix_range s) const noexcept
//     {
//         p.lo = s.hi;
//         return first_subrange(p);
//     }

    [[nodiscard]] std::pair<prefix_range, char32_t> first_subrange_utf8(prefix_range p) const noexcept
    {
        auto next_byte = [this, k = p.m] (int k_) {
            return [this, k = k + k_](std::size_t i){return text[SA[i] + k];};
        };

        p.lo = *std::ranges::upper_bound(p, u8'\0', std::less{}, next_byte(0));

        if (p.empty()) {
            return {p, -1};
        }

        std::size_t text_pos = SA[p.lo] + p.m;

        auto [c, l] = utf8_decode(&text[text_pos]);
        for (auto i = 0; i < l; ++i) {
            const auto b = text[text_pos + i];
            p.hi = *std::ranges::upper_bound(p, b, std::less{}, next_byte(i));
            p.prefix.push_back(b);
        }
        p.m += l;
        return {p, c};
    }

    [[nodiscard]] std::pair<prefix_range, char32_t> next_subrange_utf8(prefix_range p, prefix_range s) const noexcept
    {
        p.lo = s.hi;
        return first_subrange_utf8(p);
    }

    struct result_item
    {
        prefix_range range;
        std::size_t distance = 0;
    };

    std::vector<result_item> search(std::u8string_view pattern, std::size_t max_edits)
    {
        // Approximate String Matching Using Compressed Suffix Arrays
        // DOI: 10.1007/978-3-540-27801-6_33

        nhlog::ui()->flush_on(spdlog::level::trace);
//         fmt::print(stderr, "index: search('{}', {})\n", std::string_view(reinterpret_cast<const char*>(pattern.data()), pattern.size()), max_distance);

        auto F = std::vector<prefix_range>(pattern.size());
        for (std::size_t i = 0; i < pattern.size(); ++i) {
            F[i] = range_of(pattern.substr(i));
//             fmt::print(stderr, "index: F[{}]: {}\n", i, to_string(F[i]));
        }

        auto results = std::vector<result_item>{};

        enum class edit {nop, ins, del, rep, swap};

        int ilevel = 0;
        auto kapproximate = [&](auto kapproximate, prefix_range p, std::size_t i, std::size_t edits, edit last_op)
        {
            ilevel += 1;
            const auto indent = std::string(ilevel, '=');
            fmt::print(stderr, "index: {}kapproximate({}, {}, {})\n", indent, to_string(p), i, edits);

            if (auto r = concat_prefix(p, F[i]); not r.empty()) {
                fmt::print(stderr, "index:     report: {} . {} => {}\n", to_string(p), to_string(F[i]), to_string(r));
                // TODO figure out result deduplication part from paper
                results.push_back({r, edits});
            }

            if (p.empty() or edits == max_edits) {
                ilevel -= 1;
                return;
            }

            // TODO adjacent character swaps
            for (auto j = i; j < pattern.size() and not p.empty();) {
                fmt::print(stderr, "index: {}    j:{} p:{}\n", indent, j, to_string(p));
                const auto [p_char, l] = utf8_decode(&pattern[j]);
                const auto j_next = j + l;

                // deletion at j
                // dont do del-ins, or ins-del since that pair is same as replace, but in 2 edits
                if (last_op != edit::ins) {
                    kapproximate(kapproximate, p, j_next, edits + 1, edit::del);
                }

                assert(not p.empty());
                for (auto [s, c] = first_subrange_utf8(p); s.lo != p.hi; std::tie(s, c) = next_subrange_utf8(p, s)) {
                    fmt::print(stderr, "index: {}  subrange {} {} of {}\n", indent, to_string(s), uint32_t(c), to_string(p));

                    // skip null byte, thats for delimiting only
                    // also skip code point matching pattern since using that is not an edit
                    if (c == U'\0' or c == p_char) {
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
                p = extend_prefix(p, pattern.substr(j, l));
            }

            // try also inserions after patterns end
            if (last_op != edit::del) {
                for (auto [s, c] = first_subrange_utf8(p); s.lo != p.hi; std::tie(s, c) = next_subrange_utf8(p, s)) {
                    fmt::print(stderr, "index: {}  subrange {} {} of {}\n", indent, to_string(s), uint32_t(c), to_string(p));

                    // skip null byte, thats for delimiting only
                    if (c == U'\0') {
                        continue;
                    }

                    // insertion at j
                    kapproximate(kapproximate, s, pattern.size(), edits + 1, edit::ins);
                }
            }

            ilevel -= 1;
        };

        if (pattern.empty()) {
            results.push_back({empty_prefix(), 0});
        } else {
            kapproximate(kapproximate, empty_prefix(), 0, 0, edit::nop);
        }

        return results;
    }

    std::vector<int> top_items(std::u8string_view pattern, std::size_t max_distance, std::size_t max_items)
    {
        fmt::print(stderr, "index: top_items(pattern='{}', max_distance={}, max_items={})\n", std::string_view(reinterpret_cast<const char*>(pattern.data()), pattern.size()), max_distance, max_items);
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

        fmt::print(stderr, "index: CANDIDATES ranges:{}:\n", found_ranges.size());
        for (auto r: found_ranges) {
            fmt::print(stderr, "index:   RANGE {} ~{}\n", to_string(r.range), r.distance);
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
//                 fmt::print(stderr, 
//                     "index:     {} p:{} i:{}[{}] w:{} ~{}"
//                     " [..[{}..{}]..{}]"
//                     " '{}'"
//                     "\n",
//                     prefix_id, match_pos, item, item_starts[item], weight, edit_distance,
//                     match_start_pos, match_end_pos, item_length,
//                     item_text
//                 );
//                 fmt::print(stderr, 
//                     "index:         [{}[{}]{}]\n",
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

        // sort final results descending by weight, then ascending by prefix_id
        // TODO add static item weights to mix in ranking function
        auto sort_key = [&, this](int i){return std::pair(256 - weights[i], invSA[item_starts[i]]);};
        std::ranges::sort(items, std::less{}, sort_key);

        const auto t4     = std::chrono::steady_clock::now();

        fmt::print(stderr, "index: RESULTS {}:\n", items.size());
//         for (auto item: items) {
//             const auto item_text_pos = item_starts[item];
//             auto first = std::string_view(reinterpret_cast<const char*>(text.data() + item_text_pos));
//             auto second = std::string_view(first.end() + 1);
//             fmt::print(stderr, "index:     {} w:{} '{}' '{}'\n", item, weights[item], first, second);
//         }

        using fmilli = std::chrono::duration<double, std::milli>;
        fmt::print(stderr, "index:     search: {} ms\n", fmilli(t1 - t0).count());
        fmt::print(stderr, "index:     rank&dedup: {} ms\n", fmilli(t2 - t1).count());
        fmt::print(stderr, "index:     nth_element: {} ms\n", fmilli(t3 - t2).count());
        fmt::print(stderr, "index:     sort: {} ms\n", fmilli(t4 - t3).count());
        fmt::print(stderr, "index:     totals: {} ms\n", fmilli(t4 - t0).count());

        return items;
    }

    // http://www.cs.yale.edu/homes/aspnes/classes/223/notes.html#MSB_radix_sort
    void sort_suffixes(std::span<int> suffixes, int k)
    {
        auto txt = std::u8string_view(text);

        while (suffixes.size() > 1) {
//             if (size <= 1024) { // 156 ms
//             if (size <= 512) { // 148 ms
//             if (size <= 256) { // 141 ms
//             if (size <= 128) { // 135 ms
            if (suffixes.size() <= 64) { // 132 ms
//             if (size <= 32) { // 142 ms
                std::ranges::sort(suffixes, [txt, k](int l, int r){return txt.substr(l + k) < txt.substr(r + k);});
                return;
            }

            uint32_t count[256] = {};
            std::ranges::for_each(suffixes, [&](int x){count[txt[x + k]] += 1;});
            const char8_t most_common_char = std::max_element(count + 1, std::end(count)) - count;

            if (count[most_common_char] == 0) {
                // no characters besides '\0' at position k
                return;
            }

            if (count[most_common_char] < suffixes.size()) {
                uint32_t bucket[256];
                uint32_t top[256];

                bucket[0] = top[0] = 0;
                for(uint32_t i = 1; i < 256; ++i) {
                    top[i] = bucket[i] = bucket[i - 1] + count[i - 1];
                }

                for (uint32_t i = 0; i < 256; ++i) {
                    while (top[i] < bucket[i] + count[i]) {
                        auto ch = txt[suffixes[top[i]] + k];
                        if (ch == i) {
                            // element already in its bucket, just advance top
                            ++top[i];
                        } else {
                            // swap with top char of bucket for ch
                            std::swap(suffixes[top[i]], suffixes[top[ch]]);
                            ++top[ch];
                        }
                    }
                }

                // recursion into all buckets, except most_common_char
                // this makes non-tail-recursive calls at most half N size and
                // reduces stack depth to O(log n)
                for(uint32_t i = 1; i < 256; ++i) {
                    if (i != most_common_char and count[i] != 0) {
                        sort_suffixes(suffixes.subspan(bucket[i], count[i]), k + 1);
                    }
                }

                // hobo-tail-recursion for most_common_char bucket
                suffixes = suffixes.subspan(bucket[most_common_char], count[most_common_char]);
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

    fmt::print(stderr, "CompletionProxyModel: =================================================================\n");

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
        fmt::print(stderr, "CompletionProxyModel: concat full text: {} ms\n", fmilli(concat_at - start_at).count());
        fmt::print(stderr, "CompletionProxyModel: build SA: {} ms\n", fmilli(build_at - concat_at).count());
        fmt::print(stderr, "CompletionProxyModel: total: {} ms\n", fmilli(build_at - start_at).count());
        fmt::print(stderr, "CompletionProxyModel: item count: {}\n", index_->item_starts.size() - 1);
        fmt::print(stderr, "CompletionProxyModel: full_text size: {}\n", index_->text.size());
    }

    {
        QString text;
        const auto start_at = std::chrono::steady_clock::now();

        const auto row_count = sourceModel()->rowCount();

        for (int i = 0; i < row_count; i++) {
            auto string1 = sourceModel()
                            ->data(sourceModel()->index(i, 0), CompletionModel::SearchRole)
                            .toString()
                            .toLower();

            auto string2 = sourceModel()
                            ->data(sourceModel()->index(i, 0), CompletionModel::SearchRole2)
                            .toString()
                            .toLower();

            text.append(string1);
            text.push_back('\0');
            text.append(string2);
            text.push_back('\0');
        }

        const auto concat_at     = std::chrono::steady_clock::now();

        /* Makes suffix array p of x. x becomes inverse of p. p and x are both of size
        n+1. Contents of x[0...n-1] are integers in the range l...k-1. Original
        contents of x[n] is disregarded, the n-th symbol being regarded as
        end-of-string smaller than all other symbols.*/
        auto SA = std::vector<int>{};

        SA.resize(text.size());
        auto ec = libsais16(text.utf16(), SA.data(), text.size(), 0, nullptr);

        auto invSA = std::vector<int>{};
        invSA.resize(text.size(), -1);
        for (int i = 0, I = SA.size(); i < I; ++i) {
            invSA[SA[i]] = i;
        }

        const auto build_at     = std::chrono::steady_clock::now();

        using fmilli = std::chrono::duration<double, std::milli>;
        fmt::print(stderr, "CompletionProxyModel: libsais: concat full text: {} ms\n", fmilli(concat_at - start_at).count());
        fmt::print(stderr, "CompletionProxyModel: libsais: build SA (ec:{}): {} ms\n", ec, fmilli(build_at - concat_at).count());
        fmt::print(stderr, "CompletionProxyModel: libsais: total: {} ms\n", fmilli(build_at - start_at).count());
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
    if (not searchString_.isEmpty()) {
        // return default model data, if no search string
        auto key = searchString_.toUtf8();

        const auto start_at = std::chrono::steady_clock::now();
        mapping = index_->top_items(std::u8string_view(reinterpret_cast<const char8_t*>(key.data()), key.size()), std::clamp(searchString_.length() / 3, 0, maxMistakes_), max_completions_);
        const auto end_at     = std::chrono::steady_clock::now();
        const auto search_time = std::chrono::duration<double, std::milli>(end_at - start_at);
//         fmt::print(stderr, "CompletionProxyModel: search '{}': {} ms, {} results\n", key, search_time.count(), mapping.size());
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
