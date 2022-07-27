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
    std::vector<int> id;

    struct prefix_range: std::span<const int>
    {
        int m = 0;
    };

    Index(std::u8string &&text_, const std::vector<uint32_t> &item_borders)
        : text(std::move(text_))
    {
        assert(std::ranges::is_sorted(item_borders));
        assert((item_borders.empty() and text.empty()) or (item_borders.back() == text.size()));

        SA.resize(text.size());
        invSA.resize(text.size());

        std::iota(SA.begin(), SA.end(), uint32_t{0});
        sort_prefixes(SA, 0);

        for (int i = 0; i < SA.size(); ++i) {
            invSA[SA[i]] = i;
        }

        id.resize(SA.size());
        for (int i = 0; i < SA.size(); ++i) {
            id[i] = std::ranges::lower_bound(item_borders, SA[i]) - item_borders.begin();
        }
    }

    prefix_range empty_prefix() const noexcept
    {
        return {SA, 0};
    }

    prefix_range extend_prefix(prefix_range r, char8_t c) const noexcept
    {
        auto next_char = [text = this->text.data(), k = r.m](int x){return text[x + k];};
        auto lo = std::ranges::lower_bound(r, c, std::less{}, next_char);
        auto hi = std::ranges::upper_bound(r, c, std::less{}, next_char);
        return {{lo, hi}, r.m + 1};
    };

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
                std::ranges::sort(prefixes, [txt](int l, int r){return txt.substr(l) < txt.substr(r);});
                return;
            }

            uint32_t count[256];
            std::ranges::fill(count, 0);
            std::ranges::for_each(prefixes, [txt, k, &count](int x){count[txt[x + k]] += 1;});
            unsigned char most_common_char = std::ranges::max(count);

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
    std::vector<uint32_t> items;
    {
        const auto start_at = std::chrono::steady_clock::now();

        const auto row_count = sourceModel()->rowCount();

        items.reserve(row_count);

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
            full_text.append(reinterpret_cast<const char8_t*>(string1.constData()), string1.size());
            full_text.push_back('\0');
            full_text.append(reinterpret_cast<const char8_t*>(string2.constData()), string2.size());
            full_text.push_back('\0');
            items.push_back(full_text.size());
        }

        const auto concat_at     = std::chrono::steady_clock::now();

        index_.reset(new Index(std::move(full_text), items));

        const auto build_at     = std::chrono::steady_clock::now();

        using fmilli = std::chrono::duration<double, std::milli>;
        nhlog::ui()->debug("CompletionProxyModel: concat full text: {} ms", fmilli(concat_at - start_at).count());
        nhlog::ui()->debug("CompletionProxyModel: build SA: {} ms", fmilli(build_at - concat_at).count());
        nhlog::ui()->debug("CompletionProxyModel: total SA: {} ms", fmilli(build_at - start_at).count());
        nhlog::ui()->debug("CompletionProxyModel: full_text size: {}", index_->text.size());

//         auto forward = [&SA, text](int lo, int hi, int shift, unsigned char c)
//         {
//             nhlog::ui()->debug("CompletionProxyModel: forward({}, {}, '{}')", lo, hi, char(c));
//             lo = std::distance(SA.data(), std::partition_point(SA.data() + lo, SA.data() + hi, [c, text, shift](int x){return text[x + shift] < c;}));
//             hi = std::distance(SA.data(), std::partition_point(SA.data() + lo, SA.data() + hi, [c, text, shift](int x){return text[x + shift] <= c;}));
//             nhlog::ui()->debug("CompletionProxyModel: forward: -> {}, {}", lo, hi);
//             return std::pair{lo, hi};
//         };

        {
            nhlog::ui()->debug("CompletionProxyModel: WAT BEGIN");
            std::vector<bool> docs;
            docs.resize(items.size());

            const auto start_at     = std::chrono::steady_clock::now();
            auto p = index_->empty_prefix();
            p = index_->extend_prefix(p, 'g');
            p = index_->extend_prefix(p, 'r');
            p = index_->extend_prefix(p, 'i');
            p = index_->extend_prefix(p, 'n');

            for (auto i: p) {
                docs[index_->id[i]] = true;
                nhlog::ui()->debug("CompletionProxyModel: WAT '{}'", std::string_view(reinterpret_cast<const char*>(index_->text.data() + i)));
            }
            const auto end_at     = std::chrono::steady_clock::now();
            nhlog::ui()->debug("CompletionProxyModel: WAT END {} ms, {} docs", fmilli(end_at - start_at).count(), std::ranges::count(docs, true));
        }
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
    auto key = searchString_.toUcs4();
    beginResetModel();
    if (!key.empty()) {
        // return default model data, if no search string
        const auto start_at = std::chrono::steady_clock::now();
//         mapping = index_.search(key, max_completions_, maxMistakes_);
        const auto end_at     = std::chrono::steady_clock::now();
        const auto search_time = std::chrono::duration<double, std::milli>(end_at - start_at);
        nhlog::ui()->debug("CompletionProxyModel: search '{}': {} ms", searchString_.toUtf8(), search_time.count());
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
        if (sourceIndex.row() >= 0 and mapping[i] == static_cast<uint>(sourceIndex.row())) {
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
