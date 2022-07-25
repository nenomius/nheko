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

namespace {

enum class ElementRank
{
    first,
    second
};

template<typename T, std::size_t BlockSize, typename Index>
class monotonic_pool
{
public:
    using value_type = T;
    using index_type = Index;
    static constexpr std::size_t block_size = BlockSize;
    static constexpr index_type max_size = std::numeric_limits<index_type>::max();

    Index size() const {return size_;}

    value_type &operator[](index_type i)
    {
        assert(i < size_);
        const auto block_index = i / block_size;
        const auto element_index = i % block_size;
        return blocks_[block_index][element_index];
    }

    const value_type &operator[](index_type i) const
    {
        assert(i < size_);
        const auto block_index = i / block_size;
        const auto element_index = i % block_size;
        return blocks_[block_index][element_index];
    }

    Index push(T value)
    {
        assert(size_ != max_size);

        const auto index = size_;
        const auto block_index = index / block_size;
        const auto element_index = index % block_size;

        assert(block_index <= blocks_.size());

        if (block_index == blocks_.size()) {
            blocks_.push_back(std::make_unique<value_type[]>(block_size));
        }

        blocks_[block_index][element_index] = std::move(value);

        size_ += 1;
        return index;
    }

private:
    Index size_ = 0;
    std::vector<std::unique_ptr<value_type[]>> blocks_;
};

} // namespace

class CompletionProxyModel::trie
{
public:
    using Key = QChar;
    using Value = uint;
    using pool_index = uint32_t;

    static constexpr auto invalid_key = QChar();
    static constexpr auto invalid_index = std::numeric_limits<pool_index>::max();

    struct transition
    {
        Key key = invalid_key;
        pool_index node = invalid_index;

        friend bool operator<(transition l, transition r) {return l.key < r.key;}
        friend bool operator<(transition l, Key r) {return l.key < r;}
        friend bool operator<(Key l, transition r) {return l < r.key;}
    };

    struct node
    {
        pool_index values = invalid_index;

        // no transitions: {invalid_key, invalid_index}
        // single transition: {key, node_pool_index}
        // multiple transitions: {invalid_key, transidions_pool_index}
        transition transitions;
    };

    trie()
    {
        nodes.push({}); // root node
    }

    std::span<const transition> transitions_of(pool_index node) const
    {
        const auto& ts = nodes[node].transitions;

        if (ts.key == invalid_key) {
            if (ts.node == invalid_index) { // empty
                return {};
            } else { // multiple
                return transitions[ts.node];
            }
        } else { // single
            return {&ts, 1};
        }
    }

    std::span<const Value> values_of(pool_index node) const
    {
        auto &vs_index = nodes[node].values;
        if (vs_index == invalid_index) {
            return {};
        } else {
            return values[vs_index];
        }
    }

    pool_index add_transition(pool_index node, Key k)
    {
        auto& ts = nodes[node].transitions;

        if (ts.key == invalid_key) {
            if (ts.node == invalid_index) { // empty, make it single transition
                ts = {.key = k, .node = nodes.push({})};
                return ts.node;
            } else { // multiple
                auto &xs = transitions[ts.node];
                auto found = std::ranges::find_if(xs, [k] (transition t) {return t.key >= k;});
                if (found == xs.end() or found->key != k) { // new transition
                    return xs.insert(found, {.key = k, .node = nodes.push({})})->node;
                } else { // already had that transition
                    return found->node;
                }
            }
        } else { // single
            if (ts.key == k) {
                return ts.node;
            } else {
                const auto new_node = nodes.push({});
                auto xs = std::vector<transition>{ts, {.key = k, .node = new_node}};
                if (ts.key > k) {
                    std::swap(xs[0], xs[1]);
                }
                ts = {.key = invalid_key, .node = transitions.push(std::move(xs))};
                return new_node;
            }
        }
    }

    void add_value(pool_index node, Value v, ElementRank r)
    {
        auto &vs_index = nodes[node].values;
        if (vs_index == invalid_index) {
            vs_index = values.push({v});
        } else if (r == ElementRank::first) {
            values[vs_index].insert(values[vs_index].begin(), v);
        } else if (r == ElementRank::second) {
            values[vs_index].push_back(v);
        }
    }

    monotonic_pool<node, 1024, pool_index> nodes;
    monotonic_pool<std::vector<Value>, 32, pool_index> values;
    monotonic_pool<std::vector<transition>, 32, pool_index> transitions;

    void insert(std::span<const Key> keys, const Value &v, ElementRank r)
    {
//         nhlog::ui()->debug("trie: insert('{}', {}, {})", QString::fromUcs4(keys.data(), keys.size()).toUtf8(), v, int(r));

        auto n = pool_index{0};
        for (const auto k : keys) {
            n = add_transition(n, k);
        }

        add_value(n, v, r);
    }

//     template<typename Callback>
//     bool valuesAndSubvalues(const Callback & callback) const
//     {
//         for (const auto &v : values) {
//             if (not callback(v)) {
//                 return false;
//             }
//         }
// 
//         for (const auto &[k, t] : next) {
//             std::ignore = k;
//             if (not t.valuesAndSubvalues(callback)) {
//                 return false;
//             }
//         }
// 
//         return true;
//     }

    template<typename F>
    void traverse(pool_index n, F f) const
    {
        f(n);
        for (auto & [k, n]: transitions_of(n)) {
            std::ignore = k;
            traverse(n, f);
        }
    }

//     struct result_buffer
//     {
//         struct item
//         {
//             uint rank = 0;
//             Value value;
// 
//             friend bool operator< (const item &l, const item &r)
//             {
//                 return l.rank < r.rank;
//             }
//         };
// 
//         explicit result_buffer(std::size_t max_result_count, Value max_value)
//             : max_result_count(max_result_count)
//             , presence(max_value + 1)
//         {}
// 
//         void add(Value v, uint rank)
//         {
//             if (presence[v]) {
//                 auto have = std::find_if();
//             }
//             
//             std::find_if(items.begin(), items.end(), [] (auto item) {
//                 
//             });
//         }
// 
//         std::size_t max_result_count;
//         std::vector<bool> presence;
//         std::vector<item> items;
//     };

//     std::vector<Value> search(const QVector<Key> &keys, //< TODO(Nico): replace this with a span
//                               size_t result_count_limit,
//                               size_t max_edit_distance_ = 2) const
//     {
// //         auto max_value = maxValue();
// //         auto found_mask = std::vector<bool>{};
// //         found_mask.resize(max_value);
//         auto results = std::vector<result_elem>{};
//         search_impl(keys, result_count_limit, max_edit_distance_, results);
// 
//         std::vector<Value> ret;
//         while (not results.empty()) {
//             ret.push_back(results.top().value);
//             results.pop();
//         }
//         return ret;
//     }
// 
//     void search_impl(const QVector<Key> &keys, //< TODO(Nico): replace this with a span
//                      size_t result_count_limit,
//                      size_t max_edit_distance,
//                      std::priority_queue<result_elem> & results) const
//     {
//         // FIXME ranks
//         auto append = [&results, result_count_limit](Value x) {
//             if (results.size() < result_count_limit) {
//                 results.push({1, x});
//             } else if (1 < results.top().rank) {
//                 results.pop();
//                 results.push({1, x});
//             }
//             return true;
//         };
// 
//         if (keys.isEmpty()) {
//             valuesAndSubvalues(append);
//         }
// 
//         // Try first exact matches, ...
//         if (auto e = this->next.find(keys[0]); e != this->next.end()) {
//             e->second.search_impl(keys.mid(1), result_count_limit, max_edit_distance, results);
//         }
// 
//         // ... then with maximum errors
//         if (max_edit_distance > 0) {
//             max_edit_distance -= 1;
// 
//             // swap chars case
//             if (keys.size() >= 2) {
//                 auto t = this;
//                 for (int i = 1; i >= 0; i--) {
//                     if (auto e = t->next.find(keys[i]); e != t->next.end()) {
//                         t = &e->second;
//                     } else {
//                         t = nullptr;
//                         break;
//                     }
//                 }
// 
//                 if (t) {
//                     t->search_impl(keys.mid(2), result_count_limit, max_edit_distance, results);
//                 }
//             }
// 
//             // insert case
//             for (const auto &[k, t] : this->next) {
//                 if (k == keys[0])
//                     continue;
// 
//                 // insert
//                 t.search_impl(keys, result_count_limit, max_edit_distance, results);
//             }
// 
//             // delete character case
//             this->search_impl(keys.mid(1), result_count_limit, max_edit_distance, results);
// 
//             // substitute case
//             for (const auto &[k, t] : this->next) {
//                 if (k == keys[0])
//                     continue;
// 
//                 // substitute
//                 t.search_impl(keys.mid(1), result_count_limit, max_edit_distance, results);
//             }
//         }
//     }
};

CompletionProxyModel::CompletionProxyModel(QAbstractItemModel *model,
                                           int max_mistakes,
                                           size_t max_completions,
                                           QObject *parent)
  : QAbstractProxyModel(parent)
  , trie_(new trie)
  , maxMistakes_(max_mistakes)
  , max_completions_(max_completions)
{
    setSourceModel(model);

    max_completions_ = std::numeric_limits<size_t>::max();

    std::size_t trie_texts = 0;
    std::size_t total_trie_texts_length = 0;
    std::size_t skipped_texts = 0;

    auto insertParts = [&, this](const QString &str, int id) {
        QTextBoundaryFinder finder(QTextBoundaryFinder::BoundaryType::Word, str);
        finder.toStart();
        auto start = finder.position();
        finder.toNextBoundary();

        // if first word ends at the end of string, we already have that inserted
        if (finder.position() == str.size()) {
            skipped_texts += 1;
//             nhlog::ui()->debug("trie: skip '{}'", str.toUtf8());
            return;
        }

        for (; start < str.size(); finder.toNextBoundary()) {
            auto end = finder.position();

            auto ref = str.midRef(start, end - start).trimmed();

            if (!ref.isEmpty()) {
                trie_texts += 1;
                total_trie_texts_length += ref.size();
                trie_->insert(std::span(ref.constData(), ref.size()), id, ElementRank::second);
            }

            start = end;
        }
    };

    {
        const auto start_at = std::chrono::steady_clock::now();

        // insert full texts and partial matches
        for (int i = 0; i < sourceModel()->rowCount(); i++) {
            // full texts are ranked first and partial matches second
            // that way when searching full texts will be first in result list

            auto string1 = sourceModel()
                            ->data(sourceModel()->index(i, 0), CompletionModel::SearchRole)
                            .toString()
                            .toLower();
            if (!string1.isEmpty()) {
                trie_texts += 1;
                total_trie_texts_length += string1.size();
                trie_->insert(std::span(string1.constData(), string1.size()), i, ElementRank::first);
                insertParts(string1, i);
            }

            auto string2 = sourceModel()
                            ->data(sourceModel()->index(i, 0), CompletionModel::SearchRole2)
                            .toString()
                            .toLower();
            if (!string2.isEmpty()) {
                trie_texts += 1;
                total_trie_texts_length += string2.size();
                trie_->insert(std::span(string2.constData(), string2.size()), i, ElementRank::first);
                insertParts(string2, i);
            }
        }

        const auto end_at     = std::chrono::steady_clock::now();
        const auto build_time = std::chrono::duration<double, std::milli>(end_at - start_at);
        nhlog::ui()->debug("CompletionProxyModel: build trie: {} ms", build_time.count());
    }

    nhlog::ui()->debug("CompletionProxyModel: total trie texts length: {}", total_trie_texts_length);
    nhlog::ui()->debug("CompletionProxyModel: trie texts: {}", trie_texts);
    nhlog::ui()->debug("CompletionProxyModel: skipped texts: {}", skipped_texts);

    std::size_t node_count = 0;
    std::size_t total_transitions = 0;
    std::size_t total_values = 0;
    std::map<std::size_t, std::size_t> transition_count;
    std::map<std::size_t, std::size_t> value_count;
    auto collect_stats = [&](auto self, trie::pool_index n, QString word = {}) -> void {
        const auto ts = trie_->transitions_of(n);
        const auto vs = trie_->values_of(n);
        node_count += 1;
        total_transitions += ts.size();
        total_values += vs.size();
        transition_count[ts.size()] += 1;
        value_count[vs.size()] += 1;

        if (vs.size() > 1000) {
            nhlog::ui()->debug("CompletionProxyModel: trie '{}' has {} values", word.toUtf8(), vs.size());
        }

        for (auto [k, c]: ts) {
            self(self, c, word + QChar(k));
        }
    };
    collect_stats(collect_stats, 0);

// build trie: 77.082743 ms
// total trie texts length: 2134385
// trie texts: 313398
// skipped texts: 32679
// trie nodes: 986723
// total transitions: 986722
// transitions count histogram: {0: 88379, 1: 865465, 2: 18441, 3: 5734, 4: 2609, 5: 1573, 6: 1035, 7: 723, 8: 534, 9: 406, 10: 297, 11: 237, 12: 203, 13: 148, 14: 134, 15: 109, 16: 98, 17: 84, 18: 67, 19: 49, 20: 50, 21: 38, 22: 31, 23: 31, 24: 40, 25: 41, 26: 31, 27: 26, 28: 18, 29: 11, 30: 12, 31: 2, 32: 2, 33: 8, 34: 3, 35: 8, 36: 5, 37: 7, 38: 10, 39: 5, 40: 6, 41: 1, 42: 3, 43: 2, 44: 1, 45: 3, 46: 1, 47: 1, 674: 1}
// values count histogram: {0: 890095, 1: 64497, 2: 29427, 3: 1057, 4: 633, 5: 246, 6: 140, 7: 88, 8: 69, 9: 44, 10: 37, 11: 37, 12: 29, 13: 34, 14: 17, 15: 18, 16: 23, 17: 12, 18: 12, 19: 8, 20: 7, 21: 9, 22: 10, 23: 7, 24: 10, 25: 3, 26: 5, 27: 2, 28: 3, 29: 8, 30: 5, 31: 5, 32: 3, 33: 4, 34: 8, 35: 5, 36: 3, 37: 3, 38: 4, 39: 1, 40: 3, 41: 4, 42: 2, 43: 4, 44: 4, 45: 1, 46: 2, 48: 2, 49: 3, 50: 1, 51: 3, 53: 1, 54: 2, 55: 1, 57: 2, 58: 3, 59: 2, 60: 1, 63: 2, 64: 1, 66: 1, 67: 1, 70: 1, 75: 3, 76: 1, 77: 3, 80: 2, 81: 1, 82: 1, 87: 2, 92: 1, 95: 1, 96: 1, 98: 1, 100: 1, 105: 1, 106: 1, 117: 1, 122: 1, 123: 1, 137: 2, 139: 1, 142: 1, 163: 1, 169: 1, 172: 1, 196: 1, 211: 1, 216: 1, 229: 1, 241: 1, 253: 1, 260: 1, 264: 1, 401: 1, 425: 1, 442: 1, 456: 1, 1097: 1, 2477: 1, 32128: 1, 41020: 1, 41022: 1, 47926: 1}
// node pool: 986723
// transitions pool: 32879
// values pool: 96628

    nhlog::ui()->debug("CompletionProxyModel: trie nodes: {}", node_count);
    nhlog::ui()->debug("CompletionProxyModel: total transitions: {}", total_transitions);
    nhlog::ui()->debug("CompletionProxyModel: transitions count histogram: {}", transition_count);
    nhlog::ui()->debug("CompletionProxyModel: values count histogram: {}", value_count);
    nhlog::ui()->debug("CompletionProxyModel: node pool: {}", trie_->nodes.size());
    nhlog::ui()->debug("CompletionProxyModel: transitions pool: {}", trie_->transitions.size());
    nhlog::ui()->debug("CompletionProxyModel: values pool: {}", trie_->values.size());
//     trie_.maxValue();

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
//         mapping = trie_.search(key, max_completions_, maxMistakes_);
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
