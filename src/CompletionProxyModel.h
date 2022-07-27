// SPDX-FileCopyrightText: 2021 Nheko Contributors
// SPDX-FileCopyrightText: 2022 Nheko Contributors
//
// SPDX-License-Identifier: GPL-3.0-or-later

#pragma once

// Class for showing a limited amount of completions at a time

#include <QAbstractProxyModel>

class CompletionProxyModel : public QAbstractProxyModel
{
    Q_OBJECT
    Q_PROPERTY(QString searchString READ searchString WRITE setSearchString NOTIFY newSearchString)
public:
    CompletionProxyModel(QAbstractItemModel *model,
                         int max_mistakes       = 2,
                         size_t max_completions = 30,
                         QObject *parent        = nullptr);
    ~CompletionProxyModel();

    void invalidate();

    QHash<int, QByteArray> roleNames() const override;
    int rowCount(const QModelIndex &parent = QModelIndex()) const override;
    int columnCount(const QModelIndex &) const override;

    QModelIndex mapFromSource(const QModelIndex &sourceIndex) const override;
    QModelIndex mapToSource(const QModelIndex &proxyIndex) const override;

    QModelIndex
    index(int row, int column, const QModelIndex &parent = QModelIndex()) const override;
    QModelIndex parent(const QModelIndex &) const override;

public slots:
    QVariant completionAt(int i) const;

    void setSearchString(QString s);
    QString searchString() const { return searchString_; }

signals:
    void newSearchString(QString);

private:
    struct Index;

    QString searchString_;
    QScopedPointer<Index> index_;
    std::vector<uint> mapping;
    int maxMistakes_;
    size_t max_completions_;
};
