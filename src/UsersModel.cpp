// SPDX-FileCopyrightText: 2021 Nheko Contributors
// SPDX-FileCopyrightText: 2022 Nheko Contributors
//
// SPDX-License-Identifier: GPL-3.0-or-later

#include "UsersModel.h"

#include <QUrl>

#include "Cache.h"
#include "CompletionModelRoles.h"
#include "UserSettingsPage.h"

UsersModel::UsersModel(const std::string &roomId, QObject *parent)
  : QAbstractListModel(parent)
  , room_id(QString::fromStdString(roomId))
  , memberInfos_(cache::getMembers(roomId, 0, std::numeric_limits<std::size_t>::max()))
{
}

QHash<int, QByteArray>
UsersModel::roleNames() const
{
    return {
      {CompletionModel::CompletionRole, "completionRole"},
      {CompletionModel::SearchRole, "searchRole"},
      {CompletionModel::SearchRole2, "searchRole2"},
      {Roles::DisplayName, "displayName"},
      {Roles::AvatarUrl, "avatarUrl"},
      {Roles::UserID, "userid"},
    };
}

QVariant
UsersModel::data(const QModelIndex &index, int role) const
{
    if (hasIndex(index.row(), index.column(), index.parent())) {
        switch (role) {
        case CompletionModel::CompletionRole:
            if (UserSettings::instance()->markdown())
                return QStringLiteral("[%1](https://matrix.to/#/%2)")
                  .arg(QString(memberInfos_[index.row()].display_name)
                         .replace("[", "\\[")
                         .replace("]", "\\]")
                         .toHtmlEscaped(),
                       QString(QUrl::toPercentEncoding(memberInfos_[index.row()].user_id)));
            else
                return memberInfos_[index.row()].display_name;
        case CompletionModel::SearchRole:
            return memberInfos_[index.row()].display_name;
        case Qt::DisplayRole:
        case Roles::DisplayName:
            return memberInfos_[index.row()].display_name.toHtmlEscaped();
        case CompletionModel::SearchRole2:
            return memberInfos_[index.row()].user_id;
        case Roles::AvatarUrl:
            return cache::avatarUrl(room_id, memberInfos_[index.row()].user_id);
        case Roles::UserID:
            return memberInfos_[index.row()].user_id.toHtmlEscaped();
        }
    }
    return {};
}
