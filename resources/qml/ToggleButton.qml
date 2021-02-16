import QtQuick 2.5
import QtQuick 2.12
import QtQuick.Controls 2.12
import im.nheko 1.0

Switch {
    id: toggleButton

	indicator: Item {
        implicitWidth: 48
        implicitHeight: 24
        y: parent.height / 2 - height / 2

        Rectangle {
            height: 3 * parent.height/4
            radius: height/2
            width: parent.width - height
            x: radius
            y: parent.height / 2 - height / 2
            color: toggleButton.checked ? "skyblue" : "grey"
            border.color: "#cccccc"
        }
        
        Rectangle {
            x: toggleButton.checked ? parent.width - width : 0
            y: parent.height / 2 - height / 2
            width: parent.height
            height: width
            radius: width/2
            color: toggleButton.down ? "whitesmoke" : "whitesmoke"
            border.color: "#ebebeb"
        }
    }
}