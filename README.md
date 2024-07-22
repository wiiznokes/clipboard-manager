# Clipboard manager for COSMIC™

![screenshot of the applet](https://media.githubusercontent.com/media/wiiznokes/clipboard-manager/master/res/screenshots/main_popup.png)

The goal is to make a simple yet fast clipboard history, with a focus on UX, rapidity and security.

There is a quick settings popup when you right click the icon.

## Install

### Fedora

You can use this [copr](https://copr.fedorainfracloud.org/coprs/wiiznokes/cosmic-applets-unofficial/).

```sh
sudo dnf copr enable wiiznokes/cosmic-applets-unofficial
sudo dnf install cosmic-ext-applet-clipboard-manager
```

### Other distros

```sh
git clone https://github.com/wiiznokes/clipboard-manager.git
cd clipboard-manager
sudo apt install libsqlite3-dev sqlite3
just build-release
sudo just install
```

You will probably need to reboot or re login for the `COSMIC_DATA_CONTROL_ENABLED=1` environment variable to take effect.

## Logs

```sh
journalctl -p 3 -xb --user _EXE=/usr/bin/cosmic-ext-applet-clipboard-manager | less
```

- `-p` 3 means priority error
- `-x` add information
- `b` means since last boot

## Contributing

Contributions are welcome

To build and install the debug build

```sh
just build-debug && sudo just debug=1 install && pkill cosmic-panel
```

or for release

```sh
just && sudo just install && pkill cosmic-panel
```