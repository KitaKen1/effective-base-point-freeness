#!/usr/bin/env bash
set -euo pipefail

# All cleanup and swap changes are confined to the disposable Actions runner.
if [ "${GITHUB_ACTIONS:-}" != true ]; then
  echo 'This setup script must run on GitHub Actions.' >&2
  exit 1
fi
sudo rm -rf /usr/share/dotnet /usr/local/lib/android /opt/ghc \
  /usr/local/.ghcup /usr/local/share/boost /opt/hostedtoolcache/CodeQL
sudo apt-get update -qq
sudo apt-get install -y bubblewrap zstd
if [ -e /proc/sys/kernel/apparmor_restrict_unprivileged_userns ]; then
  sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0
fi
bwrap --ro-bind / / --unshare-user --uid 0 --gid 0 true
case "${F2_CI_SWAP_GB:-0}" in
  0|12) ;;
  *) echo 'F2_CI_SWAP_GB must be 0 or 12.' >&2; exit 1 ;;
esac
# Reserve extra swap only for kernel replay, whose runner has no Mathlib build.
# The build/export jobs need that disk space for compiled modules and exports.
if [ "${F2_CI_SWAP_GB:-0}" = 12 ] && \
    ! swapon --show=NAME --noheadings | grep -Fxq /mnt/f2-ci.swap; then
  sudo fallocate -l 12G /mnt/f2-ci.swap
  sudo chmod 600 /mnt/f2-ci.swap
  sudo mkswap /mnt/f2-ci.swap
  sudo swapon /mnt/f2-ci.swap
fi
free -h
df -h

curl --fail --location --retry 3 \
  https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz \
  -o "$RUNNER_TEMP/elan.tar.gz"
echo '42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63  '"$RUNNER_TEMP/elan.tar.gz" | sha256sum --check
tar -xzf "$RUNNER_TEMP/elan.tar.gz" -C "$RUNNER_TEMP"
"$RUNNER_TEMP/elan-init" -y --default-toolchain none
echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
"$HOME/.elan/bin/elan" toolchain install "$(cat lean/lean-toolchain)"
