#!/usr/bin/env bash
# Install the user-owned Subtail runtimes on an ARM64 Linux research host.
# Run as the research user after installing curl, tar, xz-utils, zstd, gh and
# tzdata, and configuring the host timezone (/etc/localtime must be readable).
# Does not clone a repository, authenticate, start jobs, or edit shell profiles.
set -euo pipefail

test "$(uname -s)" = Linux
test "$(uname -m)" = aarch64
for required in curl tar sha256sum zstd xz; do
  command -v "$required" >/dev/null
done
if ! test -r /etc/localtime; then
  printf '%s\n' 'Missing /etc/localtime: configure the host timezone before starting Lean.' >&2
  exit 1
fi

subtail_runtime="$HOME/.local/share/subtail"
mkdir -p "$subtail_runtime/tools" "$HOME/.local/bin"
subtail_scratch=$(mktemp -d)
trap 'rm -rf -- "$subtail_scratch"' EXIT

fetch_checked() {
  curl --fail --location --retry 2 --connect-timeout 15 --max-time 300 \
    --silent --show-error "$1" --output "$2"
  printf '%s  %s\n' "$3" "$2" | sha256sum --check --status
}

if ! test -x "$HOME/.elan/bin/elan"; then
  fetch_checked \
    https://github.com/leanprover/elan/releases/download/v4.2.4/elan-aarch64-unknown-linux-gnu.tar.gz \
    "$subtail_scratch/elan.tar.gz" \
    05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9
  mkdir "$subtail_scratch/elan"
  tar -xzf "$subtail_scratch/elan.tar.gz" -C "$subtail_scratch/elan"
  "$subtail_scratch/elan/elan-init" -y --default-toolchain none --no-modify-path
fi
"$HOME/.elan/bin/elan" toolchain install leanprover/lean4:v4.33.1
"$HOME/.elan/bin/elan" default leanprover/lean4:v4.33.1

if ! test -x "$subtail_runtime/tools/uv-0.12.17/uv"; then
  fetch_checked \
    https://github.com/astral-sh/uv/releases/download/0.12.17/uv-aarch64-unknown-linux-gnu.tar.gz \
    "$subtail_scratch/uv.tar.gz" \
    d636d1b678e9e7f367ecb22b46bd1cabbed234d6bc3b4d96365d2b507f72f86c
  mkdir "$subtail_scratch/uv"
  tar -xzf "$subtail_scratch/uv.tar.gz" -C "$subtail_scratch/uv"
  mv "$subtail_scratch/uv/uv-aarch64-unknown-linux-gnu" "$subtail_runtime/tools/uv-0.12.17"
fi
"$subtail_runtime/tools/uv-0.12.17/uv" python install 3.13.14

"$HOME/.elan/bin/elan" --version
"$HOME/.elan/bin/elan" run leanprover/lean4:v4.33.1 lean --version
"$subtail_runtime/tools/uv-0.12.17/uv" --version
"$subtail_runtime/tools/uv-0.12.17/uv" python find 3.13.14
