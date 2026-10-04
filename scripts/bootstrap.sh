#!/usr/bin/env bash
# Reproduce the Codex Cloud x86_64 Linux environment without relying on preinstalled Lean.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
case "$(uname -s):$(uname -m)" in
  Linux:x86_64) ;;
  *) echo 'This bootstrap targets x86_64 Linux; see README for other platforms.' >&2; exit 1 ;;
esac
for command in git curl tar zstd sha256sum rg; do
  command -v "$command" >/dev/null || { echo "Missing prerequisite: $command" >&2; exit 1; }
done
export ELAN_HOME="${ELAN_HOME:-/workspace/.local/elan}"
export NEWLANG_TOOLCHAIN_ROOT="${NEWLANG_TOOLCHAIN_ROOT:-/workspace/.local/lean}"
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-/workspace/.cache/mathlib}"
export PATH="$ELAN_HOME/bin:$PATH"
# Resolve the committed manifest without triggering mathlib's full-library cache hook.
export MATHLIB_NO_CACHE_ON_UPDATE=1
toolchain=$(cat lean-toolchain)
if [ "$toolchain" != 'leanprover/lean4:v4.34.1' ]; then
  echo 'Toolchain pin changed: update the bootstrap version and official SHA-256 together.' >&2
  exit 1
fi
scratch_dir=$(mktemp -d)
trap 'rm -rf "$scratch_dir"' EXIT
if ! "$ELAN_HOME/bin/elan" --version 2>/dev/null | rg -q '^elan 4\.2\.4( |$)'; then
  curl --proto '=https' --tlsv1.2 -fsSL \
    https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz \
    -o "$scratch_dir/elan.tar.gz"
  printf '%s  %s\n' '42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63' \
    "$scratch_dir/elan.tar.gz" | sha256sum -c -
  tar -xzf "$scratch_dir/elan.tar.gz" -C "$scratch_dir"
  "$scratch_dir/elan-init" -y --no-modify-path --default-toolchain none
fi
if ! { elan toolchain list 2>/dev/null | rg -q '^leanprover/lean4:v4\.34\.1( |$)' && \
    elan run "$toolchain" lean --version 2>/dev/null | \
    rg -q '^Lean \(version 4\.34\.1, .*commit 5045d0056413266e57c625dcd7c365b10e377c52, Release\)$'; }; then
  # Official fixed-version GitHub artifact, linked through elan under the repository pin.
  # This also works when elan's release-discovery endpoint is unavailable.
  lean_dir="$NEWLANG_TOOLCHAIN_ROOT/v4.34.1"
  if [ -e "$lean_dir" ]; then
    echo "Unrecognized existing toolchain at $lean_dir; preserve it and choose another NEWLANG_TOOLCHAIN_ROOT." >&2
    exit 1
  fi
  curl --proto '=https' --tlsv1.2 -fsSL \
    https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst \
    -o "$scratch_dir/lean.tar.zst"
  printf '%s  %s\n' '47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4' \
    "$scratch_dir/lean.tar.zst" | sha256sum -c -
  mkdir -p "$lean_dir"
  tar --zstd -xf "$scratch_dir/lean.tar.zst" --strip-components=1 -C "$lean_dir"
  elan toolchain link "$toolchain" "$lean_dir"
fi
lean --version
elan show
# lake-manifest.json pins mathlib and every transitive dependency. Do not run lake update.
manifest_before=$(sha256sum lake-manifest.json)
lake exe cache get Mathlib.Data.Finset.Basic Mathlib.Data.Set.Basic
scripts/check-proofs.sh
if [ "$(sha256sum lake-manifest.json)" != "$manifest_before" ]; then
  echo 'Unexpected dependency manifest change during setup.' >&2
  exit 1
fi
