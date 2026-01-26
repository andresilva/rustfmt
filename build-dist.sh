#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"
mkdir -p dist

if command -v podman &>/dev/null; then
    CONTAINER_CMD=podman
elif command -v docker &>/dev/null; then
    CONTAINER_CMD=docker
else
    echo "Error: neither podman nor docker found" >&2
    exit 1
fi

$CONTAINER_CMD run --rm \
    -v "$(pwd)":/rustfmt \
    -v "$(pwd)/dist":/output \
    rust:latest bash -c '
cd /rustfmt
RUSTFLAGS="-C link-arg=-Wl,-rpath,\$ORIGIN/../lib" cargo build --release
mkdir -p /output/rustfmt/bin /output/rustfmt/lib
cp target/release/rustfmt /output/rustfmt/bin/
cp $(rustc --print sysroot)/lib/*.so* /output/rustfmt/lib/ 2>/dev/null || true
cd /output && tar -czf rustfmt.tar.gz rustfmt/ && rm -rf rustfmt/
'

echo "Built: dist/rustfmt.tar.gz"
