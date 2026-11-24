#!/bin/bash

echo "Delete outdated lean toolchains, leftover partial downloads"
elan toolchain gc --delete
rm -rf ~/.elan/tmp
echo

echo "Clear the cache of precompiled binaries"
lake exe cache clean
echo

echo "Update and rebuild"
lake update
lake build
echo
