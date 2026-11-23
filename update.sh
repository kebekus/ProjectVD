#!/bin/bash

# Delete outdated lean toolchains, leftover partial downloads
elan toolchain gc --delete
rm -rf ~/.elan/tmp

# Clear the cache of precompiled binaries
lake exe cache clean
