#!/bin/bash

cd ..
./configure \
    --enable-gpl \
    --enable-debug=3 \
    --enable-sdl2 \
    --enable-shared \
    --enable-libx264 \
    --enable-libpulse \
    --disable-static \
    --disable-x86asm

make
