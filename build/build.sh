#!/bin/bash

 cd ..
 ./configure \
     --prefix=/usr \
     --enable-gpl \
     --enable-nonfree \
     --extra-cflags=-g \
     --enable-debug=3 \
     --enable-sdl2 \
     --enable-vaapi \
     --enable-shared \
     --enable-libx264 \
     --enable-libx265 \
     --enable-libpulse \
     --enable-libmp3lame \
     --disable-static \
     --disable-x86asm \
     --disable-asm \
     --disable-stripping \
     --disable-optimizations

 make
