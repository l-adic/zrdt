#!/bin/bash
# Option B: rebuild Lean v4.35.0 runtime as PIC with a dlopen-safe TLS model -> libleanrt_pic.a
set -uo pipefail
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0
SRC=/tmp/zrdt-spike-runtime/dl-lean4/lean4/src
DEBS=/tmp/zrdt-spike-runtime/dl-debs/x/usr/include
MI=/tmp/zrdt-spike-runtime/dl-mimalloc/mimalloc
OUT=/tmp/zrdt-verify-cbuild/rtpic; mkdir -p $OUT/uv
TLS=${TLS:-global-dynamic}
CXXFLAGS=(-std=c++20 -O3 -DNDEBUG -fPIC -ftls-model=$TLS -fvisibility=hidden -DLEAN_MULTI_THREAD -DLEAN_USE_GMP
          -DLEAN_EXPORTING '-DLEAN_BUILD_TYPE="Release"' -I"$TC/include" -I"$SRC" -I/tmp/zrdt-verify-cbuild/rtpic/gen -I"$DEBS" -I"$DEBS/x86_64-linux-gnu" -w)
FILES="debug thread mpz utf8 object apply exception interrupt memory stackinfo compact init_module io hash byteslice
 platform alloc allocprof sharecommon stack_overflow process object_ref mpn mutex libuv uv/net_addr uv/event_loop
 uv/timer uv/tcp uv/udp uv/dns uv/system uv/signal"
fail=0
for f in $FILES; do
  g++ "${CXXFLAGS[@]}" -c $SRC/runtime/$f.cpp -o $OUT/$f.o 2> $OUT/$(echo $f | tr / _).err || { echo "FAIL $f: $(grep -m2 error $OUT/$(echo $f | tr / _).err)"; fail=1; }
done
g++ "${CXXFLAGS[@]}" -DMI_SHARED_LIB -DMI_SHARED_LIB_EXPORT -DMI_WIN_NOREDIRECT -DMI_MAX_ALIGN_SIZE=8 -DMI_SECURE=0 \
  -fno-semantic-interposition -I"$MI/include" -I"$MI/src" -c $SRC/runtime/mimalloc.cpp -o $OUT/mimalloc.o 2> $OUT/mimalloc.err \
  || { echo "FAIL mimalloc: $(grep -m3 error $OUT/mimalloc.err)"; fail=1; }
[ $fail = 0 ] && rm -f $OUT/libleanrt_pic.a && ar rcs $OUT/libleanrt_pic.a $OUT/*.o $OUT/uv/*.o && command ls -la $OUT/libleanrt_pic.a
echo "TPOFF32 relocs: $(readelf -rW $OUT/libleanrt_pic.a 2>/dev/null | grep -c R_X86_64_TPOFF32)  TLSGD relocs: $(readelf -rW $OUT/libleanrt_pic.a 2>/dev/null | grep -c R_X86_64_TLSGD)"
