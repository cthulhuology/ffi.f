ffi.f — SwiftForth x86_64 FUNCTION: ABI
======================================

Shadows SwiftForth `FUNCTION:` so library calls can pass and return
C structs under the System V AMD64 (Linux) and Windows x64 ABIs.
The kernel is not modified.

    include ../ffi/ffi.f          \ from a sibling project such as curl.f
    include ../../ffi/ffi.f       \ from raylib.f/linux

Load it **before** any `FUNCTION:` that needs struct marshalling.

Stack-comment struct tokens (one word, braces required):

    {n}        n-byte blob; MEMORY if n>16, else INTEGER eightbytes
    {%n}       n-byte SSE struct (float vector)
    {%%n}      n-byte SSE struct of doubles
    {cccc}     field letters: c/b 8-bit, h/s/w 16-bit, i 32-bit,
               l/q/p/x 64-bit, f float, d double

Forth passes a struct by address.  A struct return takes an implicit
destination buffer (pushed first) and leaves that address.

