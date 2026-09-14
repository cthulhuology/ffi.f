\ ====================================================================
\ ffi.f -- Full x86_64 ABI for SwiftForth FUNCTION:
\
\ Load this file before defining FUNCTION: words that pass or return
\ structures.  It shadows FUNCTION: (and the LIB-INTERFACE parser /
\ wrapper generator) without modifying the SwiftForth kernel.
\
\ Stack-comment struct syntax (one token, braces required):
\
\   brace-n          n-byte struct; MEMORY if n>16, else INTEGER
\   brace-%n         n-byte SSE struct (float vector)
\   brace-%%n        n-byte SSE struct of doubles
\   brace-fields     C-like layout from field letters:
\                      c b      8-bit integer
\                      h s w    16-bit integer
\                      i        32-bit integer
\                      l q p x  64-bit integer / pointer
\                      f        32-bit float (SSE)
\                      d        64-bit double (SSE)
\
\ Structs are passed by address on the Forth data stack.  A struct
\ return takes an implicit destination address (pushed first) and
\ leaves that address as the Forth result.
\
\ System V AMD64 (Linux/macOS) and Windows x64 are both implemented.
\ ====================================================================

PACKAGE LIB-INTERFACE

PRIVATE

\ -? is undone by ?UNIQUE's /WARNING after the first header, so a
\ single -? at the top of the file does not silence later redefines.
WARNING @ CONSTANT FFI-WARN
WARNING OFF

VARG_DOUBLE 1+ CONSTANT ARG_STRUCT
RET_DOUBLE  1+ CONSTANT RET_STRUCT

0 CONSTANT CL_NONE
1 CONSTANT CL_INTEGER
2 CONSTANT CL_SSE
3 CONSTANT CL_MEMORY

32 CONSTANT MAX-FFI

VARIABLE #ARGS
VARIABLE #DARGS
VARIABLE HIDDEN-RET
VARIABLE STACK-BYTES
VARIABLE RET-SIZE
VARIABLE RET-N8
VARIABLE RET-MEM
CREATE RET-CL  2 ALLOT

CREATE A-KIND  MAX-FFI ALLOT
CREATE A-SIZE  MAX-FFI CELLS ALLOT
CREATE A-N8    MAX-FFI ALLOT
CREATE A-CL    MAX-FFI 2 * ALLOT
CREATE A-MEM   MAX-FFI ALLOT
CREATE A-PASS  MAX-FFI ALLOT
CREATE A-R0    MAX-FFI ALLOT
CREATE A-R1    MAX-FFI ALLOT
CREATE A-SOFF  MAX-FFI CELLS ALLOT
CREATE A-DSLOT MAX-FFI CELLS ALLOT

VARIABLE IREG#
VARIABLE FREG#
VARIABLE SLOT#
VARIABLE SOFF#
VARIABLE MEM?
VARIABLE SZ
VARIABLE ALN
VARIABLE FSZ
VARIABLE FAL
VARIABLE FCLS
CREATE EB-CL  2 ALLOT

: FFI-ERASE ( -- )
   0 #ARGS !  0 #DARGS !  0 HIDDEN-RET !  0 STACK-BYTES !
   0 RET-SIZE !  0 RET-N8 !  0 RET-MEM !  0 RET-CL C!  0 RET-CL 1+ C!
   A-KIND MAX-FFI ERASE
   A-SIZE MAX-FFI CELLS ERASE
   A-N8 MAX-FFI ERASE
   A-CL MAX-FFI 2 * ERASE
   A-MEM MAX-FFI ERASE
   A-PASS MAX-FFI ERASE
   A-R0 MAX-FFI ERASE
   A-R1 MAX-FFI ERASE
   A-SOFF MAX-FFI CELLS ERASE
   A-DSLOT MAX-FFI CELLS ERASE
   0 IREG# !  0 FREG# !  0 SLOT# !  0 SOFF# ! ;

: ALIGN-UP ( n align -- n' )
   DUP 0= IF  DROP EXIT  THEN
   1- TUCK + SWAP INVERT AND ;

: MERGE-CLASS ( c1 c2 -- c )
   2DUP = IF  DROP EXIT  THEN
   DUP CL_NONE = IF  DROP EXIT  THEN
   OVER CL_NONE = IF  NIP EXIT  THEN
   DUP CL_MEMORY = IF  NIP EXIT  THEN
   OVER CL_MEMORY = IF  DROP EXIT  THEN
   DUP CL_INTEGER = IF  NIP EXIT  THEN
   OVER CL_INTEGER = IF  DROP EXIT  THEN
   2DROP CL_SSE ;

: CLASS-EB ( offset class -- )
   SWAP 8 /  DUP 2 >= IF  2DROP  TRUE MEM? !  EXIT  THEN
   DUP EB-CL + C@  ROT MERGE-CLASS  SWAP EB-CL + C! ;

: FIELD-INFO ( char -- size align class )
   DUP [CHAR] A [CHAR] Z 1+ WITHIN IF  $20 +  THEN
   CASE
      [CHAR] c OF  1 1 CL_INTEGER  ENDOF
      [CHAR] b OF  1 1 CL_INTEGER  ENDOF
      [CHAR] h OF  2 2 CL_INTEGER  ENDOF
      [CHAR] s OF  2 2 CL_INTEGER  ENDOF
      [CHAR] w OF  2 2 CL_INTEGER  ENDOF
      [CHAR] i OF  4 4 CL_INTEGER  ENDOF
      [CHAR] l OF  8 8 CL_INTEGER  ENDOF
      [CHAR] q OF  8 8 CL_INTEGER  ENDOF
      [CHAR] p OF  8 8 CL_INTEGER  ENDOF
      [CHAR] x OF  8 8 CL_INTEGER  ENDOF
      [CHAR] f OF  4 4 CL_SSE      ENDOF
      [CHAR] d OF  8 8 CL_SSE      ENDOF
      DUP CR ." Unknown struct field: " EMIT
      TRUE ABORT" invalid struct field type"
   ENDCASE ;

: DIGITS? ( addr u -- flag )
   DUP 0= IF  2DROP FALSE EXIT  THEN
   0 DO  DUP I + C@ [CHAR] 0 [CHAR] 9 1+ WITHIN 0= IF
      DROP FALSE UNLOOP EXIT  THEN
   LOOP DROP TRUE ;

: DEC>N ( addr u -- n )
   BASE @ >R DECIMAL
   NUMBER? 1 <> ABORT" Invalid struct size"
   R> BASE ! ;

: FINISH-AGG ( -- size n8 c0 c1 mem )
   SZ @ 0= ABORT" Empty struct"
   SZ @ 16 > IF  TRUE MEM? !  THEN
   MEM? @ IF
      SZ @  0  CL_MEMORY CL_MEMORY TRUE
   ELSE
      SZ @  DUP 7 + 8 /  EB-CL C@  EB-CL 1+ C@  FALSE
   THEN ;

: ALL-SSE ( size -- size n8 c0 c1 mem )
   DUP SZ !  FALSE MEM? !  CL_NONE EB-CL C!  CL_NONE EB-CL 1+ C!
   DUP 16 > IF  DROP FINISH-AGG EXIT  THEN
   0 CL_SSE CLASS-EB
   DUP 8 > IF  8 CL_SSE CLASS-EB  THEN
   DROP FINISH-AGG ;

: ALL-INTEGER ( size -- size n8 c0 c1 mem )
   DUP SZ !  FALSE MEM? !  CL_NONE EB-CL C!  CL_NONE EB-CL 1+ C!
   DUP 16 > IF  DROP FINISH-AGG EXIT  THEN
   0 CL_INTEGER CLASS-EB
   DUP 8 > IF  8 CL_INTEGER CLASS-EB  THEN
   DROP FINISH-AGG ;

: PARSE-FIELDS ( addr u -- size n8 c0 c1 mem )
   0 SZ !  1 ALN !  FALSE MEM? !
   CL_NONE EB-CL C!  CL_NONE EB-CL 1+ C!
   OVER + SWAP ?DO
      I C@ FIELD-INFO  FCLS !  FAL !  FSZ !
      SZ @ FAL @ ALIGN-UP
      DUP FAL @ 1- AND IF  TRUE MEM? !  THEN
      DUP FCLS @ CLASS-EB
      FSZ @ + SZ !
      FAL @ ALN @ MAX ALN !
   LOOP
   SZ @ ALN @ ALIGN-UP SZ !
   FINISH-AGG ;

: PARSE-SPEC ( addr u -- size n8 c0 c1 mem )
   DUP 0= ABORT" Empty struct specifier"
   OVER C@ [CHAR] % = IF
      1 /STRING  DUP 0= ABORT" Missing struct size"
      OVER C@ [CHAR] % = IF  1 /STRING  THEN
      DEC>N ALL-SSE  EXIT
   THEN
   2DUP DIGITS? IF  DEC>N ALL-INTEGER  EXIT  THEN
   PARSE-FIELDS ;

: STRIP-BRACES ( addr u -- addr' u' )
   DUP 2 < ABORT" Invalid struct token"
   OVER C@ [CHAR] { <> ABORT" Invalid struct token"
   2DUP + 1- C@ [CHAR] } <> ABORT" Missing } in struct type"
   1 /STRING  1- ;

: STORE-ARG-AGG ( size n8 c0 c1 mem i -- )
   >R
   R@ A-MEM + C!
   R@ 2 * A-CL + 1+ C!
   R@ 2 * A-CL + C!
   R@ A-N8 + C!
   R> CELLS A-SIZE + ! ;

: STORE-RET-AGG ( size n8 c0 c1 mem -- )
   RET-MEM !
   RET-CL 1+ C!  RET-CL C!
   RET-N8 !
   RET-SIZE ! ;

: PARSE-STRUCT-ARG ( addr u -- )
   #ARGS @ MAX-FFI >= ABORT" Too many FFI arguments"
   STRIP-BRACES PARSE-SPEC  #ARGS @ STORE-ARG-AGG
   1 #DSI +!  1 #DARGS +! ;

: PARSE-STRUCT-RET ( addr u -- )
   STRIP-BRACES PARSE-SPEC STORE-RET-AGG ;

{ --------------------------------------------------------------------
Argument parser -- original tokens plus struct forms
-------------------------------------------------------------------- }

: (VARG) ( -- n )
   TOKEN {: addr len :}
   S" --" addr len COMPARE 0= IF
      #DSV @ #FSV @ D0= ABORT" Missing varargs"  ARG_NONE  EXIT  THEN
   S" ..." addr len COMPARE 0= ABORT" Syntax error"
   addr C@ [CHAR] { = IF
      addr len PARSE-STRUCT-ARG  1 #DSV +!  ARG_STRUCT  EXIT  THEN
   addr C@ [CHAR] % <> IF  1 #DSV +!  1 #DARGS +!  VARG_INT  EXIT  THEN
   1 #FSV +!  VARG_FLOAT  addr 1+ C@ [CHAR] % = - ;

: (ARG) ( -- n )
   #DSV @ #FSV @ OR IF  (VARG) EXIT  THEN
   TOKEN {: addr len :}
   S" --" addr len COMPARE 0= IF  ARG_NONE  EXIT  THEN
   S" ..." addr len COMPARE 0= IF  (VARG)  EXIT  THEN
   addr C@ [CHAR] { = IF
      addr len PARSE-STRUCT-ARG  ARG_STRUCT  EXIT  THEN
   addr C@ [CHAR] % <> IF  1 #DSI +!  1 #DARGS +!  ARG_INT  EXIT  THEN
   1 #FSI +!  ARG_FLOAT  addr 1+ C@ [CHAR] % = - ;

: (RET) ( -- n )
   TOKEN {: addr len :}
   S" )" addr len COMPARE 0= IF  RET_NONE EXIT  THEN
   addr C@ [CHAR] { = IF
      addr len PARSE-STRUCT-RET  RET_STRUCT  EXIT  THEN
   addr C@ [CHAR] % <> IF  RET_INT  EXIT  THEN
   RET_FLOAT addr 1+ C@ [CHAR] % = - ;

: +ARG ( n -- )
   DUP ARGS COUNT + C!  1 ARGS C+!
   ARGS C@ DUP #ARGS !  1- >R
   R@ A-KIND + C!
   R@ A-KIND + C@ ARG_STRUCT = IF  R> DROP EXIT  THEN
   R@ A-KIND + C@ CASE
      ARG_INT      OF  8  ENDOF
      ARG_FLOAT    OF  4  ENDOF
      ARG_DOUBLE   OF  8  ENDOF
      VARG_INT     OF  8  ENDOF
      VARG_FLOAT   OF  4  ENDOF
      VARG_DOUBLE  OF  8  ENDOF
      0 SWAP
   ENDCASE
   R> CELLS A-SIZE + ! ;

: +RET ( n -- )
   #RET @ 1 > ABORT" Illegal return values"  #RET +! ;

: FP-KIND? ( k -- flag )
   DUP ARG_FLOAT = OVER ARG_DOUBLE = OR
   OVER VARG_FLOAT = OR SWAP VARG_DOUBLE = OR ;

: FILL-DSLOTS ( -- )
   #DARGS @ 1-
   #ARGS @ 0 ?DO
      I A-KIND + C@ FP-KIND? IF
         -1 I CELLS A-DSLOT + !
      ELSE
         DUP I CELLS A-DSLOT + !  1-
      THEN
   LOOP DROP ;

: (PARSE-ARGS) ( -- )
   FFI-ERASE
   0 ARGS C!  0 #DSI !  0 #FSI !  0 #DSV !  0 #FSV !  0 #RET !
   PARSE-NAME S" (" COMPARE ABORT" Missing stack comment"
   BEGIN  (ARG) ?DUP WHILE  +ARG  REPEAT
   BEGIN  (RET) ?DUP WHILE  +RET  REPEAT
   FILL-DSLOTS ;

: PARSE-ARGS ( -- )
   >IN @ >R  TOKEN 2DROP  (PARSE-ARGS)  R> >IN ! ;

{ --------------------------------------------------------------------
Register / stack assignment
-------------------------------------------------------------------- }

: EB-CLASS ( i eb -- class )   SWAP 2 * + A-CL + C@ ;

: EB-LEN ( i eb -- n )
   OVER CELLS A-SIZE + @  SWAP 8 *  -  0 MAX  8 MIN ;

: N8-INTS ( i -- n )
   0 SWAP  DUP A-N8 + C@ 0 ?DO
      DUP I EB-CLASS CL_INTEGER = IF  SWAP 1+ SWAP  THEN
   LOOP DROP ;

: N8-SSES ( i -- n )
   0 SWAP  DUP A-N8 + C@ 0 ?DO
      DUP I EB-CLASS CL_SSE = IF  SWAP 1+ SWAP  THEN
   LOOP DROP ;

: ROUND8 ( n -- n' )   7 + -8 AND ;

: >STACK ( i -- )
   1 OVER A-PASS + C!
   SOFF# @ OVER CELLS A-SOFF + !
   CELLS A-SIZE + @ ROUND8  SOFF# +! ;

SYSTEM-WINDOWS? [IF]

: WIN-FIT ( n -- flag )
   DUP 1 = OVER 2 = OR OVER 4 = OR SWAP 8 = OR ;

: WIN-RECLASS ( -- )
   #ARGS @ 0 ?DO
      I A-KIND + C@ ARG_STRUCT = IF
         I CELLS A-SIZE + @ WIN-FIT IF
            0 I A-MEM + C!  1 I A-N8 + C!
            CL_INTEGER I 2 * A-CL + C!  CL_NONE I 2 * A-CL + 1+ C!
         ELSE
            1 I A-MEM + C!  0 I A-N8 + C!
            CL_MEMORY I 2 * A-CL + C!
         THEN
      THEN
   LOOP
   #RET @ RET_STRUCT = IF
      RET-SIZE @ WIN-FIT IF
         0 RET-MEM !  1 RET-N8 !
         CL_INTEGER RET-CL C!  CL_NONE RET-CL 1+ C!
      ELSE
         1 RET-MEM !  0 RET-N8 !  CL_MEMORY RET-CL C!
      THEN
   THEN ;

: WIN-SLOT-REG ( i -- )
   SLOT# @ 4 < IF
      0 OVER A-PASS + C!
      SLOT# @ SWAP A-R0 + C!
   ELSE  >STACK  THEN
   1 SLOT# +! ;

: ASSIGN ( -- )
   WIN-RECLASS
   0 SLOT# !  32 SOFF# !  0 HIDDEN-RET !
   RET-MEM @ IF  -1 HIDDEN-RET !  1 SLOT# !  THEN
   #ARGS @ 0 ?DO
      I A-KIND + C@ CASE
         ARG_INT      OF  I WIN-SLOT-REG  ENDOF
         VARG_INT     OF  I WIN-SLOT-REG  ENDOF
         ARG_FLOAT    OF  I WIN-SLOT-REG  ENDOF
         ARG_DOUBLE   OF  I WIN-SLOT-REG  ENDOF
         VARG_FLOAT   OF  I WIN-SLOT-REG  ENDOF
         VARG_DOUBLE  OF  I WIN-SLOT-REG  ENDOF
         ARG_STRUCT   OF  I WIN-SLOT-REG  ENDOF
      ENDCASE
   LOOP
   SOFF# @ 15 + -16 AND STACK-BYTES ! ;

[ELSE]

: STRUCT-FITS ( i -- flag )
   DUP N8-INTS IREG# @ + 6 > IF  DROP FALSE EXIT  THEN
   N8-SSES FREG# @ + 8 > 0= ;

: ASSIGN-INT ( i -- )
   IREG# @ 6 < IF
      0 OVER A-PASS + C!
      IREG# @ SWAP A-R0 + C!
      1 IREG# +!
   ELSE  >STACK  THEN ;

: ASSIGN-FP ( i -- )
   FREG# @ 8 < IF
      0 OVER A-PASS + C!
      FREG# @ SWAP A-R0 + C!
      1 FREG# +!
   ELSE  >STACK  THEN ;

: ARG-R! ( i eb r -- )
   -ROT IF  A-R1  ELSE  A-R0  THEN  + C! ;

: ASSIGN-STRUCT-REGS ( i -- )
   0 OVER A-PASS + C!
   DUP A-N8 + C@ 0 ?DO
      DUP I EB-CLASS CL_INTEGER = IF
         DUP I IREG# @ ARG-R!  1 IREG# +!
      ELSE
         DUP I FREG# @ ARG-R!  1 FREG# +!
      THEN
   LOOP DROP ;

: ASSIGN-STRUCT ( i -- )
   DUP A-MEM + C@ IF  >STACK EXIT  THEN
   DUP STRUCT-FITS 0= IF  >STACK EXIT  THEN
   ASSIGN-STRUCT-REGS ;

: ASSIGN ( -- )
   0 IREG# !  0 FREG# !  0 SOFF# !  0 HIDDEN-RET !
   RET-MEM @ IF  -1 HIDDEN-RET !  1 IREG# !  THEN
   #ARGS @ 0 ?DO
      I A-KIND + C@ CASE
         ARG_INT      OF  I ASSIGN-INT     ENDOF
         VARG_INT     OF  I ASSIGN-INT     ENDOF
         ARG_FLOAT    OF  I ASSIGN-FP      ENDOF
         ARG_DOUBLE   OF  I ASSIGN-FP      ENDOF
         VARG_FLOAT   OF  I ASSIGN-FP      ENDOF
         VARG_DOUBLE  OF  I ASSIGN-FP      ENDOF
         ARG_STRUCT   OF  I ASSIGN-STRUCT  ENDOF
      ENDCASE
   LOOP
   SOFF# @ 15 + -16 AND STACK-BYTES ! ;

[THEN]

{ --------------------------------------------------------------------
Assembler emitters
-------------------------------------------------------------------- }

SYSTEM-WINDOWS? [IF]

: RAX>IREG ( n -- )
   CASE
      0 OF  [+ASM]  RAX RCX MOV  [-ASM]  ENDOF
      1 OF  [+ASM]  RAX RDX MOV  [-ASM]  ENDOF
      2 OF  [+ASM]  RAX R8  MOV  [-ASM]  ENDOF
      3 OF  [+ASM]  RAX R9  MOV  [-ASM]  ENDOF
      DUP CR . TRUE ABORT" bad integer register"
   ENDCASE ;

: LOAD-HIDDEN ( -- )
   HIDDEN-RET @ IF
      #DARGS @ CELLS [+ASM]  [RBP] RCX MOV  [-ASM]
   THEN ;

[ELSE]

: RAX>IREG ( n -- )
   CASE
      0 OF  [+ASM]  RAX RDI MOV  [-ASM]  ENDOF
      1 OF  [+ASM]  RAX RSI MOV  [-ASM]  ENDOF
      2 OF  [+ASM]  RAX RDX MOV  [-ASM]  ENDOF
      3 OF  [+ASM]  RAX RCX MOV  [-ASM]  ENDOF
      4 OF  [+ASM]  RAX R8  MOV  [-ASM]  ENDOF
      5 OF  [+ASM]  RAX R9  MOV  [-ASM]  ENDOF
      DUP CR . TRUE ABORT" bad integer register"
   ENDCASE ;

: LOAD-HIDDEN ( -- )
   HIDDEN-RET @ IF
      #DARGS @ CELLS [+ASM]  [RBP] RDI MOV  [-ASM]
   THEN ;

[THEN]

VARIABLE T-ARG
VARIABLE T-OFF
VARIABLE T-LEN
VARIABLE T-XMM

: RBP>RAX ( slot -- )   CELLS [+ASM]  [RBP] RAX MOV  [-ASM] ;
: RBP>R10 ( slot -- )   CELLS [+ASM]  [RBP] R10 MOV  [-ASM] ;

: LOAD-I-FROM-R10 ( -- )
   T-LEN @ 8 = IF  T-OFF @ [+ASM]  [R10] RAX MOV     [-ASM]  EXIT THEN
   T-LEN @ 4 = IF  T-OFF @ [+ASM]  [R10] EAX MOV     [-ASM]  EXIT THEN
   T-LEN @ 2 = IF  T-OFF @ [+ASM]  [R10] RAX MOVZXW  [-ASM]  EXIT THEN
   T-LEN @ 1 = IF  T-OFF @ [+ASM]  [R10] RAX MOVZX   [-ASM]  EXIT THEN
   T-LEN @ CR . TRUE ABORT" unsupported integer eightbyte size" ;

: STORE-I-TO-R11 ( -- )
   T-LEN @ 8 = IF  T-OFF @ [+ASM]  RAX SWAP [R11] MOV  [-ASM]  EXIT THEN
   T-LEN @ 4 = IF  T-OFF @ [+ASM]  EAX SWAP [R11] MOV  [-ASM]  EXIT THEN
   T-LEN @ 2 = IF  T-OFF @ [+ASM]  AX  SWAP [R11] MOV  [-ASM]  EXIT THEN
   T-LEN @ 1 = IF  T-OFF @ [+ASM]  AL  SWAP [R11] MOV  [-ASM]  EXIT THEN
   T-LEN @ CR . TRUE ABORT" unsupported integer store size" ;

: MOVSD-XMM ( -- )
   T-XMM @ 0 = IF  T-OFF @ [+ASM]  [R10] XMM0 MOVSD  [-ASM]  EXIT THEN
   T-XMM @ 1 = IF  T-OFF @ [+ASM]  [R10] XMM1 MOVSD  [-ASM]  EXIT THEN
   T-XMM @ 2 = IF  T-OFF @ [+ASM]  [R10] XMM2 MOVSD  [-ASM]  EXIT THEN
   T-XMM @ 3 = IF  T-OFF @ [+ASM]  [R10] XMM3 MOVSD  [-ASM]  EXIT THEN
   T-XMM @ 4 = IF  T-OFF @ [+ASM]  [R10] XMM4 MOVSD  [-ASM]  EXIT THEN
   T-XMM @ 5 = IF  T-OFF @ [+ASM]  [R10] XMM5 MOVSD  [-ASM]  EXIT THEN
   T-XMM @ 6 = IF  T-OFF @ [+ASM]  [R10] XMM6 MOVSD  [-ASM]  EXIT THEN
   T-XMM @ 7 = IF  T-OFF @ [+ASM]  [R10] XMM7 MOVSD  [-ASM]  EXIT THEN
   T-XMM @ CR . TRUE ABORT" bad xmm" ;

: MOVSS-XMM ( -- )
   T-XMM @ 0 = IF  T-OFF @ [+ASM]  [R10] XMM0 MOVSS  [-ASM]  EXIT THEN
   T-XMM @ 1 = IF  T-OFF @ [+ASM]  [R10] XMM1 MOVSS  [-ASM]  EXIT THEN
   T-XMM @ 2 = IF  T-OFF @ [+ASM]  [R10] XMM2 MOVSS  [-ASM]  EXIT THEN
   T-XMM @ 3 = IF  T-OFF @ [+ASM]  [R10] XMM3 MOVSS  [-ASM]  EXIT THEN
   T-XMM @ 4 = IF  T-OFF @ [+ASM]  [R10] XMM4 MOVSS  [-ASM]  EXIT THEN
   T-XMM @ 5 = IF  T-OFF @ [+ASM]  [R10] XMM5 MOVSS  [-ASM]  EXIT THEN
   T-XMM @ 6 = IF  T-OFF @ [+ASM]  [R10] XMM6 MOVSS  [-ASM]  EXIT THEN
   T-XMM @ 7 = IF  T-OFF @ [+ASM]  [R10] XMM7 MOVSS  [-ASM]  EXIT THEN
   T-XMM @ CR . TRUE ABORT" bad xmm" ;

: LOAD-SSE-FROM-R10 ( -- )
   T-LEN @ 4 > IF  MOVSD-XMM  ELSE  MOVSS-XMM  THEN ;

: TEMP>XMM-SD ( xmm -- )
   CASE
      0 OF  [+ASM]  -8 [RBP] XMM0 MOVSD  [-ASM]  ENDOF
      1 OF  [+ASM]  -8 [RBP] XMM1 MOVSD  [-ASM]  ENDOF
      2 OF  [+ASM]  -8 [RBP] XMM2 MOVSD  [-ASM]  ENDOF
      3 OF  [+ASM]  -8 [RBP] XMM3 MOVSD  [-ASM]  ENDOF
      4 OF  [+ASM]  -8 [RBP] XMM4 MOVSD  [-ASM]  ENDOF
      5 OF  [+ASM]  -8 [RBP] XMM5 MOVSD  [-ASM]  ENDOF
      6 OF  [+ASM]  -8 [RBP] XMM6 MOVSD  [-ASM]  ENDOF
      7 OF  [+ASM]  -8 [RBP] XMM7 MOVSD  [-ASM]  ENDOF
      DUP CR . TRUE ABORT" bad xmm"
   ENDCASE ;

: TEMP>XMM-SS ( xmm -- )
   CASE
      0 OF  [+ASM]  -8 [RBP] XMM0 MOVSS  [-ASM]  ENDOF
      1 OF  [+ASM]  -8 [RBP] XMM1 MOVSS  [-ASM]  ENDOF
      2 OF  [+ASM]  -8 [RBP] XMM2 MOVSS  [-ASM]  ENDOF
      3 OF  [+ASM]  -8 [RBP] XMM3 MOVSS  [-ASM]  ENDOF
      4 OF  [+ASM]  -8 [RBP] XMM4 MOVSS  [-ASM]  ENDOF
      5 OF  [+ASM]  -8 [RBP] XMM5 MOVSS  [-ASM]  ENDOF
      6 OF  [+ASM]  -8 [RBP] XMM6 MOVSS  [-ASM]  ENDOF
      7 OF  [+ASM]  -8 [RBP] XMM7 MOVSS  [-ASM]  ENDOF
      DUP CR . TRUE ABORT" bad xmm"
   ENDCASE ;

: XMM>R11-SD ( off xmm -- )
   CASE
      0 OF  [+ASM]  XMM0 SWAP [R11] MOVSD  [-ASM]  ENDOF
      1 OF  [+ASM]  XMM1 SWAP [R11] MOVSD  [-ASM]  ENDOF
      2 OF  [+ASM]  XMM2 SWAP [R11] MOVSD  [-ASM]  ENDOF
      3 OF  [+ASM]  XMM3 SWAP [R11] MOVSD  [-ASM]  ENDOF
      4 OF  [+ASM]  XMM4 SWAP [R11] MOVSD  [-ASM]  ENDOF
      5 OF  [+ASM]  XMM5 SWAP [R11] MOVSD  [-ASM]  ENDOF
      6 OF  [+ASM]  XMM6 SWAP [R11] MOVSD  [-ASM]  ENDOF
      7 OF  [+ASM]  XMM7 SWAP [R11] MOVSD  [-ASM]  ENDOF
      DUP CR . TRUE ABORT" bad xmm"
   ENDCASE ;

: XMM>R11-SS ( off xmm -- )
   CASE
      0 OF  [+ASM]  XMM0 SWAP [R11] MOVSS  [-ASM]  ENDOF
      1 OF  [+ASM]  XMM1 SWAP [R11] MOVSS  [-ASM]  ENDOF
      2 OF  [+ASM]  XMM2 SWAP [R11] MOVSS  [-ASM]  ENDOF
      3 OF  [+ASM]  XMM3 SWAP [R11] MOVSS  [-ASM]  ENDOF
      4 OF  [+ASM]  XMM4 SWAP [R11] MOVSS  [-ASM]  ENDOF
      5 OF  [+ASM]  XMM5 SWAP [R11] MOVSS  [-ASM]  ENDOF
      6 OF  [+ASM]  XMM6 SWAP [R11] MOVSS  [-ASM]  ENDOF
      7 OF  [+ASM]  XMM7 SWAP [R11] MOVSS  [-ASM]  ENDOF
      DUP CR . TRUE ABORT" bad xmm"
   ENDCASE ;

: ARG-R ( i eb -- r )
   IF  A-R1  ELSE  A-R0  THEN  + C@ ;

{ --------------------------------------------------------------------
Place arguments
-------------------------------------------------------------------- }

: COPY-STRUCT-STACK ( i -- )
   DUP CELLS A-DSLOT + @ RBP>R10
   [+ASM]  R10 RSI MOV  [-ASM]
   DUP CELLS A-SOFF + @ [+ASM]  [RSP] RDI LEA  [-ASM]
   CELLS A-SIZE + @ [+ASM]  # RCX MOV  CLD  REP MOVSB  [-ASM] ;

: STORE-INT-STACK ( i -- )
   DUP CELLS A-DSLOT + @ RBP>RAX
   CELLS A-SOFF + @ [+ASM]  RAX SWAP [RSP] MOV  [-ASM] ;

: PLACE-STACK-ARGS ( -- )
   #ARGS @ 0 ?DO
      I A-PASS + C@ IF
         I A-KIND + C@ ARG_STRUCT = IF
            I COPY-STRUCT-STACK
         ELSE
            I A-KIND + C@ DUP ARG_INT = SWAP VARG_INT = OR IF
               I STORE-INT-STACK
            THEN
         THEN
      THEN
   LOOP ;

: LOAD-INT-ARG ( i -- )
   DUP A-KIND + C@ ARG_STRUCT = IF
      DUP T-ARG !
      CELLS A-DSLOT + @ RBP>R10
      T-ARG @ A-MEM + C@ IF
         [+ASM]  R10 RAX MOV  [-ASM]
         T-ARG @ 0 ARG-R RAX>IREG  EXIT
      THEN
      T-ARG @ A-N8 + C@ 0 ?DO
         T-ARG @ I EB-CLASS CL_INTEGER = IF
            I 8 * T-OFF !
            T-ARG @ I EB-LEN T-LEN !
            LOAD-I-FROM-R10
            T-ARG @ I ARG-R RAX>IREG
         THEN
      LOOP
   ELSE
      DUP CELLS A-DSLOT + @ RBP>RAX
      0 ARG-R RAX>IREG
   THEN ;

: LOAD-IREGS ( -- )
   #ARGS @ 0 ?DO
      I A-PASS + C@ 0= IF
         I A-KIND + C@ DUP ARG_INT = OVER VARG_INT = OR
         SWAP ARG_STRUCT = OR IF
            I LOAD-INT-ARG
         THEN
      THEN
   LOOP ;

: LOAD-STRUCT-SSE ( i -- )
   DUP T-ARG !
   CELLS A-DSLOT + @ RBP>R10
   T-ARG @ A-N8 + C@ 0 ?DO
      T-ARG @ I EB-CLASS CL_SSE = IF
         I 8 * T-OFF !
         T-ARG @ I EB-LEN T-LEN !
         T-ARG @ I ARG-R T-XMM !
         LOAD-SSE-FROM-R10
      THEN
   LOOP ;

: LOAD-SCALAR-FP ( i -- )
   DUP A-KIND + C@ DUP ARG_DOUBLE = SWAP VARG_DOUBLE = OR IF
      [+ASM]  -8 [RBP] QWORD FSTP  [-ASM]
      DUP A-PASS + C@ IF
         CELLS A-SOFF + @ [+ASM]  -8 [RBP] RAX MOV  RAX SWAP [RSP] MOV  [-ASM]
      ELSE
         0 ARG-R TEMP>XMM-SD
      THEN
   ELSE
      [+ASM]  -8 [RBP] DWORD FSTP  [-ASM]
      DUP A-PASS + C@ IF
         CELLS A-SOFF + @ [+ASM]  -8 [RBP] EAX MOV  EAX SWAP [RSP] MOV  [-ASM]
      ELSE
         0 ARG-R TEMP>XMM-SS
      THEN
   THEN ;

: LOAD-FREGS ( -- )
   #ARGS @ 0 ?DO
      #ARGS @ 1- I -  DUP A-KIND + C@ FP-KIND? IF
         LOAD-SCALAR-FP
      ELSE  DROP  THEN
   LOOP
   #ARGS @ 0 ?DO
      I A-KIND + C@ ARG_STRUCT =  I A-PASS + C@ 0= AND IF
         I LOAD-STRUCT-SSE
      THEN
   LOOP ;

{ --------------------------------------------------------------------
Returns
-------------------------------------------------------------------- }

: (RINT) ( -- )
   [+ASM]  RAX RBX MOV   RAX $20 # SHR   0= IF   EBX RBX MOVSXD   THEN  [-ASM] ;

: (RINT2) ( -- )
   [+ASM]  -8 [RBP] RBP LEA   RAX 0 [RBP] MOV   RDX RBX MOV  [-ASM] ;

: (RFLOAT) ( -- )
   [+ASM]  XMM0 -8 [RBP] MOVSS   -8 [RBP] DWORD FLD   POP(RBX)  [-ASM] ;

: (RDOUBLE) ( -- )
   [+ASM]  XMM0 -8 [RBP] MOVSD   -8 [RBP] QWORD FLD   POP(RBX)  [-ASM] ;

: RET-EB-CLASS ( eb -- class )   RET-CL + C@ ;

: RET-EB-LEN ( eb -- n )
   RET-SIZE @  SWAP 8 *  -  0 MAX  8 MIN ;

: RET-EB-XMM ( eb -- xmm )
   0 SWAP 0 ?DO
      I RET-EB-CLASS CL_SSE = IF  1+  THEN
   LOOP ;

: RET-EB-IREX ( eb -- 0=rax|1=rdx )
   0 SWAP 0 ?DO
      I RET-EB-CLASS CL_INTEGER = IF  1+  THEN
   LOOP ;

: COPY-RET-EB ( eb -- )
   DUP RET-EB-CLASS CL_INTEGER = IF
      DUP RET-EB-IREX IF  [+ASM]  RDX RAX MOV  [-ASM]  THEN
      DUP 8 * T-OFF !  RET-EB-LEN T-LEN !  STORE-I-TO-R11  EXIT
   THEN
   DUP RET-EB-CLASS CL_SSE = IF
      DUP RET-EB-XMM T-XMM !
      DUP 8 * T-OFF !  RET-EB-LEN T-LEN !
      T-LEN @ 4 > IF
         T-OFF @ T-XMM @ XMM>R11-SD
      ELSE
         T-OFF @ T-XMM @ XMM>R11-SS
      THEN  EXIT
   THEN
   DROP ;

: COPY-RET-STRUCT ( -- )
   RET-MEM @ 0= IF
      RET-N8 @ 0 ?DO  I COPY-RET-EB  LOOP
   THEN ;

: HANDLE-STRUCT-RET ( -- )
   #DARGS @ CELLS [+ASM]  [RBP] R11 MOV  [-ASM]
   COPY-RET-STRUCT
   [+ASM]  R11 RBX MOV  [-ASM]
   #DARGS @ 1+ CELLS [+ASM]  # RBP ADD  [-ASM] ;

: HANDLE-RETURN ( -- )
   #RET @ CASE
      RET_NONE   OF  [+ASM]  POP(RBX)  [-ASM]  ENDOF
      RET_INT    OF  (RINT)  ENDOF
      RET_DINT   OF  (RINT2)  ENDOF
      RET_FLOAT  OF  (RFLOAT)  ENDOF
      RET_DOUBLE OF  (RDOUBLE)  ENDOF
      RET_STRUCT OF  HANDLE-STRUCT-RET  ENDOF
      [+ASM]  POP(RBX)  [-ASM]
   ENDCASE ;

{ --------------------------------------------------------------------
Wrapper generator
-------------------------------------------------------------------- }

: EXT-INLINE ( -- )
   ASSIGN
   [+ASM]  RDI PUSH   RSI PUSH   RSP R12 MOV   -16 # RSP AND  [-ASM]
   STACK-BYTES @ IF
      STACK-BYTES @ [+ASM]  # RSP SUB  [-ASM]
   THEN
   PLACE-STACK-ARGS
   LOAD-IREGS
   LOAD-FREGS
   LOAD-HIDDEN
   [+ASM]
      #FSV @ # EAX MOV
      0 [RBX] RBX MOV   RBX CALL
      R12 RSP MOV   RSI POP   RDI POP
   [-ASM]
   #RET @ RET_STRUCT = IF
      HANDLE-RETURN
   ELSE
      #DARGS @ ?DUP IF  [+ASM]  CELLS # RBP ADD  [-ASM]  THEN
      HANDLE-RETURN
   THEN
   [+ASM]  RET  [-ASM] ;

PUBLIC

: FUNCTION: ( "name" -- )
   DEPTH >R
   'LIB @REL DUP 0= ABORT" No library"
   PARSE-ARGS  >AS @ IF  -?  THEN
   CREATE +SMUDGE
   @ ?DUP IF  LAST @ COUNT GET-PROC
      DUP 0=  @REQUIRED AND
   ABORT" not in current library" THEN
   ?DUP 0= IF  ['] NOPROC >CODE  THEN
   ( proc) ,  ( lib) 'LIB @REL ,REL
   EXT-INLINE  (EXT-INLINE)
   IMPORTS >LINK  LAST @ ,REL
   >AS @ 0= IF  -SMUDGE
      BEGIN  DEPTH R@ > WHILE  DROP  REPEAT  R> DROP  EXIT  THEN
   >IN @  >AS @ >IN !
   'CFA @ HEADER  ,JMP
   >IN ! 0 >AS !
   BEGIN  DEPTH R@ > WHILE  DROP  REPEAT  R> DROP ;

FFI-WARN WARNING !

END-PACKAGE
