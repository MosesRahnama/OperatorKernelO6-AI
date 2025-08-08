// Lean compiler output
// Module: OperatorKernelO6.Meta.Meta
// Imports: Init OperatorKernelO6.Kernel Mathlib.Data.Prod.Lex Mathlib.Tactic.Linarith
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_deltaDepth(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_eqCount(lean_object*);
static lean_object* l_OperatorKernelO6_Meta_num1___closed__0;
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_succ(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_measure(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_eqCount___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_num1;
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_num2;
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_num0;
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_sz(lean_object*);
LEAN_EXPORT uint8_t l_OperatorKernelO6_Meta_hasStep(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_sz___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_deltaDepth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_measure___boxed(lean_object*);
static lean_object* l_OperatorKernelO6_Meta_num2___closed__0;
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_recCount___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_integCount(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_tsize(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_recCount(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_recDepth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_recDepth(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_num3;
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_tsize___boxed(lean_object*);
static lean_object* l_OperatorKernelO6_Meta_num3___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_hasStep___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_integCount___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_deltaDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_OperatorKernelO6_Meta_deltaDepth(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_10);
return x_12;
}
case 2:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 0);
x_1 = x_13;
goto _start;
}
case 4:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 2);
x_1 = x_15;
goto _start;
}
default: 
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_2 = x_17;
x_3 = x_18;
goto block_7;
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_OperatorKernelO6_Meta_deltaDepth(x_2);
x_5 = l_OperatorKernelO6_Meta_deltaDepth(x_3);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_deltaDepth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OperatorKernelO6_Meta_deltaDepth(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_recDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_OperatorKernelO6_Meta_recDepth(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_10);
return x_12;
}
case 2:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 0);
x_1 = x_13;
goto _start;
}
case 4:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = l_OperatorKernelO6_Meta_deltaDepth(x_17);
x_19 = l_OperatorKernelO6_Meta_recDepth(x_15);
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = l_OperatorKernelO6_Meta_recDepth(x_16);
x_22 = lean_nat_add(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_22, x_23);
lean_dec(x_22);
return x_24;
}
default: 
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_2 = x_25;
x_3 = x_26;
goto block_7;
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_OperatorKernelO6_Meta_recDepth(x_2);
x_5 = l_OperatorKernelO6_Meta_recDepth(x_3);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_recDepth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OperatorKernelO6_Meta_recDepth(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_sz(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_7; lean_object* x_8; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(1u);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_7 = x_16;
x_8 = x_17;
goto block_14;
}
case 4:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = l_OperatorKernelO6_Meta_sz(x_18);
x_22 = l_OperatorKernelO6_Meta_sz(x_19);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = l_OperatorKernelO6_Meta_sz(x_20);
x_25 = lean_nat_add(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_25);
return x_27;
}
case 5:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_7 = x_28;
x_8 = x_29;
goto block_14;
}
default: 
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_1, 0);
x_2 = x_30;
goto block_6;
}
}
block_6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_OperatorKernelO6_Meta_sz(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_OperatorKernelO6_Meta_sz(x_7);
x_10 = l_OperatorKernelO6_Meta_sz(x_8);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_sz___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OperatorKernelO6_Meta_sz(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_eqCount(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 3:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_OperatorKernelO6_Meta_eqCount(x_3);
x_6 = l_OperatorKernelO6_Meta_eqCount(x_4);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
case 4:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = l_OperatorKernelO6_Meta_eqCount(x_8);
x_12 = l_OperatorKernelO6_Meta_eqCount(x_9);
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_OperatorKernelO6_Meta_eqCount(x_10);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
return x_15;
}
case 5:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = l_OperatorKernelO6_Meta_eqCount(x_16);
x_19 = l_OperatorKernelO6_Meta_eqCount(x_17);
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_20, x_21);
lean_dec(x_20);
return x_22;
}
default: 
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 0);
x_1 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_eqCount___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OperatorKernelO6_Meta_eqCount(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_integCount(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
case 1:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
x_1 = x_9;
goto _start;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = l_OperatorKernelO6_Meta_integCount(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_12);
return x_14;
}
case 4:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = l_OperatorKernelO6_Meta_integCount(x_15);
x_19 = l_OperatorKernelO6_Meta_integCount(x_16);
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = l_OperatorKernelO6_Meta_integCount(x_17);
x_22 = lean_nat_add(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
return x_22;
}
default: 
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_2 = x_23;
x_3 = x_24;
goto block_7;
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_OperatorKernelO6_Meta_integCount(x_2);
x_5 = l_OperatorKernelO6_Meta_integCount(x_3);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_integCount___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OperatorKernelO6_Meta_integCount(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_recCount(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_2 = x_9;
x_3 = x_10;
goto block_7;
}
case 4:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = l_OperatorKernelO6_Meta_recCount(x_11);
x_15 = l_OperatorKernelO6_Meta_recCount(x_12);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = l_OperatorKernelO6_Meta_recCount(x_13);
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_18);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_2 = x_21;
x_3 = x_22;
goto block_7;
}
default: 
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 0);
x_1 = x_23;
goto _start;
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_OperatorKernelO6_Meta_recCount(x_2);
x_5 = l_OperatorKernelO6_Meta_recCount(x_3);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_recCount___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OperatorKernelO6_Meta_recCount(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_measure(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_OperatorKernelO6_Meta_recDepth(x_1);
x_3 = l_OperatorKernelO6_Meta_sz(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_measure___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OperatorKernelO6_Meta_measure(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_OperatorKernelO6_Meta_hasStep(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
case 3:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
case 4:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 2);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
return x_11;
}
case 1:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
return x_13;
}
default: 
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
case 5:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
return x_17;
}
default: 
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_hasStep___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_OperatorKernelO6_Meta_hasStep(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_tsize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_6; lean_object* x_7; 
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_1;
}
case 3:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_6 = x_13;
x_7 = x_14;
goto block_12;
}
case 4:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = l_OperatorKernelO6_Meta_tsize(x_15);
x_19 = l_OperatorKernelO6_Meta_tsize(x_16);
x_20 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_OperatorKernelO6_Meta_tsize(x_17);
x_22 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
case 5:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_6 = x_24;
x_7 = x_25;
goto block_12;
}
default: 
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_1, 0);
x_2 = x_26;
goto block_5;
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_OperatorKernelO6_Meta_tsize(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_OperatorKernelO6_Meta_tsize(x_6);
x_9 = l_OperatorKernelO6_Meta_tsize(x_7);
x_10 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_tsize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OperatorKernelO6_Meta_tsize(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_OperatorKernelO6_Meta_num0() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_OperatorKernelO6_Meta_num1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_OperatorKernelO6_Meta_num1() {
_start:
{
lean_object* x_1; 
x_1 = l_OperatorKernelO6_Meta_num1___closed__0;
return x_1;
}
}
static lean_object* _init_l_OperatorKernelO6_Meta_num2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_OperatorKernelO6_Meta_num1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_OperatorKernelO6_Meta_num2() {
_start:
{
lean_object* x_1; 
x_1 = l_OperatorKernelO6_Meta_num2___closed__0;
return x_1;
}
}
static lean_object* _init_l_OperatorKernelO6_Meta_num3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_OperatorKernelO6_Meta_num2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_OperatorKernelO6_Meta_num3() {
_start:
{
lean_object* x_1; 
x_1 = l_OperatorKernelO6_Meta_num3___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_succ(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_OperatorKernelO6_Kernel(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Prod_Lex(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_Linarith(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_OperatorKernelO6_Meta_Meta(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_OperatorKernelO6_Kernel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Prod_Lex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_Linarith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_OperatorKernelO6_Meta_num0 = _init_l_OperatorKernelO6_Meta_num0();
lean_mark_persistent(l_OperatorKernelO6_Meta_num0);
l_OperatorKernelO6_Meta_num1___closed__0 = _init_l_OperatorKernelO6_Meta_num1___closed__0();
lean_mark_persistent(l_OperatorKernelO6_Meta_num1___closed__0);
l_OperatorKernelO6_Meta_num1 = _init_l_OperatorKernelO6_Meta_num1();
lean_mark_persistent(l_OperatorKernelO6_Meta_num1);
l_OperatorKernelO6_Meta_num2___closed__0 = _init_l_OperatorKernelO6_Meta_num2___closed__0();
lean_mark_persistent(l_OperatorKernelO6_Meta_num2___closed__0);
l_OperatorKernelO6_Meta_num2 = _init_l_OperatorKernelO6_Meta_num2();
lean_mark_persistent(l_OperatorKernelO6_Meta_num2);
l_OperatorKernelO6_Meta_num3___closed__0 = _init_l_OperatorKernelO6_Meta_num3___closed__0();
lean_mark_persistent(l_OperatorKernelO6_Meta_num3___closed__0);
l_OperatorKernelO6_Meta_num3 = _init_l_OperatorKernelO6_Meta_num3();
lean_mark_persistent(l_OperatorKernelO6_Meta_num3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
