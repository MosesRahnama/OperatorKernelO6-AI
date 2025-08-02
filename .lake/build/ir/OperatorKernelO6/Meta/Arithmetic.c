// Lean compiler output
// Module: OperatorKernelO6.Meta.Arithmetic
// Imports: Init OperatorKernelO6.Kernel OperatorKernelO6.Meta.Meta
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
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_toNat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_num___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_toNat(lean_object*);
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_toNat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_num_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_toNat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_num_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_num_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_toNat_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_num_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_num(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_mul___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_num(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 1)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = l_OperatorKernelO6_Meta_num(x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_num___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OperatorKernelO6_Meta_num(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_toNat(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_OperatorKernelO6_Meta_toNat(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
case 2:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
x_1 = x_6;
goto _start;
}
case 3:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_OperatorKernelO6_Meta_toNat(x_8);
x_11 = l_OperatorKernelO6_Meta_toNat(x_9);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
case 4:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 2);
x_1 = x_13;
goto _start;
}
default: 
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(0u);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_toNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OperatorKernelO6_Meta_toNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_toNat_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_2(x_5, x_12, x_13);
return x_14;
}
case 4:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_3(x_6, x_15, x_16, x_17);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_2(x_7, x_19, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_toNat_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_toNat_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_toNat_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_toNat_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_toNat_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_toNat_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_num_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_num_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_num_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_num_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_num_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_num_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_OperatorKernelO6_Meta_Arithmetic_0__OperatorKernelO6_Meta_num_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_OperatorKernelO6_Meta_toNat(x_1);
x_4 = l_OperatorKernelO6_Meta_toNat(x_2);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = l_OperatorKernelO6_Meta_num(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_OperatorKernelO6_Meta_add(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_OperatorKernelO6_Meta_toNat(x_1);
x_4 = l_OperatorKernelO6_Meta_toNat(x_2);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = l_OperatorKernelO6_Meta_num(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_OperatorKernelO6_Meta_mul(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_OperatorKernelO6_Kernel(uint8_t builtin, lean_object*);
lean_object* initialize_OperatorKernelO6_Meta_Meta(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_OperatorKernelO6_Meta_Arithmetic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_OperatorKernelO6_Kernel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_OperatorKernelO6_Meta_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
