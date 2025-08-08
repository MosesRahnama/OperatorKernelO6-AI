// Lean compiler output
// Module: OperatorKernelO6.Meta.Termination_Lex
// Imports: Init OperatorKernelO6.Kernel Init.WF Mathlib.Data.Prod.Lex Mathlib.SetTheory.Ordinal.Basic Mathlib.SetTheory.Ordinal.Arithmetic Mathlib.SetTheory.Ordinal.Exponential Mathlib.Algebra.Order.SuccPred Mathlib.Data.Nat.Cast.Order.Basic
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
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Termination__Lex_0__OperatorKernelO6_Meta_kappa_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_kappa(lean_object*);
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Termination__Lex_0__OperatorKernelO6_Meta_kappa_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_kappa___boxed(lean_object*);
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_kappa(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(2u);
return x_2;
}
case 5:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_OperatorKernelO6_Meta_kappa___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_OperatorKernelO6_Meta_kappa(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Termination__Lex_0__OperatorKernelO6_Meta_kappa_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_2, x_5, x_6, x_7);
return x_8;
}
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_3, x_9, x_10);
return x_11;
}
default: 
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_apply_3(x_4, x_1, lean_box(0), lean_box(0));
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_OperatorKernelO6_Meta_Termination__Lex_0__OperatorKernelO6_Meta_kappa_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_OperatorKernelO6_Meta_Termination__Lex_0__OperatorKernelO6_Meta_kappa_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_OperatorKernelO6_Kernel(uint8_t builtin, lean_object*);
lean_object* initialize_Init_WF(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Prod_Lex(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_SetTheory_Ordinal_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_SetTheory_Ordinal_Arithmetic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_SetTheory_Ordinal_Exponential(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Order_SuccPred(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Cast_Order_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_OperatorKernelO6_Meta_Termination__Lex(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_OperatorKernelO6_Kernel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Prod_Lex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_SetTheory_Ordinal_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_SetTheory_Ordinal_Arithmetic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_SetTheory_Ordinal_Exponential(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Order_SuccPred(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Cast_Order_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
