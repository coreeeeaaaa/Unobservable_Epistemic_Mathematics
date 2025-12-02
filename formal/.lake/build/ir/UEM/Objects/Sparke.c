// Lean compiler output
// Module: UEM.Objects.Sparke
// Imports: public import Init public import Mathlib.Algebra.Group.Defs public import Mathlib.Data.Set.Basic
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
LEAN_EXPORT lean_object* l_UEM_instZeroSparke(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UEM_instZeroSparke___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UEM_sparkeAdd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UEM_sparkeZero___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UEM_instAddSparke___redArg(lean_object*);
LEAN_EXPORT lean_object* l_UEM_instZeroSparke___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UEM_Time_ctorIdx(lean_object*);
lean_object* l_AddMonoid_toAddZeroClass___redArg(lean_object*);
LEAN_EXPORT lean_object* l_UEM_instAddSparke(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UEM_instZeroSparke___redArg(lean_object*);
LEAN_EXPORT lean_object* l_UEM_Sparke_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UEM_sparkeZero(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UEM_sparkeAdd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UEM_sparkeZero___redArg(lean_object*);
LEAN_EXPORT lean_object* l_UEM_sparkeZero___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UEM_Sparke_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UEM_Time_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UEM_Sparke_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UEM_Sparke_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_UEM_Sparke_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UEM_sparkeAdd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = lean_apply_2(x_4, x_5, x_7);
x_10 = lean_box(0);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_2(x_4, x_5, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_UEM_sparkeAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_UEM_sparkeAdd___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UEM_sparkeZero___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_AddMonoid_toAddZeroClass___redArg(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
x_5 = lean_box(0);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_UEM_sparkeZero(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_UEM_sparkeZero___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UEM_sparkeZero___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_UEM_sparkeZero___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UEM_sparkeZero___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_UEM_sparkeZero(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UEM_instAddSparke___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_UEM_sparkeAdd), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UEM_instAddSparke(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_UEM_sparkeAdd), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UEM_instZeroSparke___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_UEM_sparkeZero___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UEM_instZeroSparke(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_UEM_sparkeZero___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UEM_instZeroSparke___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_UEM_instZeroSparke___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UEM_instZeroSparke___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_UEM_instZeroSparke(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Mathlib_Algebra_Group_Defs(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Set_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_UEM_Objects_Sparke(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Group_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Set_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
