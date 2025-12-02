// Lean compiler output
// Module: UEM
// Imports: public import Init public import UEM.Basic.Val public import UEM.Basic.DirectSum public import UEM.Basic.NullProjection public import UEM.Basic.Dimensions public import UEM.Objects.Sparke public import UEM.Objects.Hierarchy public import UEM.System.State public import UEM.Theorems.P1_NullProjection public import UEM.Theorems.P2_SparkeMonoid
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_UEM_Basic_Val(uint8_t builtin);
lean_object* initialize_UEM_Basic_DirectSum(uint8_t builtin);
lean_object* initialize_UEM_Basic_NullProjection(uint8_t builtin);
lean_object* initialize_UEM_Basic_Dimensions(uint8_t builtin);
lean_object* initialize_UEM_Objects_Sparke(uint8_t builtin);
lean_object* initialize_UEM_Objects_Hierarchy(uint8_t builtin);
lean_object* initialize_UEM_System_State(uint8_t builtin);
lean_object* initialize_UEM_Theorems_P1__NullProjection(uint8_t builtin);
lean_object* initialize_UEM_Theorems_P2__SparkeMonoid(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_UEM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UEM_Basic_Val(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UEM_Basic_DirectSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UEM_Basic_NullProjection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UEM_Basic_Dimensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UEM_Objects_Sparke(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UEM_Objects_Hierarchy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UEM_System_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UEM_Theorems_P1__NullProjection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_UEM_Theorems_P2__SparkeMonoid(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
