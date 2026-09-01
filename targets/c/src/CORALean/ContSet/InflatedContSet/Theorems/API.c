// Lean compiler output
// Module: CORALean.ContSet.InflatedContSet.Theorems.API
// Imports: public import Init public meta import Init public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset public import CORALean.ContSet.InflatedContSet.Theorems.MapSubset public import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset public import CORALean.ContSet.InflatedContSet.Theorems.LinCombSubset
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_InflatedContSet_Theorems_MonoSubset(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_InflatedContSet_Theorems_MapSubset(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_InflatedContSet_Theorems_PlusSubset(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_InflatedContSet_Theorems_LinCombSubset(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_InflatedContSet_Theorems_API(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_InflatedContSet_Theorems_MonoSubset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_InflatedContSet_Theorems_MapSubset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_InflatedContSet_Theorems_PlusSubset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_InflatedContSet_Theorems_LinCombSubset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
