// Lean compiler output
// Module: CORALean.Real.ContSet.Interval.Theorems.API
// Imports: public import Init public meta import Init public import CORALean.Real.ContSet.Interval.Theorems.Convex public import CORALean.Real.ContSet.Interval.Theorems.IsBounded public import CORALean.Real.ContSet.Interval.Theorems.IsClosed public import CORALean.Real.ContSet.Interval.Theorems.IsNonempty public import CORALean.Real.ContSet.Interval.Theorems.PlusExact public import CORALean.Real.ContSet.Interval.Theorems.LinCombOuter public import CORALean.Real.ContSet.Interval.Theorems.MtimesOuter
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
lean_object* initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_Convex(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_IsBounded(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_IsClosed(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_IsNonempty(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_PlusExact(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_LinCombOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_MtimesOuter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_API(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_Convex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_IsBounded(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_IsClosed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_IsNonempty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_PlusExact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_LinCombOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Interval_Theorems_MtimesOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
