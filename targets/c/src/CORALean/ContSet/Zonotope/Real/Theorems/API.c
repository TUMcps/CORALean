// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Real.Theorems.API
// Imports: public import Init public meta import Init public import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact public import CORALean.ContSet.Zonotope.Real.Theorems.IntervalOuter public import CORALean.ContSet.Zonotope.Real.Theorems.Convex public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact public import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatOuter public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter
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
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_Coefficient(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_PlusExact(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_MtimesExact(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_IntervalOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_Convex(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_IsBounded(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_IsCompact(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_LinCombOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_MtimesIntervalMatOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_ReduceOuter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_API(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_Coefficient(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_PlusExact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_MtimesExact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_IntervalOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_Convex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_IsBounded(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_IsCompact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_LinCombOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_MtimesIntervalMatOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_ReduceOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
