// Lean compiler output
// Module: CORALean.Float.ContSet.Zonotope.Theorems.API
// Imports: public import Init public meta import Init public import CORALean.Float.ContSet.Zonotope.Theorems.MemGeneratorError public import CORALean.Float.ContSet.Zonotope.Theorems.PlusOuter public import CORALean.Float.ContSet.Zonotope.Theorems.LinCombOuter public import CORALean.Float.ContSet.Zonotope.Theorems.MtimesOuter public import CORALean.Float.ContSet.Zonotope.Theorems.IntervalOuter public import CORALean.Float.ContSet.Zonotope.Theorems.AbsorbErrorOuter public import CORALean.Float.ContSet.Zonotope.Theorems.ReduceByOuterRefines public import CORALean.Float.ContSet.Zonotope.Theorems.ReduceByOuter public import CORALean.Float.ContSet.Zonotope.Theorems.ReduceOuter public import CORALean.Float.ContSet.Zonotope.Theorems.ReduceAndAbsorbByOuter
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
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_MemGeneratorError(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_PlusOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_LinCombOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_MtimesOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_IntervalOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_AbsorbErrorOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_ReduceByOuterRefines(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_ReduceByOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_ReduceOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_ReduceAndAbsorbByOuter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_API(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_MemGeneratorError(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_PlusOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_LinCombOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_MtimesOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_IntervalOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_AbsorbErrorOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_ReduceByOuterRefines(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_ReduceByOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_ReduceOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Theorems_ReduceAndAbsorbByOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
