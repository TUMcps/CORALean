// Lean compiler output
// Module: CORALean.Real.ContSet.Zonotope.Operations.API
// Imports: public import Init public meta import Init public import CORALean.Real.ContSet.Zonotope.Operations.Plus public import CORALean.Real.ContSet.Zonotope.Operations.Mtimes public import CORALean.Real.ContSet.Zonotope.Operations.Interval public import CORALean.Real.ContSet.Zonotope.Operations.MtimesIntervalMat public import CORALean.Real.ContSet.Zonotope.Operations.LinComb public import CORALean.Real.ContSet.Zonotope.Operations.Reduce
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
lean_object* initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_Plus(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_Mtimes(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_Interval(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_MtimesIntervalMat(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_LinComb(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_Reduce(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_API(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_Plus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_Mtimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_Interval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_MtimesIntervalMat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_LinComb(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
