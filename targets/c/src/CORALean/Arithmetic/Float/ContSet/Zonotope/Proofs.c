// Lean compiler output
// Module: CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs
// Imports: public import Init public meta import Init public import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.MemGeneratorError public import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.PlusSound public import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.AbsorbErrorSound public import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.MtimesSound public import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.ReduceSound public import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.ReduceAndAbsorbSound public import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs.IntervalSound
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
lean_object* initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_MemGeneratorError(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_PlusSound(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_AbsorbErrorSound(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_MtimesSound(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_ReduceSound(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_ReduceAndAbsorbSound(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_IntervalSound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_MemGeneratorError(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_PlusSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_AbsorbErrorSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_MtimesSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_ReduceSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_ReduceAndAbsorbSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Zonotope_Proofs_IntervalSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
