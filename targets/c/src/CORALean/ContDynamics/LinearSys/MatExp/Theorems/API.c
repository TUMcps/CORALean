// Lean compiler output
// Module: CORALean.ContDynamics.LinearSys.MatExp.Theorems.API
// Imports: public import Init public meta import Init public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrix public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpDiff public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpEnclosure public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral
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
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_CorrCoeffBound(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_ConstCorrectionMatrix(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_CorrectionMatrix(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_ExpDiff(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_ExpEnclosure(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_ExpIntegral(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_API(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_CorrCoeffBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_ConstCorrectionMatrix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_CorrectionMatrix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_ExpDiff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_ExpEnclosure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_MatExp_Theorems_ExpIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
