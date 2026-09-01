// Lean compiler output
// Module: CORALean.ContDynamics.LinearSys.Theorems.API
// Imports: public import Init public meta import Init public import CORALean.ContDynamics.LinearSys.Theorems.Discretize public import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuter public import CORALean.ContDynamics.LinearSys.Theorems.ReachOuter public import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterZonotope public import CORALean.ContDynamics.LinearSys.Theorems.StepInputOuter public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter public import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants public import CORALean.ContDynamics.LinearSys.Theorems.WeightedIntegral
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
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_Discretize(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_InputIntegrable(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_InputSolutionOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_ReachOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_ReachOuterZonotope(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_StepInputOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_TimeIntervalOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_TrajectoryTimeIntervalOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_VariationOfConstants(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_WeightedIntegral(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_API(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_Discretize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_InputIntegrable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_InputSolutionOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_ReachOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_ReachOuterZonotope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_StepInputOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_TimeIntervalOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_TrajectoryTimeIntervalOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_VariationOfConstants(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_WeightedIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
