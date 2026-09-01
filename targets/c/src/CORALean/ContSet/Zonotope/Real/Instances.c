// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Real.Instances
// Imports: public import Init public meta import Init public import CORALean.ContSet.Zonotope.Real.Theorems.API
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instContSetZonotopeVecReal(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instContSetZonotopeVecReal___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instContSetZonotopeVecReal(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instContSetZonotopeVecReal___boxed(lean_object* v_n_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_CORALean_CORALean_Real_instContSetZonotopeVecReal(v_n_3_);
lean_dec(v_n_3_);
return v_res_4_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
