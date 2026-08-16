// Lean compiler output
// Module: CORALean.Arithmetic.Float.ContSet.InflatedContSet.API
// Imports: public import Init public meta import Init public import CORALean.Arithmetic.Float.ContSet.Interval.Theorems
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_InflatedContSet_instContSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_InflatedContSet_instContSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_InflatedContSet_instContSet(lean_object* v_F_1_, lean_object* v_S_2_, lean_object* v_N_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_n_6_, lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_InflatedContSet_instContSet___boxed(lean_object* v_F_10_, lean_object* v_S_11_, lean_object* v_N_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_n_15_, lean_object* v_inst_16_, lean_object* v_inst_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_CORALean_CORALean_Arithmetic_Float_InflatedContSet_instContSet(v_F_10_, v_S_11_, v_N_12_, v_inst_13_, v_inst_14_, v_n_15_, v_inst_16_, v_inst_17_);
lean_dec_ref(v_inst_17_);
lean_dec(v_n_15_);
lean_dec(v_inst_14_);
lean_dec_ref(v_inst_13_);
return v_res_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Interval_Theorems(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Arithmetic_Float_ContSet_InflatedContSet_API(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Arithmetic_Float_ContSet_Interval_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
