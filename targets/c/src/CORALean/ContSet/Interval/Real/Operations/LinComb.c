// Lean compiler output
// Module: CORALean.ContSet.Interval.Real.Operations.LinComb
// Imports: public import Init public meta import Init public import CORALean.ContSet.Interval.Real.Interval
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_3793047190____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___redArg___lam__0(lean_object* v_I_u2081_1_, lean_object* v_I_u2082_2_, lean_object* v_i_3_){
_start:
{
lean_object* v_inf_4_; lean_object* v_inf_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___f_8_; 
v_inf_4_ = lean_ctor_get(v_I_u2081_1_, 0);
lean_inc(v_inf_4_);
lean_dec_ref(v_I_u2081_1_);
v_inf_5_ = lean_ctor_get(v_I_u2082_2_, 0);
lean_inc(v_inf_5_);
lean_dec_ref(v_I_u2082_2_);
lean_inc(v_i_3_);
v___x_6_ = lean_apply_1(v_inf_4_, v_i_3_);
v___x_7_ = lean_apply_1(v_inf_5_, v_i_3_);
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_8_, 0, v___x_6_);
lean_closure_set(v___f_8_, 1, v___x_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___redArg___lam__1(lean_object* v_I_u2081_9_, lean_object* v_I_u2082_10_, lean_object* v_i_11_){
_start:
{
lean_object* v_sup_12_; lean_object* v_sup_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___f_16_; 
v_sup_12_ = lean_ctor_get(v_I_u2081_9_, 1);
lean_inc(v_sup_12_);
lean_dec_ref(v_I_u2081_9_);
v_sup_13_ = lean_ctor_get(v_I_u2082_10_, 1);
lean_inc(v_sup_13_);
lean_dec_ref(v_I_u2082_10_);
lean_inc(v_i_11_);
v___x_14_ = lean_apply_1(v_sup_12_, v_i_11_);
v___x_15_ = lean_apply_1(v_sup_13_, v_i_11_);
v___f_16_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_3793047190____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_16_, 0, v___x_14_);
lean_closure_set(v___f_16_, 1, v___x_15_);
return v___f_16_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___redArg(lean_object* v_I_u2081_17_, lean_object* v_I_u2082_18_){
_start:
{
lean_object* v___f_19_; lean_object* v___f_20_; lean_object* v___x_21_; 
lean_inc_ref(v_I_u2082_18_);
lean_inc_ref(v_I_u2081_17_);
v___f_19_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_linComb___redArg___lam__0), 3, 2);
lean_closure_set(v___f_19_, 0, v_I_u2081_17_);
lean_closure_set(v___f_19_, 1, v_I_u2082_18_);
v___f_20_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_linComb___redArg___lam__1), 3, 2);
lean_closure_set(v___f_20_, 0, v_I_u2081_17_);
lean_closure_set(v___f_20_, 1, v_I_u2082_18_);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v___f_19_);
lean_ctor_set(v___x_21_, 1, v___f_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb(lean_object* v_n_22_, lean_object* v_I_u2081_23_, lean_object* v_I_u2082_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_CORALean_CORALean_Real_Interval_linComb___redArg(v_I_u2081_23_, v_I_u2082_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___boxed(lean_object* v_n_26_, lean_object* v_I_u2081_27_, lean_object* v_I_u2082_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_CORALean_CORALean_Real_Interval_linComb(v_n_26_, v_I_u2081_27_, v_I_u2082_28_);
lean_dec(v_n_26_);
return v_res_29_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Interval_Real_Interval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Interval_Real_Operations_LinComb(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Interval_Real_Interval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
