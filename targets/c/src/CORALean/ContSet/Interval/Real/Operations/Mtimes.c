// Lean compiler output
// Module: CORALean.ContSet.Interval.Real.Operations.Mtimes
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_CORALean_Finset_sum___at___00dotProduct___at___00CORALean_matMulLeft_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_3793047190____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__0(lean_object* v_I_1_, lean_object* v_M_2_, lean_object* v_i_3_, lean_object* v_k_4_){
_start:
{
lean_object* v_inf_5_; lean_object* v_sup_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___f_11_; lean_object* v___f_12_; 
v_inf_5_ = lean_ctor_get(v_I_1_, 0);
lean_inc(v_inf_5_);
v_sup_6_ = lean_ctor_get(v_I_1_, 1);
lean_inc(v_sup_6_);
lean_dec_ref(v_I_1_);
lean_inc_n(v_k_4_, 2);
v___x_7_ = lean_apply_2(v_M_2_, v_i_3_, v_k_4_);
v___x_8_ = lean_apply_1(v_inf_5_, v_k_4_);
lean_inc(v___x_7_);
v___f_9_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_9_, 0, v___x_7_);
lean_closure_set(v___f_9_, 1, v___x_8_);
v___x_10_ = lean_apply_1(v_sup_6_, v_k_4_);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_11_, 0, v___x_7_);
lean_closure_set(v___f_11_, 1, v___x_10_);
v___f_12_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_3793047190____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_12_, 0, v___f_9_);
lean_closure_set(v___f_12_, 1, v___f_11_);
return v___f_12_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__1(lean_object* v_I_13_, lean_object* v_M_14_, lean_object* v_n_15_, lean_object* v_i_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___f_17_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__0), 4, 3);
lean_closure_set(v___f_17_, 0, v_I_13_);
lean_closure_set(v___f_17_, 1, v_M_14_);
lean_closure_set(v___f_17_, 2, v_i_16_);
v___x_18_ = l_List_finRange(v_n_15_);
v___x_19_ = lp_CORALean_Finset_sum___at___00dotProduct___at___00CORALean_matMulLeft_spec__0_spec__0___redArg(v___x_18_, v___f_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__2(lean_object* v_I_20_, lean_object* v_M_21_, lean_object* v_i_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_inf_24_; lean_object* v_sup_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___f_30_; lean_object* v___f_31_; 
v_inf_24_ = lean_ctor_get(v_I_20_, 0);
lean_inc(v_inf_24_);
v_sup_25_ = lean_ctor_get(v_I_20_, 1);
lean_inc(v_sup_25_);
lean_dec_ref(v_I_20_);
lean_inc_n(v_k_23_, 2);
v___x_26_ = lean_apply_2(v_M_21_, v_i_22_, v_k_23_);
v___x_27_ = lean_apply_1(v_inf_24_, v_k_23_);
lean_inc(v___x_26_);
v___f_28_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_28_, 0, v___x_26_);
lean_closure_set(v___f_28_, 1, v___x_27_);
v___x_29_ = lean_apply_1(v_sup_25_, v_k_23_);
v___f_30_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_30_, 0, v___x_26_);
lean_closure_set(v___f_30_, 1, v___x_29_);
v___f_31_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_31_, 0, v___f_28_);
lean_closure_set(v___f_31_, 1, v___f_30_);
return v___f_31_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__3(lean_object* v_I_32_, lean_object* v_M_33_, lean_object* v_n_34_, lean_object* v_i_35_){
_start:
{
lean_object* v___f_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___f_36_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__2), 4, 3);
lean_closure_set(v___f_36_, 0, v_I_32_);
lean_closure_set(v___f_36_, 1, v_M_33_);
lean_closure_set(v___f_36_, 2, v_i_35_);
v___x_37_ = l_List_finRange(v_n_34_);
v___x_38_ = lp_CORALean_Finset_sum___at___00dotProduct___at___00CORALean_matMulLeft_spec__0_spec__0___redArg(v___x_37_, v___f_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg(lean_object* v_n_39_, lean_object* v_M_40_, lean_object* v_I_41_){
_start:
{
lean_object* v___f_42_; lean_object* v___f_43_; lean_object* v___x_44_; 
lean_inc(v_n_39_);
lean_inc(v_M_40_);
lean_inc_ref(v_I_41_);
v___f_42_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__1), 4, 3);
lean_closure_set(v___f_42_, 0, v_I_41_);
lean_closure_set(v___f_42_, 1, v_M_40_);
lean_closure_set(v___f_42_, 2, v_n_39_);
v___f_43_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__3), 4, 3);
lean_closure_set(v___f_43_, 0, v_I_41_);
lean_closure_set(v___f_43_, 1, v_M_40_);
lean_closure_set(v___f_43_, 2, v_n_39_);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___f_43_);
lean_ctor_set(v___x_44_, 1, v___f_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes(lean_object* v_n_45_, lean_object* v_m_46_, lean_object* v_M_47_, lean_object* v_I_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lp_CORALean_CORALean_Real_Interval_mtimes___redArg(v_n_45_, v_M_47_, v_I_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___boxed(lean_object* v_n_50_, lean_object* v_m_51_, lean_object* v_M_52_, lean_object* v_I_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_CORALean_CORALean_Real_Interval_mtimes(v_n_50_, v_m_51_, v_M_52_, v_I_53_);
lean_dec(v_m_51_);
return v_res_54_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Interval_Real_Interval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Interval_Real_Operations_Mtimes(uint8_t builtin) {
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
