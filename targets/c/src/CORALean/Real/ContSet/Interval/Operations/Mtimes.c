// Lean compiler output
// Module: CORALean.Real.ContSet.Interval.Operations.Mtimes
// Imports: public import Init public meta import Init public import CORALean.Real.ContSet.Interval.Interval
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
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_3793047190____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_CORALean_Multiset_sum___at___00Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_CORALean_Multiset_sum___at___00Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0_spec__0___closed__0 = (const lean_object*)&lp_CORALean_Multiset_sum___at___00Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_CORALean_Multiset_sum___at___00Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* lp_CORALean_Multiset_sum___at___00Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0_spec__0(lean_object* v_s_14_){
_start:
{
lean_object* v___f_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___f_15_ = ((lean_object*)(lp_CORALean_Multiset_sum___at___00Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0_spec__0___closed__0));
v___x_16_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_17_ = l_List_foldrTR___redArg(v___f_15_, v___x_16_, v_s_14_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0___redArg(lean_object* v_s_18_, lean_object* v_f_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lp_mathlib_Multiset_map___redArg(v_f_19_, v_s_18_);
v___x_21_ = lp_CORALean_Multiset_sum___at___00Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0_spec__0(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__1(lean_object* v_I_22_, lean_object* v_M_23_, lean_object* v_n_24_, lean_object* v_i_25_){
_start:
{
lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___f_26_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__0), 4, 3);
lean_closure_set(v___f_26_, 0, v_I_22_);
lean_closure_set(v___f_26_, 1, v_M_23_);
lean_closure_set(v___f_26_, 2, v_i_25_);
v___x_27_ = l_List_finRange(v_n_24_);
v___x_28_ = lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0___redArg(v___x_27_, v___f_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__2(lean_object* v_I_29_, lean_object* v_M_30_, lean_object* v_i_31_, lean_object* v_k_32_){
_start:
{
lean_object* v_inf_33_; lean_object* v_sup_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___f_37_; lean_object* v___x_38_; lean_object* v___f_39_; lean_object* v___f_40_; 
v_inf_33_ = lean_ctor_get(v_I_29_, 0);
lean_inc(v_inf_33_);
v_sup_34_ = lean_ctor_get(v_I_29_, 1);
lean_inc(v_sup_34_);
lean_dec_ref(v_I_29_);
lean_inc_n(v_k_32_, 2);
v___x_35_ = lean_apply_2(v_M_30_, v_i_31_, v_k_32_);
v___x_36_ = lean_apply_1(v_inf_33_, v_k_32_);
lean_inc(v___x_35_);
v___f_37_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_37_, 0, v___x_35_);
lean_closure_set(v___f_37_, 1, v___x_36_);
v___x_38_ = lean_apply_1(v_sup_34_, v_k_32_);
v___f_39_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_39_, 0, v___x_35_);
lean_closure_set(v___f_39_, 1, v___x_38_);
v___f_40_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_40_, 0, v___f_37_);
lean_closure_set(v___f_40_, 1, v___f_39_);
return v___f_40_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__3(lean_object* v_I_41_, lean_object* v_M_42_, lean_object* v_n_43_, lean_object* v_i_44_){
_start:
{
lean_object* v___f_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___f_45_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__2), 4, 3);
lean_closure_set(v___f_45_, 0, v_I_41_);
lean_closure_set(v___f_45_, 1, v_M_42_);
lean_closure_set(v___f_45_, 2, v_i_44_);
v___x_46_ = l_List_finRange(v_n_43_);
v___x_47_ = lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0___redArg(v___x_46_, v___f_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg(lean_object* v_n_48_, lean_object* v_M_49_, lean_object* v_I_50_){
_start:
{
lean_object* v___f_51_; lean_object* v___f_52_; lean_object* v___x_53_; 
lean_inc(v_n_48_);
lean_inc(v_M_49_);
lean_inc_ref(v_I_50_);
v___f_51_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__1), 4, 3);
lean_closure_set(v___f_51_, 0, v_I_50_);
lean_closure_set(v___f_51_, 1, v_M_49_);
lean_closure_set(v___f_51_, 2, v_n_48_);
v___f_52_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_mtimes___redArg___lam__3), 4, 3);
lean_closure_set(v___f_52_, 0, v_I_50_);
lean_closure_set(v___f_52_, 1, v_M_49_);
lean_closure_set(v___f_52_, 2, v_n_48_);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v___f_52_);
lean_ctor_set(v___x_53_, 1, v___f_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes(lean_object* v_n_54_, lean_object* v_m_55_, lean_object* v_M_56_, lean_object* v_I_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_CORALean_CORALean_Real_Interval_mtimes___redArg(v_n_54_, v_M_56_, v_I_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___boxed(lean_object* v_n_59_, lean_object* v_m_60_, lean_object* v_M_61_, lean_object* v_I_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = lp_CORALean_CORALean_Real_Interval_mtimes(v_n_59_, v_m_60_, v_M_61_, v_I_62_);
lean_dec(v_m_60_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0(lean_object* v_00_u03b9_64_, lean_object* v_s_65_, lean_object* v_f_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0___redArg(v_s_65_, v_f_66_);
return v___x_67_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Interval_Interval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Real_ContSet_Interval_Operations_Mtimes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Interval_Interval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
