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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___redArg___lam__0(lean_object* v_I_u2081_1_, lean_object* v_I_u2082_2_, lean_object* v_entry_3_, lean_object* v_i_4_){
_start:
{
lean_object* v_inf_5_; lean_object* v_inf_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___f_9_; 
v_inf_5_ = lean_ctor_get(v_I_u2081_1_, 0);
lean_inc(v_inf_5_);
lean_dec_ref(v_I_u2081_1_);
v_inf_6_ = lean_ctor_get(v_I_u2082_2_, 0);
lean_inc(v_inf_6_);
lean_dec_ref(v_I_u2082_2_);
lean_inc(v_entry_3_);
lean_inc(v_i_4_);
v___x_7_ = lean_apply_2(v_entry_3_, v_inf_5_, v_i_4_);
v___x_8_ = lean_apply_2(v_entry_3_, v_inf_6_, v_i_4_);
v___f_9_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1934218611____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_9_, 0, v___x_7_);
lean_closure_set(v___f_9_, 1, v___x_8_);
return v___f_9_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___redArg___lam__1(lean_object* v_I_u2081_10_, lean_object* v_I_u2082_11_, lean_object* v_entry_12_, lean_object* v_i_13_){
_start:
{
lean_object* v_sup_14_; lean_object* v_sup_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___f_18_; 
v_sup_14_ = lean_ctor_get(v_I_u2081_10_, 1);
lean_inc(v_sup_14_);
lean_dec_ref(v_I_u2081_10_);
v_sup_15_ = lean_ctor_get(v_I_u2082_11_, 1);
lean_inc(v_sup_15_);
lean_dec_ref(v_I_u2082_11_);
lean_inc(v_entry_12_);
lean_inc(v_i_13_);
v___x_16_ = lean_apply_2(v_entry_12_, v_sup_14_, v_i_13_);
v___x_17_ = lean_apply_2(v_entry_12_, v_sup_15_, v_i_13_);
v___f_18_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_3793047190____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_18_, 0, v___x_16_);
lean_closure_set(v___f_18_, 1, v___x_17_);
return v___f_18_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___redArg(lean_object* v_inst_19_, lean_object* v_I_u2081_20_, lean_object* v_I_u2082_21_){
_start:
{
lean_object* v_entry_22_; lean_object* v_ofEntry_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_34_; 
v_entry_22_ = lean_ctor_get(v_inst_19_, 0);
v_ofEntry_23_ = lean_ctor_get(v_inst_19_, 1);
v_isSharedCheck_34_ = !lean_is_exclusive(v_inst_19_);
if (v_isSharedCheck_34_ == 0)
{
v___x_25_ = v_inst_19_;
v_isShared_26_ = v_isSharedCheck_34_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_ofEntry_23_);
lean_inc(v_entry_22_);
lean_dec(v_inst_19_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_34_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
lean_inc(v_entry_22_);
lean_inc_ref(v_I_u2082_21_);
lean_inc_ref(v_I_u2081_20_);
v___f_27_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_linComb___redArg___lam__0), 4, 3);
lean_closure_set(v___f_27_, 0, v_I_u2081_20_);
lean_closure_set(v___f_27_, 1, v_I_u2082_21_);
lean_closure_set(v___f_27_, 2, v_entry_22_);
v___f_28_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_linComb___redArg___lam__1), 4, 3);
lean_closure_set(v___f_28_, 0, v_I_u2081_20_);
lean_closure_set(v___f_28_, 1, v_I_u2082_21_);
lean_closure_set(v___f_28_, 2, v_entry_22_);
lean_inc(v_ofEntry_23_);
v___x_29_ = lean_apply_1(v_ofEntry_23_, v___f_27_);
v___x_30_ = lean_apply_1(v_ofEntry_23_, v___f_28_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v___x_30_);
lean_ctor_set(v___x_25_, 0, v___x_29_);
v___x_32_ = v___x_25_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b9_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_I_u2081_40_, lean_object* v_I_u2082_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_CORALean_CORALean_Real_Interval_linComb___redArg(v_inst_39_, v_I_u2081_40_, v_I_u2082_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_linComb___boxed(lean_object* v_00_u03b1_43_, lean_object* v_00_u03b9_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_I_u2081_48_, lean_object* v_I_u2082_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_CORALean_CORALean_Real_Interval_linComb(v_00_u03b1_43_, v_00_u03b9_44_, v_inst_45_, v_inst_46_, v_inst_47_, v_I_u2081_48_, v_I_u2082_49_);
lean_dec(v_inst_46_);
lean_dec_ref(v_inst_45_);
return v_res_50_;
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
