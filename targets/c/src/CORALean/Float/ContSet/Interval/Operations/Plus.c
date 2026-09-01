// Lean compiler output
// Module: CORALean.Float.ContSet.Interval.Operations.Plus
// Imports: public import Init public meta import Init public import CORALean.Float.ContSet.Interval.Interval
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_plus___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_plus___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_plus___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_plus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_plus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_plus___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_I_u2081_2_, lean_object* v_I_u2082_3_, lean_object* v_i_4_){
_start:
{
lean_object* v_addDown_5_; lean_object* v_inf_6_; lean_object* v_inf_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_addDown_5_ = lean_ctor_get(v_inst_1_, 3);
lean_inc(v_addDown_5_);
lean_dec_ref(v_inst_1_);
v_inf_6_ = lean_ctor_get(v_I_u2081_2_, 0);
lean_inc(v_inf_6_);
lean_dec_ref(v_I_u2081_2_);
v_inf_7_ = lean_ctor_get(v_I_u2082_3_, 0);
lean_inc(v_inf_7_);
lean_dec_ref(v_I_u2082_3_);
lean_inc(v_i_4_);
v___x_8_ = lean_apply_1(v_inf_6_, v_i_4_);
v___x_9_ = lean_apply_1(v_inf_7_, v_i_4_);
v___x_10_ = lean_apply_2(v_addDown_5_, v___x_8_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_plus___redArg___lam__1(lean_object* v_inst_11_, lean_object* v_I_u2081_12_, lean_object* v_I_u2082_13_, lean_object* v_i_14_){
_start:
{
lean_object* v_addUp_15_; lean_object* v_sup_16_; lean_object* v_sup_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_addUp_15_ = lean_ctor_get(v_inst_11_, 2);
lean_inc(v_addUp_15_);
lean_dec_ref(v_inst_11_);
v_sup_16_ = lean_ctor_get(v_I_u2081_12_, 1);
lean_inc(v_sup_16_);
lean_dec_ref(v_I_u2081_12_);
v_sup_17_ = lean_ctor_get(v_I_u2082_13_, 1);
lean_inc(v_sup_17_);
lean_dec_ref(v_I_u2082_13_);
lean_inc(v_i_14_);
v___x_18_ = lean_apply_1(v_sup_16_, v_i_14_);
v___x_19_ = lean_apply_1(v_sup_17_, v_i_14_);
v___x_20_ = lean_apply_2(v_addUp_15_, v___x_18_, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_plus___redArg(lean_object* v_inst_21_, lean_object* v_I_u2081_22_, lean_object* v_I_u2082_23_){
_start:
{
lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___x_26_; 
lean_inc_ref(v_I_u2082_23_);
lean_inc_ref(v_I_u2081_22_);
lean_inc_ref(v_inst_21_);
v___f_24_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Interval_plus___redArg___lam__0), 4, 3);
lean_closure_set(v___f_24_, 0, v_inst_21_);
lean_closure_set(v___f_24_, 1, v_I_u2081_22_);
lean_closure_set(v___f_24_, 2, v_I_u2082_23_);
v___f_25_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Interval_plus___redArg___lam__1), 4, 3);
lean_closure_set(v___f_25_, 0, v_inst_21_);
lean_closure_set(v___f_25_, 1, v_I_u2081_22_);
lean_closure_set(v___f_25_, 2, v_I_u2082_23_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___f_24_);
lean_ctor_set(v___x_26_, 1, v___f_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_plus(lean_object* v_00_U0001d54b_27_, lean_object* v_inst_28_, lean_object* v_n_29_, lean_object* v_I_u2081_30_, lean_object* v_I_u2082_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_CORALean_CORALean_Float_Interval_plus___redArg(v_inst_28_, v_I_u2081_30_, v_I_u2082_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_plus___boxed(lean_object* v_00_U0001d54b_33_, lean_object* v_inst_34_, lean_object* v_n_35_, lean_object* v_I_u2081_36_, lean_object* v_I_u2082_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_CORALean_CORALean_Float_Interval_plus(v_00_U0001d54b_33_, v_inst_34_, v_n_35_, v_I_u2081_36_, v_I_u2082_37_);
lean_dec(v_n_35_);
return v_res_38_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Interval_Interval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Float_ContSet_Interval_Operations_Plus(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Interval_Interval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
