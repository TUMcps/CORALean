// Lean compiler output
// Module: CORALean.Real.ContSet.Interval.Operations.Plus
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus___redArg___lam__0(lean_object* v_sup_1_, lean_object* v_sup_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___f_6_; 
lean_inc(v___y_3_);
v___x_4_ = lean_apply_1(v_sup_1_, v___y_3_);
v___x_5_ = lean_apply_1(v_sup_2_, v___y_3_);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_6_, 0, v___x_4_);
lean_closure_set(v___f_6_, 1, v___x_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus___redArg___lam__1(lean_object* v_inf_7_, lean_object* v_inf_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___f_12_; 
lean_inc(v___y_9_);
v___x_10_ = lean_apply_1(v_inf_7_, v___y_9_);
v___x_11_ = lean_apply_1(v_inf_8_, v___y_9_);
v___f_12_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_12_, 0, v___x_10_);
lean_closure_set(v___f_12_, 1, v___x_11_);
return v___f_12_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus___redArg(lean_object* v_I_u2081_13_, lean_object* v_I_u2082_14_){
_start:
{
lean_object* v_inf_15_; lean_object* v_sup_16_; lean_object* v_inf_17_; lean_object* v_sup_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_27_; 
v_inf_15_ = lean_ctor_get(v_I_u2081_13_, 0);
lean_inc(v_inf_15_);
v_sup_16_ = lean_ctor_get(v_I_u2081_13_, 1);
lean_inc(v_sup_16_);
lean_dec_ref(v_I_u2081_13_);
v_inf_17_ = lean_ctor_get(v_I_u2082_14_, 0);
v_sup_18_ = lean_ctor_get(v_I_u2082_14_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v_I_u2082_14_);
if (v_isSharedCheck_27_ == 0)
{
v___x_20_ = v_I_u2082_14_;
v_isShared_21_ = v_isSharedCheck_27_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_sup_18_);
lean_inc(v_inf_17_);
lean_dec(v_I_u2082_14_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_27_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_25_; 
v___f_22_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_plus___redArg___lam__0), 3, 2);
lean_closure_set(v___f_22_, 0, v_sup_16_);
lean_closure_set(v___f_22_, 1, v_sup_18_);
v___f_23_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_plus___redArg___lam__1), 3, 2);
lean_closure_set(v___f_23_, 0, v_inf_15_);
lean_closure_set(v___f_23_, 1, v_inf_17_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 1, v___f_22_);
lean_ctor_set(v___x_20_, 0, v___f_23_);
v___x_25_ = v___x_20_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___f_23_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v___f_22_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus(lean_object* v_n_28_, lean_object* v_I_u2081_29_, lean_object* v_I_u2082_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_CORALean_CORALean_Real_Interval_plus___redArg(v_I_u2081_29_, v_I_u2082_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus___boxed(lean_object* v_n_32_, lean_object* v_I_u2081_33_, lean_object* v_I_u2082_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_CORALean_CORALean_Real_Interval_plus(v_n_32_, v_I_u2081_33_, v_I_u2082_34_);
lean_dec(v_n_32_);
return v_res_35_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Interval_Interval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Real_ContSet_Interval_Operations_Plus(uint8_t builtin) {
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
