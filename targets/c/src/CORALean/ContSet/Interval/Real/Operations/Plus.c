// Lean compiler output
// Module: CORALean.ContSet.Interval.Real.Operations.Plus
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus___redArg(lean_object* v_inst_1_, lean_object* v_I_u2081_2_, lean_object* v_I_u2082_3_){
_start:
{
lean_object* v_toAddMonoid_4_; lean_object* v_toAddSemigroup_5_; lean_object* v_inf_6_; lean_object* v_sup_7_; lean_object* v_inf_8_; lean_object* v_sup_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_18_; 
v_toAddMonoid_4_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toAddMonoid_4_);
lean_dec_ref(v_inst_1_);
v_toAddSemigroup_5_ = lean_ctor_get(v_toAddMonoid_4_, 0);
lean_inc(v_toAddSemigroup_5_);
lean_dec_ref(v_toAddMonoid_4_);
v_inf_6_ = lean_ctor_get(v_I_u2081_2_, 0);
lean_inc(v_inf_6_);
v_sup_7_ = lean_ctor_get(v_I_u2081_2_, 1);
lean_inc(v_sup_7_);
lean_dec_ref(v_I_u2081_2_);
v_inf_8_ = lean_ctor_get(v_I_u2082_3_, 0);
v_sup_9_ = lean_ctor_get(v_I_u2082_3_, 1);
v_isSharedCheck_18_ = !lean_is_exclusive(v_I_u2082_3_);
if (v_isSharedCheck_18_ == 0)
{
v___x_11_ = v_I_u2082_3_;
v_isShared_12_ = v_isSharedCheck_18_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_sup_9_);
lean_inc(v_inf_8_);
lean_dec(v_I_u2082_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_18_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_16_; 
lean_inc(v_toAddSemigroup_5_);
v___x_13_ = lean_apply_2(v_toAddSemigroup_5_, v_inf_6_, v_inf_8_);
v___x_14_ = lean_apply_2(v_toAddSemigroup_5_, v_sup_7_, v_sup_9_);
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 1, v___x_14_);
lean_ctor_set(v___x_11_, 0, v___x_13_);
v___x_16_ = v___x_11_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_13_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v___x_14_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Interval_plus(lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_I_u2081_21_, lean_object* v_I_u2082_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_CORALean_CORALean_Real_Interval_plus___redArg(v_inst_20_, v_I_u2081_21_, v_I_u2082_22_);
return v___x_23_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Interval_Real_Interval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Interval_Real_Operations_Plus(uint8_t builtin) {
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
