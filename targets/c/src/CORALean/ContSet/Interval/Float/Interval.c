// Lean compiler output
// Module: CORALean.ContSet.Interval.Float.Interval
// Imports: public import Init public meta import Init public import CORALean.Global.Float.SoundFloatArithmetic public import CORALean.ContSet.Interval.Real.API
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
lean_object* lp_CORALean_CORALean_Float_toRealVec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_nominal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_nominal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_nominal___redArg(lean_object* v_inst_1_, lean_object* v_n_2_, lean_object* v_inst_3_, lean_object* v_I_4_){
_start:
{
lean_object* v_inf_5_; lean_object* v_sup_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_15_; 
v_inf_5_ = lean_ctor_get(v_I_4_, 0);
v_sup_6_ = lean_ctor_get(v_I_4_, 1);
v_isSharedCheck_15_ = !lean_is_exclusive(v_I_4_);
if (v_isSharedCheck_15_ == 0)
{
v___x_8_ = v_I_4_;
v_isShared_9_ = v_isSharedCheck_15_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_sup_6_);
lean_inc(v_inf_5_);
lean_dec(v_I_4_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_15_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_13_; 
lean_inc(v_n_2_);
lean_inc(v_inst_3_);
lean_inc_ref(v_inst_1_);
v___x_10_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_toRealVec___boxed), 6, 5);
lean_closure_set(v___x_10_, 0, lean_box(0));
lean_closure_set(v___x_10_, 1, v_inst_1_);
lean_closure_set(v___x_10_, 2, v_inst_3_);
lean_closure_set(v___x_10_, 3, v_n_2_);
lean_closure_set(v___x_10_, 4, v_inf_5_);
v___x_11_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_toRealVec___boxed), 6, 5);
lean_closure_set(v___x_11_, 0, lean_box(0));
lean_closure_set(v___x_11_, 1, v_inst_1_);
lean_closure_set(v___x_11_, 2, v_inst_3_);
lean_closure_set(v___x_11_, 3, v_n_2_);
lean_closure_set(v___x_11_, 4, v_sup_6_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___x_11_);
lean_ctor_set(v___x_8_, 0, v___x_10_);
v___x_13_ = v___x_8_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v___x_10_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v___x_11_);
v___x_13_ = v_reuseFailAlloc_14_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_nominal(lean_object* v_00_U0001d54b_16_, lean_object* v_inst_17_, lean_object* v_n_18_, lean_object* v_inst_19_, lean_object* v_I_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_CORALean_CORALean_Float_Interval_nominal___redArg(v_inst_17_, v_n_18_, v_inst_19_, v_I_20_);
return v___x_21_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Global_Float_SoundFloatArithmetic(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Interval_Real_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Interval_Float_Interval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Global_Float_SoundFloatArithmetic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Interval_Real_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
