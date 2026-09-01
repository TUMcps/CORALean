// Lean compiler output
// Module: CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterSplitZonotope
// Imports: public import Init public meta import Init public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuterSplit public import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter public import CORALean.ContSet.Zonotope.Real.API
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_aux__centered___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_aux__centered___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_CORALean_CORALean_Real_aux__centered___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_CORALean_CORALean_Real_aux__centered___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_CORALean_CORALean_Real_aux__centered___redArg___closed__0 = (const lean_object*)&lp_CORALean_CORALean_Real_aux__centered___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_aux__centered___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_aux__centered(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_aux__centered___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_aux__centered___redArg___lam__0(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_aux__centered___redArg___lam__0___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_CORALean_CORALean_Real_aux__centered___redArg___lam__0(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_aux__centered___redArg(lean_object* v_Z_6_){
_start:
{
lean_object* v_h_7_; lean_object* v_G_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_16_; 
v_h_7_ = lean_ctor_get(v_Z_6_, 0);
v_G_8_ = lean_ctor_get(v_Z_6_, 2);
v_isSharedCheck_16_ = !lean_is_exclusive(v_Z_6_);
if (v_isSharedCheck_16_ == 0)
{
lean_object* v_unused_17_; 
v_unused_17_ = lean_ctor_get(v_Z_6_, 1);
lean_dec(v_unused_17_);
v___x_10_ = v_Z_6_;
v_isShared_11_ = v_isSharedCheck_16_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_G_8_);
lean_inc(v_h_7_);
lean_dec(v_Z_6_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_16_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___f_12_; lean_object* v___x_14_; 
v___f_12_ = ((lean_object*)(lp_CORALean_CORALean_Real_aux__centered___redArg___closed__0));
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v___f_12_);
v___x_14_ = v___x_10_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_h_7_);
lean_ctor_set(v_reuseFailAlloc_15_, 1, v___f_12_);
lean_ctor_set(v_reuseFailAlloc_15_, 2, v_G_8_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_aux__centered(lean_object* v_n_18_, lean_object* v_Z_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_CORALean_CORALean_Real_aux__centered___redArg(v_Z_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_aux__centered___boxed(lean_object* v_n_21_, lean_object* v_Z_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_CORALean_CORALean_Real_aux__centered(v_n_21_, v_Z_22_);
lean_dec(v_n_21_);
return v_res_23_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_InputSolutionTimeIntervalOuterSplit(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_TrajectoryTimeIntervalOuter(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_TimeIntervalOuterSplitZonotope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_InputSolutionTimeIntervalOuterSplit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSys_Theorems_TrajectoryTimeIntervalOuter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
