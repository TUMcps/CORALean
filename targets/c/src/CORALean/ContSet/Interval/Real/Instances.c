// Lean compiler output
// Module: CORALean.ContSet.Interval.Real.Instances
// Imports: public import Init public meta import Init public import CORALean.ContSet.Interval.Real.Theorems.API
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
lean_object* lp_CORALean_CORALean_Real_Interval_mtimes___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Real_Interval_plus___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Real_Interval_linComb___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instContSetIntervalVecReal(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instContSetIntervalVecReal___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instOuterContSetIntervalVecReal___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instOuterContSetIntervalVecReal___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_CORALean_CORALean_Real_instOuterContSetIntervalVecReal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_CORALean_CORALean_Real_instOuterContSetIntervalVecReal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_CORALean_CORALean_Real_instOuterContSetIntervalVecReal___closed__0 = (const lean_object*)&lp_CORALean_CORALean_Real_instOuterContSetIntervalVecReal___closed__0_value;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instOuterContSetIntervalVecReal(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instMtimesMatRealInterval___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instMtimesMatRealInterval___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_CORALean_CORALean_Real_instMtimesMatRealInterval___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_CORALean_CORALean_Real_instMtimesMatRealInterval___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_CORALean_CORALean_Real_instMtimesMatRealInterval___closed__0 = (const lean_object*)&lp_CORALean_CORALean_Real_instMtimesMatRealInterval___closed__0_value;
LEAN_EXPORT const lean_object* lp_CORALean_CORALean_Real_instMtimesMatRealInterval = (const lean_object*)&lp_CORALean_CORALean_Real_instMtimesMatRealInterval___closed__0_value;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instContSetIntervalVecReal(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instContSetIntervalVecReal___boxed(lean_object* v_n_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_CORALean_CORALean_Real_instContSetIntervalVecReal(v_n_3_);
lean_dec(v_n_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instOuterContSetIntervalVecReal___lam__0(lean_object* v_I_5_, lean_object* v_x_6_){
_start:
{
lean_inc_ref(v_I_5_);
return v_I_5_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instOuterContSetIntervalVecReal___lam__0___boxed(lean_object* v_I_7_, lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_CORALean_CORALean_Real_instOuterContSetIntervalVecReal___lam__0(v_I_7_, v_x_8_);
lean_dec(v_x_8_);
lean_dec_ref(v_I_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instOuterContSetIntervalVecReal(lean_object* v_n_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___f_12_ = ((lean_object*)(lp_CORALean_CORALean_Real_instOuterContSetIntervalVecReal___closed__0));
lean_inc(v_n_11_);
v___x_13_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_plus___boxed), 3, 1);
lean_closure_set(v___x_13_, 0, v_n_11_);
v___x_14_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Interval_linComb___boxed), 3, 1);
lean_closure_set(v___x_14_, 0, v_n_11_);
v___x_15_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_15_, 0, v___x_13_);
lean_ctor_set(v___x_15_, 1, v___x_14_);
lean_ctor_set(v___x_15_, 2, v___f_12_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instMtimesMatRealInterval___lam__0(lean_object* v_m_16_, lean_object* v_n_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_CORALean_CORALean_Real_Interval_mtimes___redArg(v_n_17_, v___y_18_, v___y_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instMtimesMatRealInterval___lam__0___boxed(lean_object* v_m_21_, lean_object* v_n_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_CORALean_CORALean_Real_instMtimesMatRealInterval___lam__0(v_m_21_, v_n_22_, v___y_23_, v___y_24_);
lean_dec(v_m_21_);
return v_res_25_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Interval_Real_Theorems_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Interval_Real_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Interval_Real_Theorems_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
