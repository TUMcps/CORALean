// Lean compiler output
// Module: CORALean.Float.ContSet.Interval.Operations.Symmetric
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_symmetric___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_symmetric___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_symmetric(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_symmetric___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_symmetric___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_r_2_, lean_object* v_i_3_){
_start:
{
lean_object* v_neg_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v_neg_4_ = lean_ctor_get(v_inst_1_, 1);
lean_inc(v_neg_4_);
lean_dec_ref(v_inst_1_);
v___x_5_ = lean_apply_1(v_r_2_, v_i_3_);
v___x_6_ = lean_apply_1(v_neg_4_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_symmetric___redArg(lean_object* v_inst_7_, lean_object* v_r_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; 
lean_inc(v_r_8_);
v___f_9_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Interval_symmetric___redArg___lam__0), 3, 2);
lean_closure_set(v___f_9_, 0, v_inst_7_);
lean_closure_set(v___f_9_, 1, v_r_8_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___f_9_);
lean_ctor_set(v___x_10_, 1, v_r_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_symmetric(lean_object* v_00_U0001d54b_11_, lean_object* v_inst_12_, lean_object* v_n_13_, lean_object* v_r_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_CORALean_CORALean_Float_Interval_symmetric___redArg(v_inst_12_, v_r_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_symmetric___boxed(lean_object* v_00_U0001d54b_16_, lean_object* v_inst_17_, lean_object* v_n_18_, lean_object* v_r_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_CORALean_CORALean_Float_Interval_symmetric(v_00_U0001d54b_16_, v_inst_17_, v_n_18_, v_r_19_);
lean_dec(v_n_18_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Interval_Interval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Float_ContSet_Interval_Operations_Symmetric(uint8_t builtin) {
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
