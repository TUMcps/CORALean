// Lean compiler output
// Module: CORALean.Float.ContSet.Interval.Operations.Residual
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
lean_object* lp_CORALean_CORALean_Float_subDown___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_subUp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_residual___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_residual___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_residual___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_residual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_residual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_residual___redArg___lam__0(lean_object* v_lo_1_, lean_object* v_stored_2_, lean_object* v_inst_3_, lean_object* v_i_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
lean_inc(v_i_4_);
v___x_5_ = lean_apply_1(v_lo_1_, v_i_4_);
v___x_6_ = lean_apply_1(v_stored_2_, v_i_4_);
v___x_7_ = lp_CORALean_CORALean_Float_subDown___redArg(v_inst_3_, v___x_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_residual___redArg___lam__1(lean_object* v_hi_8_, lean_object* v_stored_9_, lean_object* v_inst_10_, lean_object* v_i_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
lean_inc(v_i_11_);
v___x_12_ = lean_apply_1(v_hi_8_, v_i_11_);
v___x_13_ = lean_apply_1(v_stored_9_, v_i_11_);
v___x_14_ = lp_CORALean_CORALean_Float_subUp___redArg(v_inst_10_, v___x_12_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_residual___redArg(lean_object* v_inst_15_, lean_object* v_lo_16_, lean_object* v_hi_17_, lean_object* v_stored_18_){
_start:
{
lean_object* v___f_19_; lean_object* v___f_20_; lean_object* v___x_21_; 
lean_inc_ref(v_inst_15_);
lean_inc(v_stored_18_);
v___f_19_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Interval_residual___redArg___lam__0), 4, 3);
lean_closure_set(v___f_19_, 0, v_lo_16_);
lean_closure_set(v___f_19_, 1, v_stored_18_);
lean_closure_set(v___f_19_, 2, v_inst_15_);
v___f_20_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Interval_residual___redArg___lam__1), 4, 3);
lean_closure_set(v___f_20_, 0, v_hi_17_);
lean_closure_set(v___f_20_, 1, v_stored_18_);
lean_closure_set(v___f_20_, 2, v_inst_15_);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v___f_19_);
lean_ctor_set(v___x_21_, 1, v___f_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_residual(lean_object* v_00_U0001d54b_22_, lean_object* v_inst_23_, lean_object* v_n_24_, lean_object* v_lo_25_, lean_object* v_hi_26_, lean_object* v_stored_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_CORALean_CORALean_Float_Interval_residual___redArg(v_inst_23_, v_lo_25_, v_hi_26_, v_stored_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_residual___boxed(lean_object* v_00_U0001d54b_29_, lean_object* v_inst_30_, lean_object* v_n_31_, lean_object* v_lo_32_, lean_object* v_hi_33_, lean_object* v_stored_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_CORALean_CORALean_Float_Interval_residual(v_00_U0001d54b_29_, v_inst_30_, v_n_31_, v_lo_32_, v_hi_33_, v_stored_34_);
lean_dec(v_n_31_);
return v_res_35_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Interval_Interval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Float_ContSet_Interval_Operations_Residual(uint8_t builtin) {
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
