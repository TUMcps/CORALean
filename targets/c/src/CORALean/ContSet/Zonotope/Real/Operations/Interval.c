// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Real.Operations.Interval
// Imports: public import Init public meta import Init public import CORALean.ContSet.Zonotope.Real.Zonotope
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
lean_object* lp_mathlib_abs___at___00EReal_abs_spec__0(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_interval___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_interval___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_interval___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_interval___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_interval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_interval___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_interval___redArg___lam__0(lean_object* v_G_1_, lean_object* v_i_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_2(v_G_1_, v_i_2_, v_j_3_);
v___x_5_ = lp_mathlib_abs___at___00EReal_abs_spec__0(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_interval___redArg___lam__1(lean_object* v_Z_6_, lean_object* v_i_7_){
_start:
{
lean_object* v_h_8_; lean_object* v_c_9_; lean_object* v_G_10_; lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___f_15_; 
v_h_8_ = lean_ctor_get(v_Z_6_, 0);
lean_inc(v_h_8_);
v_c_9_ = lean_ctor_get(v_Z_6_, 1);
lean_inc(v_c_9_);
v_G_10_ = lean_ctor_get(v_Z_6_, 2);
lean_inc(v_G_10_);
lean_dec_ref(v_Z_6_);
lean_inc(v_i_7_);
v___f_11_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_interval___redArg___lam__0), 3, 2);
lean_closure_set(v___f_11_, 0, v_G_10_);
lean_closure_set(v___f_11_, 1, v_i_7_);
v___x_12_ = lean_apply_1(v_c_9_, v_i_7_);
v___x_13_ = l_List_finRange(v_h_8_);
v___x_14_ = lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0___redArg(v___x_13_, v___f_11_);
v___f_15_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_15_, 0, v___x_12_);
lean_closure_set(v___f_15_, 1, v___x_14_);
return v___f_15_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_interval___redArg___lam__3(lean_object* v_Z_16_, lean_object* v_i_17_){
_start:
{
lean_object* v_h_18_; lean_object* v_c_19_; lean_object* v_G_20_; lean_object* v___f_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___f_25_; lean_object* v___f_26_; 
v_h_18_ = lean_ctor_get(v_Z_16_, 0);
lean_inc(v_h_18_);
v_c_19_ = lean_ctor_get(v_Z_16_, 1);
lean_inc(v_c_19_);
v_G_20_ = lean_ctor_get(v_Z_16_, 2);
lean_inc(v_G_20_);
lean_dec_ref(v_Z_16_);
lean_inc(v_i_17_);
v___f_21_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_interval___redArg___lam__0), 3, 2);
lean_closure_set(v___f_21_, 0, v_G_20_);
lean_closure_set(v___f_21_, 1, v_i_17_);
v___x_22_ = lean_apply_1(v_c_19_, v_i_17_);
v___x_23_ = l_List_finRange(v_h_18_);
v___x_24_ = lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0___redArg(v___x_23_, v___f_21_);
v___f_25_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_25_, 0, v___x_24_);
v___f_26_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_26_, 0, v___x_22_);
lean_closure_set(v___f_26_, 1, v___f_25_);
return v___f_26_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_interval___redArg(lean_object* v_Z_27_){
_start:
{
lean_object* v___f_28_; lean_object* v___f_29_; lean_object* v___x_30_; 
lean_inc_ref(v_Z_27_);
v___f_28_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_interval___redArg___lam__1), 2, 1);
lean_closure_set(v___f_28_, 0, v_Z_27_);
v___f_29_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_interval___redArg___lam__3), 2, 1);
lean_closure_set(v___f_29_, 0, v_Z_27_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___f_29_);
lean_ctor_set(v___x_30_, 1, v___f_28_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_interval(lean_object* v_n_31_, lean_object* v_Z_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_CORALean_CORALean_Real_Zonotope_interval___redArg(v_Z_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_interval___boxed(lean_object* v_n_34_, lean_object* v_Z_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_CORALean_CORALean_Real_Zonotope_interval(v_n_34_, v_Z_35_);
lean_dec(v_n_34_);
return v_res_36_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Zonotope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_Interval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Zonotope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
