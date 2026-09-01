// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
// Imports: public import Init public meta import Init public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes public import CORALean.MatSet.API
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_absBound___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_absBound___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_absBound(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_absBound___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_absBound___redArg___lam__0(lean_object* v_G_1_, lean_object* v_j_2_, lean_object* v_l_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_2(v_G_1_, v_l_3_, v_j_2_);
v___x_5_ = lp_mathlib_abs___at___00EReal_abs_spec__0(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_absBound___redArg(lean_object* v_Z_6_, lean_object* v_j_7_){
_start:
{
lean_object* v_h_8_; lean_object* v_c_9_; lean_object* v_G_10_; lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___f_16_; 
v_h_8_ = lean_ctor_get(v_Z_6_, 0);
lean_inc(v_h_8_);
v_c_9_ = lean_ctor_get(v_Z_6_, 1);
lean_inc(v_c_9_);
v_G_10_ = lean_ctor_get(v_Z_6_, 2);
lean_inc(v_G_10_);
lean_dec_ref(v_Z_6_);
lean_inc(v_j_7_);
v___f_11_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_absBound___redArg___lam__0), 3, 2);
lean_closure_set(v___f_11_, 0, v_G_10_);
lean_closure_set(v___f_11_, 1, v_j_7_);
v___x_12_ = lean_apply_1(v_c_9_, v_j_7_);
v___x_13_ = lp_mathlib_abs___at___00EReal_abs_spec__0(v___x_12_);
v___x_14_ = l_List_finRange(v_h_8_);
v___x_15_ = lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0___redArg(v___x_14_, v___f_11_);
v___f_16_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_16_, 0, v___x_13_);
lean_closure_set(v___f_16_, 1, v___x_15_);
return v___f_16_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_absBound(lean_object* v_n_17_, lean_object* v_Z_18_, lean_object* v_j_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_CORALean_CORALean_Real_Zonotope_absBound___redArg(v_Z_18_, v_j_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_absBound___boxed(lean_object* v_n_21_, lean_object* v_Z_22_, lean_object* v_j_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_CORALean_CORALean_Real_Zonotope_absBound(v_n_21_, v_Z_22_, v_j_23_);
lean_dec(v_n_21_);
return v_res_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_Mtimes(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_MatSet_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_MtimesIntervalMat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_Mtimes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_MatSet_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
