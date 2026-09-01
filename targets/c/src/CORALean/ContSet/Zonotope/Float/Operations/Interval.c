// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Float.Operations.Interval
// Imports: public import Init public meta import Init public import CORALean.ContSet.Zonotope.Float.Zonotope
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
lean_object* lp_CORALean_CORALean_Float_radius___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_subDown___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_interval___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_interval___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_interval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_interval(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_interval___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_interval___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_Z_2_, lean_object* v_i_3_){
_start:
{
lean_object* v_addDown_4_; lean_object* v_h_5_; lean_object* v_c_6_; lean_object* v_G_7_; lean_object* v_E_8_; lean_object* v___x_9_; lean_object* v_inf_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_addDown_4_ = lean_ctor_get(v_inst_1_, 3);
lean_inc(v_addDown_4_);
v_h_5_ = lean_ctor_get(v_Z_2_, 0);
lean_inc(v_h_5_);
v_c_6_ = lean_ctor_get(v_Z_2_, 1);
lean_inc(v_c_6_);
v_G_7_ = lean_ctor_get(v_Z_2_, 2);
lean_inc(v_G_7_);
v_E_8_ = lean_ctor_get(v_Z_2_, 3);
lean_inc_ref(v_E_8_);
lean_dec_ref(v_Z_2_);
lean_inc_n(v_i_3_, 2);
v___x_9_ = lean_apply_1(v_c_6_, v_i_3_);
v_inf_10_ = lean_ctor_get(v_E_8_, 0);
lean_inc(v_inf_10_);
lean_dec_ref(v_E_8_);
lean_inc_ref(v_inst_1_);
v___x_11_ = lp_CORALean_CORALean_Float_radius___redArg(v_inst_1_, v_h_5_, v_G_7_, v_i_3_);
lean_dec(v_h_5_);
v___x_12_ = lp_CORALean_CORALean_Float_subDown___redArg(v_inst_1_, v___x_9_, v___x_11_);
v___x_13_ = lean_apply_1(v_inf_10_, v_i_3_);
v___x_14_ = lean_apply_2(v_addDown_4_, v___x_12_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_interval___redArg___lam__1(lean_object* v_inst_15_, lean_object* v_Z_16_, lean_object* v_i_17_){
_start:
{
lean_object* v_E_18_; lean_object* v_addUp_19_; lean_object* v_h_20_; lean_object* v_c_21_; lean_object* v_G_22_; lean_object* v_sup_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v_E_18_ = lean_ctor_get(v_Z_16_, 3);
lean_inc_ref(v_E_18_);
v_addUp_19_ = lean_ctor_get(v_inst_15_, 2);
lean_inc_n(v_addUp_19_, 2);
v_h_20_ = lean_ctor_get(v_Z_16_, 0);
lean_inc(v_h_20_);
v_c_21_ = lean_ctor_get(v_Z_16_, 1);
lean_inc(v_c_21_);
v_G_22_ = lean_ctor_get(v_Z_16_, 2);
lean_inc(v_G_22_);
lean_dec_ref(v_Z_16_);
v_sup_23_ = lean_ctor_get(v_E_18_, 1);
lean_inc(v_sup_23_);
lean_dec_ref(v_E_18_);
lean_inc_n(v_i_17_, 2);
v___x_24_ = lean_apply_1(v_c_21_, v_i_17_);
v___x_25_ = lp_CORALean_CORALean_Float_radius___redArg(v_inst_15_, v_h_20_, v_G_22_, v_i_17_);
lean_dec(v_h_20_);
v___x_26_ = lean_apply_2(v_addUp_19_, v___x_24_, v___x_25_);
v___x_27_ = lean_apply_1(v_sup_23_, v_i_17_);
v___x_28_ = lean_apply_2(v_addUp_19_, v___x_26_, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_interval___redArg(lean_object* v_inst_29_, lean_object* v_Z_30_){
_start:
{
lean_object* v___f_31_; lean_object* v___f_32_; lean_object* v___x_33_; 
lean_inc_ref(v_Z_30_);
lean_inc_ref(v_inst_29_);
v___f_31_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_interval___redArg___lam__0), 3, 2);
lean_closure_set(v___f_31_, 0, v_inst_29_);
lean_closure_set(v___f_31_, 1, v_Z_30_);
v___f_32_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_interval___redArg___lam__1), 3, 2);
lean_closure_set(v___f_32_, 0, v_inst_29_);
lean_closure_set(v___f_32_, 1, v_Z_30_);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v___f_31_);
lean_ctor_set(v___x_33_, 1, v___f_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_interval(lean_object* v_00_U0001d54b_34_, lean_object* v_inst_35_, lean_object* v_n_36_, lean_object* v_Z_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_CORALean_CORALean_Float_Zonotope_interval___redArg(v_inst_35_, v_Z_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_interval___boxed(lean_object* v_00_U0001d54b_39_, lean_object* v_inst_40_, lean_object* v_n_41_, lean_object* v_Z_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_CORALean_CORALean_Float_Zonotope_interval(v_00_U0001d54b_39_, v_inst_40_, v_n_41_, v_Z_42_);
lean_dec(v_n_41_);
return v_res_43_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Zonotope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Operations_Interval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Float_Zonotope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
