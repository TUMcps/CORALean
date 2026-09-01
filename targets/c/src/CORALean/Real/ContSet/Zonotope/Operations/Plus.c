// Lean compiler output
// Module: CORALean.Real.ContSet.Zonotope.Operations.Plus
// Imports: public import Init public meta import Init public import CORALean.Real.ContSet.Zonotope.Zonotope
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
lean_object* l_Fin_addCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus___redArg___lam__0(lean_object* v_G_1_, lean_object* v_G_2_, lean_object* v_h_3_, lean_object* v_i_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
lean_inc(v_i_4_);
v___x_6_ = lean_apply_1(v_G_1_, v_i_4_);
v___x_7_ = lean_apply_1(v_G_2_, v_i_4_);
v___x_8_ = l_Fin_addCases___redArg(v_h_3_, v___x_6_, v___x_7_, v___y_5_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus___redArg___lam__0___boxed(lean_object* v_G_9_, lean_object* v_G_10_, lean_object* v_h_11_, lean_object* v_i_12_, lean_object* v___y_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_CORALean_CORALean_Real_Zonotope_plus___redArg___lam__0(v_G_9_, v_G_10_, v_h_11_, v_i_12_, v___y_13_);
lean_dec(v_h_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus___redArg___lam__1(lean_object* v_c_15_, lean_object* v_c_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___f_20_; 
lean_inc(v___y_17_);
v___x_18_ = lean_apply_1(v_c_15_, v___y_17_);
v___x_19_ = lean_apply_1(v_c_16_, v___y_17_);
v___f_20_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_20_, 0, v___x_18_);
lean_closure_set(v___f_20_, 1, v___x_19_);
return v___f_20_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus___redArg(lean_object* v_Z_u2081_21_, lean_object* v_Z_u2082_22_){
_start:
{
lean_object* v_h_23_; lean_object* v_c_24_; lean_object* v_G_25_; lean_object* v_h_26_; lean_object* v_c_27_; lean_object* v_G_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_38_; 
v_h_23_ = lean_ctor_get(v_Z_u2081_21_, 0);
lean_inc(v_h_23_);
v_c_24_ = lean_ctor_get(v_Z_u2081_21_, 1);
lean_inc(v_c_24_);
v_G_25_ = lean_ctor_get(v_Z_u2081_21_, 2);
lean_inc(v_G_25_);
lean_dec_ref(v_Z_u2081_21_);
v_h_26_ = lean_ctor_get(v_Z_u2082_22_, 0);
v_c_27_ = lean_ctor_get(v_Z_u2082_22_, 1);
v_G_28_ = lean_ctor_get(v_Z_u2082_22_, 2);
v_isSharedCheck_38_ = !lean_is_exclusive(v_Z_u2082_22_);
if (v_isSharedCheck_38_ == 0)
{
v___x_30_ = v_Z_u2082_22_;
v_isShared_31_ = v_isSharedCheck_38_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_G_28_);
lean_inc(v_c_27_);
lean_inc(v_h_26_);
lean_dec(v_Z_u2082_22_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_38_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
lean_inc(v_h_23_);
v___f_32_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_plus___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_32_, 0, v_G_25_);
lean_closure_set(v___f_32_, 1, v_G_28_);
lean_closure_set(v___f_32_, 2, v_h_23_);
v___f_33_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_plus___redArg___lam__1), 3, 2);
lean_closure_set(v___f_33_, 0, v_c_24_);
lean_closure_set(v___f_33_, 1, v_c_27_);
v___x_34_ = lean_nat_add(v_h_23_, v_h_26_);
lean_dec(v_h_26_);
lean_dec(v_h_23_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 2, v___f_32_);
lean_ctor_set(v___x_30_, 1, v___f_33_);
lean_ctor_set(v___x_30_, 0, v___x_34_);
v___x_36_ = v___x_30_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v___f_33_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v___f_32_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus(lean_object* v_n_39_, lean_object* v_Z_u2081_40_, lean_object* v_Z_u2082_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_CORALean_CORALean_Real_Zonotope_plus___redArg(v_Z_u2081_40_, v_Z_u2082_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus___boxed(lean_object* v_n_43_, lean_object* v_Z_u2081_44_, lean_object* v_Z_u2082_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_CORALean_CORALean_Real_Zonotope_plus(v_n_43_, v_Z_u2081_44_, v_Z_u2082_45_);
lean_dec(v_n_43_);
return v_res_46_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Zonotope_Zonotope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Real_ContSet_Zonotope_Operations_Plus(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Zonotope_Zonotope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
