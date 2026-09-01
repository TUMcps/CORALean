// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Float.Operations.Mtimes
// Imports: public import Init public meta import Init public import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError
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
lean_object* lp_CORALean_CORALean_Float_mulVecDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_matMulDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_mulVecUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Interval_residual___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_matMulDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Zonotope_generatorError___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Interval_plus___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_mtimesResidual___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_mtimesResidual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_mtimes___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_mtimes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_mtimesResidual___redArg(lean_object* v_inst_1_, lean_object* v_n_2_, lean_object* v_m_3_, lean_object* v_M_4_, lean_object* v_Z_5_){
_start:
{
lean_object* v_h_6_; lean_object* v_c_7_; lean_object* v_G_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_h_6_ = lean_ctor_get(v_Z_5_, 0);
lean_inc_n(v_h_6_, 2);
v_c_7_ = lean_ctor_get(v_Z_5_, 1);
lean_inc_n(v_c_7_, 2);
v_G_8_ = lean_ctor_get(v_Z_5_, 2);
lean_inc(v_G_8_);
lean_dec_ref(v_Z_5_);
lean_inc_n(v_M_4_, 2);
lean_inc_n(v_n_2_, 2);
lean_inc_n(v_m_3_, 3);
lean_inc_ref_n(v_inst_1_, 5);
v___x_9_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_mulVecDown___boxed), 7, 6);
lean_closure_set(v___x_9_, 0, lean_box(0));
lean_closure_set(v___x_9_, 1, v_inst_1_);
lean_closure_set(v___x_9_, 2, v_m_3_);
lean_closure_set(v___x_9_, 3, v_n_2_);
lean_closure_set(v___x_9_, 4, v_M_4_);
lean_closure_set(v___x_9_, 5, v_c_7_);
v___x_10_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_mulVecUp___boxed), 7, 6);
lean_closure_set(v___x_10_, 0, lean_box(0));
lean_closure_set(v___x_10_, 1, v_inst_1_);
lean_closure_set(v___x_10_, 2, v_m_3_);
lean_closure_set(v___x_10_, 3, v_n_2_);
lean_closure_set(v___x_10_, 4, v_M_4_);
lean_closure_set(v___x_10_, 5, v_c_7_);
lean_inc_ref(v___x_9_);
v___x_11_ = lp_CORALean_CORALean_Float_Interval_residual___redArg(v_inst_1_, v___x_9_, v___x_10_, v___x_9_);
v___x_12_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_matMulDiff___boxed), 9, 7);
lean_closure_set(v___x_12_, 0, lean_box(0));
lean_closure_set(v___x_12_, 1, v_inst_1_);
lean_closure_set(v___x_12_, 2, v_m_3_);
lean_closure_set(v___x_12_, 3, v_n_2_);
lean_closure_set(v___x_12_, 4, v_h_6_);
lean_closure_set(v___x_12_, 5, v_M_4_);
lean_closure_set(v___x_12_, 6, v_G_8_);
v___x_13_ = lp_CORALean_CORALean_Float_Zonotope_generatorError___redArg(v_inst_1_, v_m_3_, v_h_6_, v___x_12_);
v___x_14_ = lp_CORALean_CORALean_Float_Interval_plus___redArg(v_inst_1_, v___x_11_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_mtimesResidual(lean_object* v_00_U0001d54b_15_, lean_object* v_inst_16_, lean_object* v_n_17_, lean_object* v_m_18_, lean_object* v_M_19_, lean_object* v_Z_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_CORALean_CORALean_Float_Zonotope_mtimesResidual___redArg(v_inst_16_, v_n_17_, v_m_18_, v_M_19_, v_Z_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_mtimes___redArg(lean_object* v_inst_22_, lean_object* v_n_23_, lean_object* v_m_24_, lean_object* v_M_25_, lean_object* v_Z_26_){
_start:
{
lean_object* v_h_27_; lean_object* v_c_28_; lean_object* v_G_29_; lean_object* v_E_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_h_27_ = lean_ctor_get(v_Z_26_, 0);
lean_inc_n(v_h_27_, 2);
v_c_28_ = lean_ctor_get(v_Z_26_, 1);
v_G_29_ = lean_ctor_get(v_Z_26_, 2);
v_E_30_ = lean_ctor_get(v_Z_26_, 3);
lean_inc(v_c_28_);
lean_inc_n(v_M_25_, 3);
lean_inc_n(v_n_23_, 3);
lean_inc_n(v_m_24_, 2);
lean_inc_ref_n(v_inst_22_, 4);
v___x_31_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_mulVecDown___boxed), 7, 6);
lean_closure_set(v___x_31_, 0, lean_box(0));
lean_closure_set(v___x_31_, 1, v_inst_22_);
lean_closure_set(v___x_31_, 2, v_m_24_);
lean_closure_set(v___x_31_, 3, v_n_23_);
lean_closure_set(v___x_31_, 4, v_M_25_);
lean_closure_set(v___x_31_, 5, v_c_28_);
lean_inc(v_G_29_);
v___x_32_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_matMulDown___boxed), 9, 7);
lean_closure_set(v___x_32_, 0, lean_box(0));
lean_closure_set(v___x_32_, 1, v_inst_22_);
lean_closure_set(v___x_32_, 2, v_m_24_);
lean_closure_set(v___x_32_, 3, v_n_23_);
lean_closure_set(v___x_32_, 4, v_h_27_);
lean_closure_set(v___x_32_, 5, v_M_25_);
lean_closure_set(v___x_32_, 6, v_G_29_);
lean_inc_ref(v_E_30_);
v___x_33_ = lp_CORALean_CORALean_Float_Interval_mtimes___redArg(v_inst_22_, v_n_23_, v_M_25_, v_E_30_);
v___x_34_ = lp_CORALean_CORALean_Float_Zonotope_mtimesResidual___redArg(v_inst_22_, v_n_23_, v_m_24_, v_M_25_, v_Z_26_);
v___x_35_ = lp_CORALean_CORALean_Float_Interval_plus___redArg(v_inst_22_, v___x_33_, v___x_34_);
v___x_36_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_36_, 0, v_h_27_);
lean_ctor_set(v___x_36_, 1, v___x_31_);
lean_ctor_set(v___x_36_, 2, v___x_32_);
lean_ctor_set(v___x_36_, 3, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_mtimes(lean_object* v_00_U0001d54b_37_, lean_object* v_inst_38_, lean_object* v_n_39_, lean_object* v_m_40_, lean_object* v_M_41_, lean_object* v_Z_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_CORALean_CORALean_Float_Zonotope_mtimes___redArg(v_inst_38_, v_n_39_, v_m_40_, v_M_41_, v_Z_42_);
return v___x_43_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Operations_GeneratorError(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Operations_Mtimes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Float_Operations_GeneratorError(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
