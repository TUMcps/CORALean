// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Float.Instances
// Imports: public import Init public meta import Init public import CORALean.ContSet.Zonotope.Float.Theorems.API
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
lean_object* lp_CORALean_CORALean_Float_Zonotope_mtimes___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Zonotope_plus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Zonotope_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotope___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotope___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotope___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_m_2_, lean_object* v_n_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lp_CORALean_CORALean_Float_Zonotope_mtimes___redArg(v_inst_1_, v_n_3_, v_m_2_, v___y_4_, v___y_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotope___redArg(lean_object* v_inst_7_){
_start:
{
lean_object* v___f_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
lean_inc_ref_n(v_inst_7_, 3);
v___f_8_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_instOuterContSetZonotope___redArg___lam__0), 5, 1);
lean_closure_set(v___f_8_, 0, v_inst_7_);
v___x_9_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_plus___boxed), 5, 2);
lean_closure_set(v___x_9_, 0, lean_box(0));
lean_closure_set(v___x_9_, 1, v_inst_7_);
v___x_10_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_linComb), 5, 2);
lean_closure_set(v___x_10_, 0, lean_box(0));
lean_closure_set(v___x_10_, 1, v_inst_7_);
v___x_11_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_reduce___boxed), 5, 2);
lean_closure_set(v___x_11_, 0, lean_box(0));
lean_closure_set(v___x_11_, 1, v_inst_7_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v___f_8_);
lean_ctor_set(v___x_12_, 1, v___x_9_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotope(lean_object* v_00_U0001d54b_13_, lean_object* v_inst_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_CORALean_CORALean_Float_instOuterContSetZonotope___redArg(v_inst_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotope___boxed(lean_object* v_00_U0001d54b_17_, lean_object* v_inst_18_, lean_object* v_inst_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_CORALean_CORALean_Float_instOuterContSetZonotope(v_00_U0001d54b_17_, v_inst_18_, v_inst_19_);
lean_dec(v_inst_19_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Theorems_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Float_Theorems_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
