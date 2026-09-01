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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotopeVecReal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotopeVecReal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotopeVecReal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instMtimesMatZonotope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instMtimesMatZonotope___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instMtimesMatZonotope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instMtimesMatZonotope___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotopeVecReal___redArg(lean_object* v_inst_1_, lean_object* v_n_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
lean_inc_n(v_n_2_, 2);
lean_inc_ref_n(v_inst_1_, 2);
v___x_3_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_plus___boxed), 5, 3);
lean_closure_set(v___x_3_, 0, lean_box(0));
lean_closure_set(v___x_3_, 1, v_inst_1_);
lean_closure_set(v___x_3_, 2, v_n_2_);
v___x_4_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_linComb), 5, 3);
lean_closure_set(v___x_4_, 0, lean_box(0));
lean_closure_set(v___x_4_, 1, v_inst_1_);
lean_closure_set(v___x_4_, 2, v_n_2_);
v___x_5_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_reduce___boxed), 5, 3);
lean_closure_set(v___x_5_, 0, lean_box(0));
lean_closure_set(v___x_5_, 1, v_inst_1_);
lean_closure_set(v___x_5_, 2, v_n_2_);
v___x_6_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6_, 0, v___x_3_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
lean_ctor_set(v___x_6_, 2, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotopeVecReal(lean_object* v_00_U0001d54b_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_n_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_CORALean_CORALean_Float_instOuterContSetZonotopeVecReal___redArg(v_inst_8_, v_n_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instOuterContSetZonotopeVecReal___boxed(lean_object* v_00_U0001d54b_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_n_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_CORALean_CORALean_Float_instOuterContSetZonotopeVecReal(v_00_U0001d54b_12_, v_inst_13_, v_inst_14_, v_n_15_);
lean_dec(v_inst_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instMtimesMatZonotope___redArg___lam__0(lean_object* v_inst_17_, lean_object* v_m_18_, lean_object* v_n_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lp_CORALean_CORALean_Float_Zonotope_mtimes___redArg(v_inst_17_, v_n_19_, v_m_18_, v___y_20_, v___y_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instMtimesMatZonotope___redArg(lean_object* v_inst_23_){
_start:
{
lean_object* v___f_24_; 
v___f_24_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_instMtimesMatZonotope___redArg___lam__0), 5, 1);
lean_closure_set(v___f_24_, 0, v_inst_23_);
return v___f_24_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instMtimesMatZonotope(lean_object* v_00_U0001d54b_25_, lean_object* v_inst_26_, lean_object* v_inst_27_){
_start:
{
lean_object* v___f_28_; 
v___f_28_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_instMtimesMatZonotope___redArg___lam__0), 5, 1);
lean_closure_set(v___f_28_, 0, v_inst_26_);
return v___f_28_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instMtimesMatZonotope___boxed(lean_object* v_00_U0001d54b_29_, lean_object* v_inst_30_, lean_object* v_inst_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_CORALean_CORALean_Float_instMtimesMatZonotope(v_00_U0001d54b_29_, v_inst_30_, v_inst_31_);
lean_dec(v_inst_31_);
return v_res_32_;
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
