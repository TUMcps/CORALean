// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Float.Zonotope
// Imports: public import Init public meta import Init public import CORALean.ContSet.InflatedContSet.API public import CORALean.ContSet.Zonotope.Real.API
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
lean_object* lp_CORALean_CORALean_Float_toRealVec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___lam__2___boxed(lean_object*);
static const lean_closure_object lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___closed__0 = (const lean_object*)&lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___lam__0(lean_object* v_G_1_, lean_object* v_inst_2_, lean_object* v_j_3_, lean_object* v_i_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_2(v_G_1_, v_i_4_, v_j_3_);
v___x_6_ = lean_apply_1(v_inst_2_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___lam__1(lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_n_9_, lean_object* v_Z_10_){
_start:
{
lean_object* v_h_11_; lean_object* v_c_12_; lean_object* v_G_13_; lean_object* v___f_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_h_11_ = lean_ctor_get(v_Z_10_, 0);
lean_inc(v_h_11_);
v_c_12_ = lean_ctor_get(v_Z_10_, 1);
lean_inc(v_c_12_);
v_G_13_ = lean_ctor_get(v_Z_10_, 2);
lean_inc(v_G_13_);
lean_dec_ref(v_Z_10_);
lean_inc(v_inst_7_);
v___f_14_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___lam__0), 4, 2);
lean_closure_set(v___f_14_, 0, v_G_13_);
lean_closure_set(v___f_14_, 1, v_inst_7_);
v___x_15_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_toRealVec___boxed), 6, 5);
lean_closure_set(v___x_15_, 0, lean_box(0));
lean_closure_set(v___x_15_, 1, v_inst_8_);
lean_closure_set(v___x_15_, 2, v_inst_7_);
lean_closure_set(v___x_15_, 3, v_n_9_);
lean_closure_set(v___x_15_, 4, v_c_12_);
v___x_16_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_16_, 0, v_h_11_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
lean_ctor_set(v___x_16_, 2, v___f_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___lam__2(lean_object* v_Z_17_){
_start:
{
lean_object* v_E_18_; 
v_E_18_ = lean_ctor_get(v_Z_17_, 3);
lean_inc_ref(v_E_18_);
return v_E_18_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___lam__2___boxed(lean_object* v_Z_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___lam__2(v_Z_19_);
lean_dec_ref(v_Z_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg(lean_object* v_inst_22_, lean_object* v_n_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___x_27_; 
v___f_25_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___lam__1), 4, 3);
lean_closure_set(v___f_25_, 0, v_inst_24_);
lean_closure_set(v___f_25_, 1, v_inst_22_);
lean_closure_set(v___f_25_, 2, v_n_23_);
v___f_26_ = ((lean_object*)(lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg___closed__0));
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v___f_25_);
lean_ctor_set(v___x_27_, 1, v___f_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal(lean_object* v_00_U0001d54b_28_, lean_object* v_inst_29_, lean_object* v_n_30_, lean_object* v_inst_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotopeVecReal___redArg(v_inst_29_, v_n_30_, v_inst_31_);
return v___x_32_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_InflatedContSet_API(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Zonotope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_InflatedContSet_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
