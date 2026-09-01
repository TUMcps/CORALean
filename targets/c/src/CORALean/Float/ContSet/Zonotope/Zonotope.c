// Lean compiler output
// Module: CORALean.Float.ContSet.Zonotope.Zonotope
// Imports: public import Init public meta import Init public import CORALean.Float.ContSet.InflatedContSet.API public import CORALean.Real.ContSet.Zonotope.API
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
lean_object* lp_CORALean_CORALean_Float_toRealMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___closed__0 = (const lean_object*)&lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_n_3_, lean_object* v_Z_4_){
_start:
{
lean_object* v_h_5_; lean_object* v_c_6_; lean_object* v_G_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_h_5_ = lean_ctor_get(v_Z_4_, 0);
lean_inc_n(v_h_5_, 2);
v_c_6_ = lean_ctor_get(v_Z_4_, 1);
lean_inc(v_c_6_);
v_G_7_ = lean_ctor_get(v_Z_4_, 2);
lean_inc(v_G_7_);
lean_dec_ref(v_Z_4_);
lean_inc(v_n_3_);
lean_inc(v_inst_2_);
lean_inc_ref(v_inst_1_);
v___x_8_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_toRealVec___boxed), 6, 5);
lean_closure_set(v___x_8_, 0, lean_box(0));
lean_closure_set(v___x_8_, 1, v_inst_1_);
lean_closure_set(v___x_8_, 2, v_inst_2_);
lean_closure_set(v___x_8_, 3, v_n_3_);
lean_closure_set(v___x_8_, 4, v_c_6_);
v___x_9_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_toRealMat___boxed), 8, 6);
lean_closure_set(v___x_9_, 0, lean_box(0));
lean_closure_set(v___x_9_, 1, v_inst_1_);
lean_closure_set(v___x_9_, 2, v_inst_2_);
lean_closure_set(v___x_9_, 3, v_h_5_);
lean_closure_set(v___x_9_, 4, v_n_3_);
lean_closure_set(v___x_9_, 5, v_G_7_);
v___x_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_10_, 0, v_h_5_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___lam__1(lean_object* v_Z_11_){
_start:
{
lean_object* v_E_12_; 
v_E_12_ = lean_ctor_get(v_Z_11_, 3);
lean_inc_ref(v_E_12_);
return v_E_12_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___lam__1___boxed(lean_object* v_Z_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___lam__1(v_Z_13_);
lean_dec_ref(v_Z_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg(lean_object* v_inst_16_, lean_object* v_n_17_, lean_object* v_inst_18_){
_start:
{
lean_object* v___f_19_; lean_object* v___f_20_; lean_object* v___x_21_; 
v___f_19_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___lam__0), 4, 3);
lean_closure_set(v___f_19_, 0, v_inst_16_);
lean_closure_set(v___f_19_, 1, v_inst_18_);
lean_closure_set(v___f_19_, 2, v_n_17_);
v___f_20_ = ((lean_object*)(lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg___closed__0));
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v___f_19_);
lean_ctor_set(v___x_21_, 1, v___f_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope(lean_object* v_00_U0001d54b_22_, lean_object* v_inst_23_, lean_object* v_n_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_CORALean_CORALean_Float_instInflatedContSetZonotopeZonotope___redArg(v_inst_23_, v_n_24_, v_inst_25_);
return v___x_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_InflatedContSet_API(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_ContSet_Zonotope_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Zonotope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_InflatedContSet_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_ContSet_Zonotope_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
