// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Real.Instances
// Imports: public import Init public meta import Init public import CORALean.ContSet.Zonotope.Real.Theorems.API
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
lean_object* lp_CORALean_CORALean_matMulLeft___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Real_Zonotope_map___redArg(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Real_Zonotope_mtimes___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instCommSemiring;
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_mulVecBilin___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instContSetZonotopeOfModuleReal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instContSetZonotopeOfModuleReal___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instMtimesMatRealZonotopeVec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instMtimesMatRealZonotopeVec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_CORALean_CORALean_Real_instMtimesMatRealZonotopeVec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_CORALean_CORALean_Real_instMtimesMatRealZonotopeVec___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_CORALean_CORALean_Real_instMtimesMatRealZonotopeVec___closed__0 = (const lean_object*)&lp_CORALean_CORALean_Real_instMtimesMatRealZonotopeVec___closed__0_value;
LEAN_EXPORT const lean_object* lp_CORALean_CORALean_Real_instMtimesMatRealZonotopeVec = (const lean_object*)&lp_CORALean_CORALean_Real_instMtimesMatRealZonotopeVec___closed__0_value;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeVecReal___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeVecReal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeVecReal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeReal___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeReal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeReal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeReal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instContSetZonotopeOfModuleReal(lean_object* v_00_u03b1_1_, lean_object* v_inst_2_, lean_object* v_inst_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instContSetZonotopeOfModuleReal___boxed(lean_object* v_00_u03b1_5_, lean_object* v_inst_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_CORALean_CORALean_Real_instContSetZonotopeOfModuleReal(v_00_u03b1_5_, v_inst_6_, v_inst_7_);
lean_dec(v_inst_7_);
lean_dec_ref(v_inst_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instMtimesMatRealZonotopeVec___lam__0(lean_object* v_m_9_, lean_object* v_n_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lp_CORALean_CORALean_Real_Zonotope_mtimes___redArg(v_n_10_, v___y_11_, v___y_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instMtimesMatRealZonotopeVec___lam__0___boxed(lean_object* v_m_14_, lean_object* v_n_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_CORALean_CORALean_Real_instMtimesMatRealZonotopeVec___lam__0(v_m_14_, v_n_15_, v___y_16_, v___y_17_);
lean_dec(v_m_14_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeVecReal___redArg___lam__0(lean_object* v___x_21_, lean_object* v_inst_22_, lean_object* v_p_23_, lean_object* v_q_24_, lean_object* v___x_25_, lean_object* v_M_26_, lean_object* v_Z_27_){
_start:
{
lean_object* v___x_28_; lean_object* v_toNonUnitalNonAssocSemiring_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_28_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v___x_21_);
v_toNonUnitalNonAssocSemiring_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc_ref(v_toNonUnitalNonAssocSemiring_29_);
lean_dec_ref(v___x_28_);
v___x_30_ = lean_apply_3(v_inst_22_, v_p_23_, v_q_24_, v_M_26_);
v___x_31_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_mulVecBilin___redArg___lam__0), 5, 3);
lean_closure_set(v___x_31_, 0, v_toNonUnitalNonAssocSemiring_29_);
lean_closure_set(v___x_31_, 1, v___x_25_);
lean_closure_set(v___x_31_, 2, v___x_30_);
v___x_32_ = lp_CORALean_CORALean_Real_Zonotope_map___redArg(v___x_31_, v_Z_27_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeVecReal___redArg(lean_object* v_inst_33_, lean_object* v_p_34_, lean_object* v_q_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___f_38_; 
v___x_36_ = lp_mathlib_Real_instCommSemiring;
lean_inc(v_q_35_);
v___x_37_ = l_List_finRange(v_q_35_);
v___f_38_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeVecReal___redArg___lam__0), 7, 5);
lean_closure_set(v___f_38_, 0, v___x_36_);
lean_closure_set(v___f_38_, 1, v_inst_33_);
lean_closure_set(v___f_38_, 2, v_p_34_);
lean_closure_set(v___f_38_, 3, v_q_35_);
lean_closure_set(v___f_38_, 4, v___x_37_);
return v___f_38_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeVecReal(lean_object* v_00_U0001d54b_39_, lean_object* v_inst_40_, lean_object* v_p_41_, lean_object* v_q_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeVecReal___redArg(v_inst_40_, v_p_41_, v_q_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeReal___redArg___lam__0(lean_object* v_inst_44_, lean_object* v_p_45_, lean_object* v_q_46_, lean_object* v_M_47_, lean_object* v_Z_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___f_50_; lean_object* v___x_51_; 
lean_inc(v_q_46_);
v___x_49_ = lean_apply_3(v_inst_44_, v_p_45_, v_q_46_, v_M_47_);
v___f_50_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_matMulLeft___redArg___lam__2), 5, 2);
lean_closure_set(v___f_50_, 0, v___x_49_);
lean_closure_set(v___f_50_, 1, v_q_46_);
v___x_51_ = lp_CORALean_CORALean_Real_Zonotope_map___redArg(v___f_50_, v_Z_48_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeReal___redArg(lean_object* v_inst_52_, lean_object* v_p_53_, lean_object* v_q_54_){
_start:
{
lean_object* v___f_55_; 
v___f_55_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeReal___redArg___lam__0), 5, 3);
lean_closure_set(v___f_55_, 0, v_inst_52_);
lean_closure_set(v___f_55_, 1, v_p_53_);
lean_closure_set(v___f_55_, 2, v_q_54_);
return v___f_55_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeReal(lean_object* v_00_U0001d54b_56_, lean_object* v_inst_57_, lean_object* v_p_58_, lean_object* v_q_59_, lean_object* v_r_60_){
_start:
{
lean_object* v___f_61_; 
v___f_61_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeReal___redArg___lam__0), 5, 3);
lean_closure_set(v___f_61_, 0, v_inst_57_);
lean_closure_set(v___f_61_, 1, v_p_58_);
lean_closure_set(v___f_61_, 2, v_q_59_);
return v___f_61_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeReal___boxed(lean_object* v_00_U0001d54b_62_, lean_object* v_inst_63_, lean_object* v_p_64_, lean_object* v_q_65_, lean_object* v_r_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_CORALean_CORALean_Real_instLinMtimesMatZonotopeReal(v_00_U0001d54b_62_, v_inst_63_, v_p_64_, v_q_65_, v_r_66_);
lean_dec(v_r_66_);
return v_res_67_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Theorems_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
