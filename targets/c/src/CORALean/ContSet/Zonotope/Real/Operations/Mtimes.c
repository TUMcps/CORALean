// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Real.Operations.Mtimes
// Imports: public import Init public meta import Init public import CORALean.ContSet.Zonotope.Real.Operations.Map
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_CORALean_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_CORALean_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1_spec__2___closed__0 = (const lean_object*)&lp_CORALean_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* lp_CORALean_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mtimes___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mtimes___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mtimes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mtimes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mtimes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0___redArg___lam__0(lean_object* v_M_1_, lean_object* v_x_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_M_1_, v_x_2_, v_j_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0___lam__0(lean_object* v_v_5_, lean_object* v_w_6_, lean_object* v_i_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___f_10_; 
lean_inc(v_i_7_);
v___x_8_ = lean_apply_1(v_v_5_, v_i_7_);
v___x_9_ = lean_apply_1(v_w_6_, v_i_7_);
v___f_10_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(v___f_10_, 0, v___x_8_);
lean_closure_set(v___f_10_, 1, v___x_9_);
return v___f_10_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1_spec__2(lean_object* v_s_12_){
_start:
{
lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___f_13_ = ((lean_object*)(lp_CORALean_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1_spec__2___closed__0));
v___x_14_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_15_ = l_List_foldrTR___redArg(v___f_13_, v___x_14_, v_s_12_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1___redArg(lean_object* v_s_16_, lean_object* v_f_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lp_mathlib_Multiset_map___redArg(v_f_17_, v_s_16_);
v___x_19_ = lp_CORALean_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1_spec__2(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0(lean_object* v_n_20_, lean_object* v_v_21_, lean_object* v_w_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___f_23_ = lean_alloc_closure((void*)(lp_CORALean_dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_23_, 0, v_v_21_);
lean_closure_set(v___f_23_, 1, v_w_22_);
v___x_24_ = l_List_finRange(v_n_20_);
v___x_25_ = lp_CORALean_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1___redArg(v___x_24_, v___f_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0___redArg(lean_object* v_n_26_, lean_object* v_M_27_, lean_object* v_v_28_, lean_object* v_x_29_){
_start:
{
lean_object* v___f_30_; lean_object* v___x_31_; 
v___f_30_ = lean_alloc_closure((void*)(lp_CORALean_Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_30_, 0, v_M_27_);
lean_closure_set(v___f_30_, 1, v_x_29_);
v___x_31_ = lp_CORALean_dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0(v_n_26_, v___f_30_, v_v_28_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mtimes___redArg___lam__0(lean_object* v_G_32_, lean_object* v_n_33_, lean_object* v_M_34_, lean_object* v_j_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_apply_1(v_G_32_, v_j_35_);
v___x_38_ = lp_CORALean_Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0___redArg(v_n_33_, v_M_34_, v___x_37_, v___y_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mtimes___redArg___lam__1(lean_object* v_n_39_, lean_object* v_M_40_, lean_object* v_c_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_CORALean_Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0___redArg(v_n_39_, v_M_40_, v_c_41_, v___y_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mtimes___redArg(lean_object* v_n_44_, lean_object* v_M_45_, lean_object* v_Z_46_){
_start:
{
lean_object* v_h_47_; lean_object* v_c_48_; lean_object* v_G_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_58_; 
v_h_47_ = lean_ctor_get(v_Z_46_, 0);
v_c_48_ = lean_ctor_get(v_Z_46_, 1);
v_G_49_ = lean_ctor_get(v_Z_46_, 2);
v_isSharedCheck_58_ = !lean_is_exclusive(v_Z_46_);
if (v_isSharedCheck_58_ == 0)
{
v___x_51_ = v_Z_46_;
v_isShared_52_ = v_isSharedCheck_58_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_G_49_);
lean_inc(v_c_48_);
lean_inc(v_h_47_);
lean_dec(v_Z_46_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_58_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___x_56_; 
lean_inc(v_M_45_);
lean_inc(v_n_44_);
v___f_53_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_mtimes___redArg___lam__0), 5, 3);
lean_closure_set(v___f_53_, 0, v_G_49_);
lean_closure_set(v___f_53_, 1, v_n_44_);
lean_closure_set(v___f_53_, 2, v_M_45_);
v___f_54_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_mtimes___redArg___lam__1), 4, 3);
lean_closure_set(v___f_54_, 0, v_n_44_);
lean_closure_set(v___f_54_, 1, v_M_45_);
lean_closure_set(v___f_54_, 2, v_c_48_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 2, v___f_53_);
lean_ctor_set(v___x_51_, 1, v___f_54_);
v___x_56_ = v___x_51_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_h_47_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v___f_54_);
lean_ctor_set(v_reuseFailAlloc_57_, 2, v___f_53_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mtimes(lean_object* v_n_59_, lean_object* v_m_60_, lean_object* v_M_61_, lean_object* v_Z_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_CORALean_CORALean_Real_Zonotope_mtimes___redArg(v_n_59_, v_M_61_, v_Z_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mtimes___boxed(lean_object* v_n_64_, lean_object* v_m_65_, lean_object* v_M_66_, lean_object* v_Z_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_CORALean_CORALean_Real_Zonotope_mtimes(v_n_64_, v_m_65_, v_M_66_, v_Z_67_);
lean_dec(v_m_65_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0(lean_object* v_n_69_, lean_object* v_m_70_, lean_object* v_M_71_, lean_object* v_v_72_, lean_object* v_x_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lp_CORALean_Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0___redArg(v_n_69_, v_M_71_, v_v_72_, v_x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1(lean_object* v_00_u03b9_75_, lean_object* v_s_76_, lean_object* v_f_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lp_CORALean_Finset_sum___at___00dotProduct___at___00Matrix_mulVec___at___00CORALean_Real_Zonotope_mtimes_spec__0_spec__0_spec__1___redArg(v_s_76_, v_f_77_);
return v___x_78_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_Map(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_Mtimes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_Map(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
