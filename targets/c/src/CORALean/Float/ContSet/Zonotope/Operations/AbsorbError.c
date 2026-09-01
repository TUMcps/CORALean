// Lean compiler output
// Module: CORALean.Float.ContSet.Zonotope.Operations.AbsorbError
// Imports: public import Init public meta import Init public import CORALean.Float.ContSet.Zonotope.Zonotope
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
lean_object* lp_CORALean_CORALean_Float_subUp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_diagonalBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_addCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Interval_residual___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftDown___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftUp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_errorRadius___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_errorRadius(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_errorRadius___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_absorbError___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_absorbError___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_absorbError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_absorbError(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftDown___redArg(lean_object* v_inst_1_, lean_object* v_Z_2_, lean_object* v_i_3_){
_start:
{
lean_object* v_E_4_; lean_object* v_addDown_5_; lean_object* v_half_6_; lean_object* v_c_7_; lean_object* v_inf_8_; lean_object* v_sup_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_E_4_ = lean_ctor_get(v_Z_2_, 3);
lean_inc_ref(v_E_4_);
v_addDown_5_ = lean_ctor_get(v_inst_1_, 3);
lean_inc_n(v_addDown_5_, 2);
v_half_6_ = lean_ctor_get(v_inst_1_, 9);
lean_inc(v_half_6_);
lean_dec_ref(v_inst_1_);
v_c_7_ = lean_ctor_get(v_Z_2_, 1);
lean_inc(v_c_7_);
lean_dec_ref(v_Z_2_);
v_inf_8_ = lean_ctor_get(v_E_4_, 0);
lean_inc(v_inf_8_);
v_sup_9_ = lean_ctor_get(v_E_4_, 1);
lean_inc(v_sup_9_);
lean_dec_ref(v_E_4_);
lean_inc_n(v_i_3_, 2);
v___x_10_ = lean_apply_1(v_c_7_, v_i_3_);
v___x_11_ = lean_apply_1(v_inf_8_, v_i_3_);
v___x_12_ = lean_apply_1(v_sup_9_, v_i_3_);
v___x_13_ = lean_apply_2(v_addDown_5_, v___x_11_, v___x_12_);
v___x_14_ = lean_apply_1(v_half_6_, v___x_13_);
v___x_15_ = lean_apply_2(v_addDown_5_, v___x_10_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftDown(lean_object* v_00_U0001d54b_16_, lean_object* v_inst_17_, lean_object* v_n_18_, lean_object* v_Z_19_, lean_object* v_i_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_CORALean_CORALean_Float_Zonotope_shiftDown___redArg(v_inst_17_, v_Z_19_, v_i_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftDown___boxed(lean_object* v_00_U0001d54b_22_, lean_object* v_inst_23_, lean_object* v_n_24_, lean_object* v_Z_25_, lean_object* v_i_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_CORALean_CORALean_Float_Zonotope_shiftDown(v_00_U0001d54b_22_, v_inst_23_, v_n_24_, v_Z_25_, v_i_26_);
lean_dec(v_n_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftUp___redArg(lean_object* v_inst_28_, lean_object* v_Z_29_, lean_object* v_i_30_){
_start:
{
lean_object* v_E_31_; lean_object* v_addUp_32_; lean_object* v_half_33_; lean_object* v_c_34_; lean_object* v_inf_35_; lean_object* v_sup_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_E_31_ = lean_ctor_get(v_Z_29_, 3);
lean_inc_ref(v_E_31_);
v_addUp_32_ = lean_ctor_get(v_inst_28_, 2);
lean_inc_n(v_addUp_32_, 2);
v_half_33_ = lean_ctor_get(v_inst_28_, 9);
lean_inc(v_half_33_);
lean_dec_ref(v_inst_28_);
v_c_34_ = lean_ctor_get(v_Z_29_, 1);
lean_inc(v_c_34_);
lean_dec_ref(v_Z_29_);
v_inf_35_ = lean_ctor_get(v_E_31_, 0);
lean_inc(v_inf_35_);
v_sup_36_ = lean_ctor_get(v_E_31_, 1);
lean_inc(v_sup_36_);
lean_dec_ref(v_E_31_);
lean_inc_n(v_i_30_, 2);
v___x_37_ = lean_apply_1(v_c_34_, v_i_30_);
v___x_38_ = lean_apply_1(v_inf_35_, v_i_30_);
v___x_39_ = lean_apply_1(v_sup_36_, v_i_30_);
v___x_40_ = lean_apply_2(v_addUp_32_, v___x_38_, v___x_39_);
v___x_41_ = lean_apply_1(v_half_33_, v___x_40_);
v___x_42_ = lean_apply_2(v_addUp_32_, v___x_37_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftUp(lean_object* v_00_U0001d54b_43_, lean_object* v_inst_44_, lean_object* v_n_45_, lean_object* v_Z_46_, lean_object* v_i_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_CORALean_CORALean_Float_Zonotope_shiftUp___redArg(v_inst_44_, v_Z_46_, v_i_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftUp___boxed(lean_object* v_00_U0001d54b_49_, lean_object* v_inst_50_, lean_object* v_n_51_, lean_object* v_Z_52_, lean_object* v_i_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_CORALean_CORALean_Float_Zonotope_shiftUp(v_00_U0001d54b_49_, v_inst_50_, v_n_51_, v_Z_52_, v_i_53_);
lean_dec(v_n_51_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_errorRadius___redArg(lean_object* v_inst_55_, lean_object* v_Z_56_, lean_object* v_i_57_){
_start:
{
lean_object* v_E_58_; lean_object* v_half_59_; lean_object* v_inf_60_; lean_object* v_sup_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_E_58_ = lean_ctor_get(v_Z_56_, 3);
lean_inc_ref(v_E_58_);
lean_dec_ref(v_Z_56_);
v_half_59_ = lean_ctor_get(v_inst_55_, 9);
lean_inc(v_half_59_);
v_inf_60_ = lean_ctor_get(v_E_58_, 0);
lean_inc(v_inf_60_);
v_sup_61_ = lean_ctor_get(v_E_58_, 1);
lean_inc(v_sup_61_);
lean_dec_ref(v_E_58_);
lean_inc(v_i_57_);
v___x_62_ = lean_apply_1(v_sup_61_, v_i_57_);
v___x_63_ = lean_apply_1(v_inf_60_, v_i_57_);
v___x_64_ = lp_CORALean_CORALean_Float_subUp___redArg(v_inst_55_, v___x_62_, v___x_63_);
v___x_65_ = lean_apply_1(v_half_59_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_errorRadius(lean_object* v_00_U0001d54b_66_, lean_object* v_inst_67_, lean_object* v_n_68_, lean_object* v_Z_69_, lean_object* v_i_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_CORALean_CORALean_Float_Zonotope_errorRadius___redArg(v_inst_67_, v_Z_69_, v_i_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_errorRadius___boxed(lean_object* v_00_U0001d54b_72_, lean_object* v_inst_73_, lean_object* v_n_74_, lean_object* v_Z_75_, lean_object* v_i_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_CORALean_CORALean_Float_Zonotope_errorRadius(v_00_U0001d54b_72_, v_inst_73_, v_n_74_, v_Z_75_, v_i_76_);
lean_dec(v_n_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_absorbError___redArg___lam__0(lean_object* v_G_78_, lean_object* v_inst_79_, lean_object* v_n_80_, lean_object* v_Z_81_, lean_object* v_h_82_, lean_object* v_i_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
lean_inc(v_i_83_);
v___x_85_ = lean_apply_1(v_G_78_, v_i_83_);
lean_inc(v_n_80_);
lean_inc_ref(v_inst_79_);
v___x_86_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_errorRadius___boxed), 5, 4);
lean_closure_set(v___x_86_, 0, lean_box(0));
lean_closure_set(v___x_86_, 1, v_inst_79_);
lean_closure_set(v___x_86_, 2, v_n_80_);
lean_closure_set(v___x_86_, 3, v_Z_81_);
v___x_87_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_diagonalBlock___boxed), 6, 5);
lean_closure_set(v___x_87_, 0, lean_box(0));
lean_closure_set(v___x_87_, 1, v_inst_79_);
lean_closure_set(v___x_87_, 2, v_n_80_);
lean_closure_set(v___x_87_, 3, v___x_86_);
lean_closure_set(v___x_87_, 4, v_i_83_);
v___x_88_ = l_Fin_addCases___redArg(v_h_82_, v___x_85_, v___x_87_, v___y_84_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_absorbError___redArg___lam__0___boxed(lean_object* v_G_89_, lean_object* v_inst_90_, lean_object* v_n_91_, lean_object* v_Z_92_, lean_object* v_h_93_, lean_object* v_i_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_CORALean_CORALean_Float_Zonotope_absorbError___redArg___lam__0(v_G_89_, v_inst_90_, v_n_91_, v_Z_92_, v_h_93_, v_i_94_, v___y_95_);
lean_dec(v_h_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_absorbError___redArg(lean_object* v_inst_97_, lean_object* v_n_98_, lean_object* v_Z_99_){
_start:
{
lean_object* v_h_100_; lean_object* v_G_101_; lean_object* v___f_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_h_100_ = lean_ctor_get(v_Z_99_, 0);
v_G_101_ = lean_ctor_get(v_Z_99_, 2);
lean_inc(v_h_100_);
lean_inc_ref_n(v_Z_99_, 2);
lean_inc_n(v_n_98_, 2);
lean_inc_ref_n(v_inst_97_, 3);
lean_inc(v_G_101_);
v___f_102_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_absorbError___redArg___lam__0___boxed), 7, 5);
lean_closure_set(v___f_102_, 0, v_G_101_);
lean_closure_set(v___f_102_, 1, v_inst_97_);
lean_closure_set(v___f_102_, 2, v_n_98_);
lean_closure_set(v___f_102_, 3, v_Z_99_);
lean_closure_set(v___f_102_, 4, v_h_100_);
v___x_103_ = lean_nat_add(v_h_100_, v_n_98_);
v___x_104_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_shiftDown___boxed), 5, 4);
lean_closure_set(v___x_104_, 0, lean_box(0));
lean_closure_set(v___x_104_, 1, v_inst_97_);
lean_closure_set(v___x_104_, 2, v_n_98_);
lean_closure_set(v___x_104_, 3, v_Z_99_);
v___x_105_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_shiftUp___boxed), 5, 4);
lean_closure_set(v___x_105_, 0, lean_box(0));
lean_closure_set(v___x_105_, 1, v_inst_97_);
lean_closure_set(v___x_105_, 2, v_n_98_);
lean_closure_set(v___x_105_, 3, v_Z_99_);
lean_inc_ref_n(v___x_104_, 2);
v___x_106_ = lp_CORALean_CORALean_Float_Interval_residual___redArg(v_inst_97_, v___x_104_, v___x_105_, v___x_104_);
v___x_107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_107_, 0, v___x_103_);
lean_ctor_set(v___x_107_, 1, v___x_104_);
lean_ctor_set(v___x_107_, 2, v___f_102_);
lean_ctor_set(v___x_107_, 3, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_absorbError(lean_object* v_00_U0001d54b_108_, lean_object* v_inst_109_, lean_object* v_n_110_, lean_object* v_Z_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lp_CORALean_CORALean_Float_Zonotope_absorbError___redArg(v_inst_109_, v_n_110_, v_Z_111_);
return v___x_112_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Zonotope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Operations_AbsorbError(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Zonotope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
