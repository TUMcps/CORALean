// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Float.Operations.LinComb
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_subDown___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Fin_append___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_addCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Interval_linComb___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Interval_residual___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_subUp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Interval_symmetric___redArg(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Interval_plus___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpoint___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpointResidual___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpointResidual___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpointResidual___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpointResidual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiffError___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiffError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiffError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiffError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpoint___redArg(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_, lean_object* v_i_4_){
_start:
{
lean_object* v_addDown_5_; lean_object* v_half_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_addDown_5_ = lean_ctor_get(v_inst_1_, 3);
lean_inc(v_addDown_5_);
v_half_6_ = lean_ctor_get(v_inst_1_, 9);
lean_inc(v_half_6_);
lean_dec_ref(v_inst_1_);
lean_inc(v_i_4_);
v___x_7_ = lean_apply_1(v_a_2_, v_i_4_);
v___x_8_ = lean_apply_1(v_b_3_, v_i_4_);
v___x_9_ = lean_apply_2(v_addDown_5_, v___x_7_, v___x_8_);
v___x_10_ = lean_apply_1(v_half_6_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpoint(lean_object* v_00_U0001d54b_11_, lean_object* v_inst_12_, lean_object* v_n_13_, lean_object* v_a_14_, lean_object* v_b_15_, lean_object* v_i_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_CORALean_CORALean_Float_Zonotope_midpoint___redArg(v_inst_12_, v_a_14_, v_b_15_, v_i_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpoint___boxed(lean_object* v_00_U0001d54b_18_, lean_object* v_inst_19_, lean_object* v_n_20_, lean_object* v_a_21_, lean_object* v_b_22_, lean_object* v_i_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_CORALean_CORALean_Float_Zonotope_midpoint(v_00_U0001d54b_18_, v_inst_19_, v_n_20_, v_a_21_, v_b_22_, v_i_23_);
lean_dec(v_n_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiff___redArg(lean_object* v_inst_25_, lean_object* v_a_26_, lean_object* v_b_27_, lean_object* v_i_28_){
_start:
{
lean_object* v_half_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_half_29_ = lean_ctor_get(v_inst_25_, 9);
lean_inc(v_half_29_);
lean_inc(v_i_28_);
v___x_30_ = lean_apply_1(v_a_26_, v_i_28_);
v___x_31_ = lean_apply_1(v_b_27_, v_i_28_);
v___x_32_ = lp_CORALean_CORALean_Float_subDown___redArg(v_inst_25_, v___x_30_, v___x_31_);
v___x_33_ = lean_apply_1(v_half_29_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiff(lean_object* v_00_U0001d54b_34_, lean_object* v_inst_35_, lean_object* v_n_36_, lean_object* v_a_37_, lean_object* v_b_38_, lean_object* v_i_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_CORALean_CORALean_Float_Zonotope_halfDiff___redArg(v_inst_35_, v_a_37_, v_b_38_, v_i_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiff___boxed(lean_object* v_00_U0001d54b_41_, lean_object* v_inst_42_, lean_object* v_n_43_, lean_object* v_a_44_, lean_object* v_b_45_, lean_object* v_i_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_CORALean_CORALean_Float_Zonotope_halfDiff(v_00_U0001d54b_41_, v_inst_42_, v_n_43_, v_a_44_, v_b_45_, v_i_46_);
lean_dec(v_n_43_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpointResidual___redArg___lam__0(lean_object* v_inst_48_, lean_object* v_a_49_, lean_object* v_b_50_, lean_object* v_i_51_){
_start:
{
lean_object* v_addDown_52_; lean_object* v_half_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_addDown_52_ = lean_ctor_get(v_inst_48_, 3);
lean_inc(v_addDown_52_);
v_half_53_ = lean_ctor_get(v_inst_48_, 9);
lean_inc(v_half_53_);
lean_dec_ref(v_inst_48_);
lean_inc(v_i_51_);
v___x_54_ = lean_apply_1(v_a_49_, v_i_51_);
v___x_55_ = lean_apply_1(v_b_50_, v_i_51_);
v___x_56_ = lean_apply_2(v_addDown_52_, v___x_54_, v___x_55_);
v___x_57_ = lean_apply_1(v_half_53_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpointResidual___redArg___lam__1(lean_object* v_inst_58_, lean_object* v_a_59_, lean_object* v_b_60_, lean_object* v_i_61_){
_start:
{
lean_object* v_addUp_62_; lean_object* v_half_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_addUp_62_ = lean_ctor_get(v_inst_58_, 2);
lean_inc(v_addUp_62_);
v_half_63_ = lean_ctor_get(v_inst_58_, 9);
lean_inc(v_half_63_);
lean_dec_ref(v_inst_58_);
lean_inc(v_i_61_);
v___x_64_ = lean_apply_1(v_a_59_, v_i_61_);
v___x_65_ = lean_apply_1(v_b_60_, v_i_61_);
v___x_66_ = lean_apply_2(v_addUp_62_, v___x_64_, v___x_65_);
v___x_67_ = lean_apply_1(v_half_63_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpointResidual___redArg(lean_object* v_inst_68_, lean_object* v_n_69_, lean_object* v_a_70_, lean_object* v_b_71_){
_start:
{
lean_object* v___f_72_; lean_object* v___f_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_inc_n(v_b_71_, 2);
lean_inc_n(v_a_70_, 2);
lean_inc_ref_n(v_inst_68_, 3);
v___f_72_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_midpointResidual___redArg___lam__0), 4, 3);
lean_closure_set(v___f_72_, 0, v_inst_68_);
lean_closure_set(v___f_72_, 1, v_a_70_);
lean_closure_set(v___f_72_, 2, v_b_71_);
v___f_73_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_midpointResidual___redArg___lam__1), 4, 3);
lean_closure_set(v___f_73_, 0, v_inst_68_);
lean_closure_set(v___f_73_, 1, v_a_70_);
lean_closure_set(v___f_73_, 2, v_b_71_);
v___x_74_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_midpoint___boxed), 6, 5);
lean_closure_set(v___x_74_, 0, lean_box(0));
lean_closure_set(v___x_74_, 1, v_inst_68_);
lean_closure_set(v___x_74_, 2, v_n_69_);
lean_closure_set(v___x_74_, 3, v_a_70_);
lean_closure_set(v___x_74_, 4, v_b_71_);
v___x_75_ = lp_CORALean_CORALean_Float_Interval_residual___redArg(v_inst_68_, v___f_72_, v___f_73_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_midpointResidual(lean_object* v_00_U0001d54b_76_, lean_object* v_inst_77_, lean_object* v_n_78_, lean_object* v_a_79_, lean_object* v_b_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_CORALean_CORALean_Float_Zonotope_midpointResidual___redArg(v_inst_77_, v_n_78_, v_a_79_, v_b_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiffError___redArg___lam__0(lean_object* v_inst_82_, lean_object* v_a_83_, lean_object* v_b_84_, lean_object* v_i_85_){
_start:
{
lean_object* v_half_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_half_86_ = lean_ctor_get(v_inst_82_, 9);
lean_inc(v_i_85_);
v___x_87_ = lean_apply_1(v_a_83_, v_i_85_);
v___x_88_ = lean_apply_1(v_b_84_, v_i_85_);
lean_inc(v___x_88_);
lean_inc(v___x_87_);
lean_inc_ref_n(v_inst_82_, 2);
v___x_89_ = lp_CORALean_CORALean_Float_subUp___redArg(v_inst_82_, v___x_87_, v___x_88_);
lean_inc_n(v_half_86_, 2);
v___x_90_ = lean_apply_1(v_half_86_, v___x_89_);
v___x_91_ = lp_CORALean_CORALean_Float_subDown___redArg(v_inst_82_, v___x_87_, v___x_88_);
v___x_92_ = lean_apply_1(v_half_86_, v___x_91_);
v___x_93_ = lp_CORALean_CORALean_Float_subUp___redArg(v_inst_82_, v___x_90_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiffError___redArg(lean_object* v_inst_94_, lean_object* v_a_95_, lean_object* v_b_96_){
_start:
{
lean_object* v___f_97_; lean_object* v___x_98_; 
lean_inc_ref(v_inst_94_);
v___f_97_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_halfDiffError___redArg___lam__0), 4, 3);
lean_closure_set(v___f_97_, 0, v_inst_94_);
lean_closure_set(v___f_97_, 1, v_a_95_);
lean_closure_set(v___f_97_, 2, v_b_96_);
v___x_98_ = lp_CORALean_CORALean_Float_Interval_symmetric___redArg(v_inst_94_, v___f_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiffError(lean_object* v_00_U0001d54b_99_, lean_object* v_inst_100_, lean_object* v_n_101_, lean_object* v_a_102_, lean_object* v_b_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lp_CORALean_CORALean_Float_Zonotope_halfDiffError___redArg(v_inst_100_, v_a_102_, v_b_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_halfDiffError___boxed(lean_object* v_00_U0001d54b_105_, lean_object* v_inst_106_, lean_object* v_n_107_, lean_object* v_a_108_, lean_object* v_b_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = lp_CORALean_CORALean_Float_Zonotope_halfDiffError(v_00_U0001d54b_105_, v_inst_106_, v_n_107_, v_a_108_, v_b_109_);
lean_dec(v_n_107_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb___redArg___lam__0(lean_object* v_inst_111_, lean_object* v_c_112_, lean_object* v_c_113_, lean_object* v_i_114_, lean_object* v_x_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lp_CORALean_CORALean_Float_Zonotope_halfDiff___redArg(v_inst_111_, v_c_112_, v_c_113_, v_i_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb___redArg___lam__0___boxed(lean_object* v_inst_117_, lean_object* v_c_118_, lean_object* v_c_119_, lean_object* v_i_120_, lean_object* v_x_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = lp_CORALean_CORALean_Float_Zonotope_linComb___redArg___lam__0(v_inst_117_, v_c_118_, v_c_119_, v_i_120_, v_x_121_);
lean_dec(v_x_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb___redArg___lam__1(lean_object* v_inst_123_, lean_object* v_c_124_, lean_object* v_c_125_, lean_object* v_G_126_, lean_object* v_G_127_, lean_object* v_h_128_, lean_object* v_h_129_, lean_object* v___x_130_, lean_object* v_i_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___f_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
lean_inc_n(v_i_131_, 2);
v___f_133_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_linComb___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_133_, 0, v_inst_123_);
lean_closure_set(v___f_133_, 1, v_c_124_);
lean_closure_set(v___f_133_, 2, v_c_125_);
lean_closure_set(v___f_133_, 3, v_i_131_);
v___x_134_ = lean_apply_1(v_G_126_, v_i_131_);
v___x_135_ = lean_apply_1(v_G_127_, v_i_131_);
v___x_136_ = lean_alloc_closure((void*)(lp_mathlib_Fin_append___boxed), 6, 5);
lean_closure_set(v___x_136_, 0, v_h_128_);
lean_closure_set(v___x_136_, 1, v_h_129_);
lean_closure_set(v___x_136_, 2, lean_box(0));
lean_closure_set(v___x_136_, 3, v___x_134_);
lean_closure_set(v___x_136_, 4, v___x_135_);
v___x_137_ = l_Fin_addCases___redArg(v___x_130_, v___x_136_, v___f_133_, v___y_132_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb___redArg___lam__1___boxed(lean_object* v_inst_138_, lean_object* v_c_139_, lean_object* v_c_140_, lean_object* v_G_141_, lean_object* v_G_142_, lean_object* v_h_143_, lean_object* v_h_144_, lean_object* v___x_145_, lean_object* v_i_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = lp_CORALean_CORALean_Float_Zonotope_linComb___redArg___lam__1(v_inst_138_, v_c_139_, v_c_140_, v_G_141_, v_G_142_, v_h_143_, v_h_144_, v___x_145_, v_i_146_, v___y_147_);
lean_dec(v___x_145_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb___redArg(lean_object* v_inst_149_, lean_object* v_n_150_, lean_object* v_Z_u2081_151_, lean_object* v_Z_u2082_152_){
_start:
{
lean_object* v_h_153_; lean_object* v_c_154_; lean_object* v_G_155_; lean_object* v_E_156_; lean_object* v_h_157_; lean_object* v_c_158_; lean_object* v_G_159_; lean_object* v_E_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_177_; 
v_h_153_ = lean_ctor_get(v_Z_u2081_151_, 0);
lean_inc(v_h_153_);
v_c_154_ = lean_ctor_get(v_Z_u2081_151_, 1);
lean_inc(v_c_154_);
v_G_155_ = lean_ctor_get(v_Z_u2081_151_, 2);
lean_inc(v_G_155_);
v_E_156_ = lean_ctor_get(v_Z_u2081_151_, 3);
lean_inc_ref(v_E_156_);
lean_dec_ref(v_Z_u2081_151_);
v_h_157_ = lean_ctor_get(v_Z_u2082_152_, 0);
v_c_158_ = lean_ctor_get(v_Z_u2082_152_, 1);
v_G_159_ = lean_ctor_get(v_Z_u2082_152_, 2);
v_E_160_ = lean_ctor_get(v_Z_u2082_152_, 3);
v_isSharedCheck_177_ = !lean_is_exclusive(v_Z_u2082_152_);
if (v_isSharedCheck_177_ == 0)
{
v___x_162_ = v_Z_u2082_152_;
v_isShared_163_ = v_isSharedCheck_177_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_E_160_);
lean_inc(v_G_159_);
lean_inc(v_c_158_);
lean_inc(v_h_157_);
lean_dec(v_Z_u2082_152_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_177_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_164_ = lean_nat_add(v_h_153_, v_h_157_);
lean_inc(v___x_164_);
lean_inc_n(v_c_158_, 3);
lean_inc_n(v_c_154_, 3);
lean_inc_ref_n(v_inst_149_, 6);
v___f_165_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_linComb___redArg___lam__1___boxed), 10, 8);
lean_closure_set(v___f_165_, 0, v_inst_149_);
lean_closure_set(v___f_165_, 1, v_c_154_);
lean_closure_set(v___f_165_, 2, v_c_158_);
lean_closure_set(v___f_165_, 3, v_G_155_);
lean_closure_set(v___f_165_, 4, v_G_159_);
lean_closure_set(v___f_165_, 5, v_h_153_);
lean_closure_set(v___f_165_, 6, v_h_157_);
lean_closure_set(v___f_165_, 7, v___x_164_);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_add(v___x_164_, v___x_166_);
lean_dec(v___x_164_);
lean_inc(v_n_150_);
v___x_168_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_midpoint___boxed), 6, 5);
lean_closure_set(v___x_168_, 0, lean_box(0));
lean_closure_set(v___x_168_, 1, v_inst_149_);
lean_closure_set(v___x_168_, 2, v_n_150_);
lean_closure_set(v___x_168_, 3, v_c_154_);
lean_closure_set(v___x_168_, 4, v_c_158_);
v___x_169_ = lp_CORALean_CORALean_Float_Interval_linComb___redArg(v_inst_149_, v_E_156_, v_E_160_);
v___x_170_ = lp_CORALean_CORALean_Float_Zonotope_midpointResidual___redArg(v_inst_149_, v_n_150_, v_c_154_, v_c_158_);
v___x_171_ = lp_CORALean_CORALean_Float_Zonotope_halfDiffError___redArg(v_inst_149_, v_c_154_, v_c_158_);
v___x_172_ = lp_CORALean_CORALean_Float_Interval_plus___redArg(v_inst_149_, v___x_170_, v___x_171_);
v___x_173_ = lp_CORALean_CORALean_Float_Interval_plus___redArg(v_inst_149_, v___x_169_, v___x_172_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 3, v___x_173_);
lean_ctor_set(v___x_162_, 2, v___f_165_);
lean_ctor_set(v___x_162_, 1, v___x_168_);
lean_ctor_set(v___x_162_, 0, v___x_167_);
v___x_175_ = v___x_162_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v___f_165_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_linComb(lean_object* v_00_U0001d54b_178_, lean_object* v_inst_179_, lean_object* v_n_180_, lean_object* v_Z_u2081_181_, lean_object* v_Z_u2082_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lp_CORALean_CORALean_Float_Zonotope_linComb___redArg(v_inst_179_, v_n_180_, v_Z_u2081_181_, v_Z_u2082_182_);
return v___x_183_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Zonotope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Operations_LinComb(uint8_t builtin) {
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
