// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Float.Operations.Reduce
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
lean_object* lp_CORALean_CORALean_Float_absolute___redArg(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_sumUp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_maximumOver___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_subDown___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Partition_split(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_sortPerm(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_finCongr(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Partition_reindex___redArg(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Partition_left___redArg(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_radius___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_diagonalBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_addCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Partition_right___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceGirard___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceGirard___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceGirard(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceGirard___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduce___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduce___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg___lam__0(lean_object* v_part_1_, lean_object* v_G_2_, lean_object* v_i_3_, lean_object* v_l_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lp_CORALean_CORALean_Partition_right___redArg(v_part_1_, v_l_4_);
v___x_6_ = lean_apply_2(v_G_2_, v_i_3_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg___lam__1(lean_object* v_part_7_, lean_object* v_G_8_, lean_object* v_i_9_, lean_object* v_l_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lp_CORALean_CORALean_Partition_left___redArg(v_part_7_, v_l_10_);
v___x_12_ = lean_apply_2(v_G_8_, v_i_9_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg___lam__2(lean_object* v_part_13_, lean_object* v_G_14_, lean_object* v_inst_15_, lean_object* v_n_16_, lean_object* v_r_17_, lean_object* v___f_18_, lean_object* v_q_19_, lean_object* v_i_20_, lean_object* v___y_21_){
_start:
{
lean_object* v___f_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
lean_inc(v_i_20_);
v___f_22_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg___lam__1), 4, 3);
lean_closure_set(v___f_22_, 0, v_part_13_);
lean_closure_set(v___f_22_, 1, v_G_14_);
lean_closure_set(v___f_22_, 2, v_i_20_);
lean_inc(v_n_16_);
lean_inc_ref(v_inst_15_);
v___x_23_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_radius___boxed), 6, 5);
lean_closure_set(v___x_23_, 0, lean_box(0));
lean_closure_set(v___x_23_, 1, v_inst_15_);
lean_closure_set(v___x_23_, 2, v_n_16_);
lean_closure_set(v___x_23_, 3, v_r_17_);
lean_closure_set(v___x_23_, 4, v___f_18_);
v___x_24_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_diagonalBlock___boxed), 6, 5);
lean_closure_set(v___x_24_, 0, lean_box(0));
lean_closure_set(v___x_24_, 1, v_inst_15_);
lean_closure_set(v___x_24_, 2, v_n_16_);
lean_closure_set(v___x_24_, 3, v___x_23_);
lean_closure_set(v___x_24_, 4, v_i_20_);
v___x_25_ = l_Fin_addCases___redArg(v_q_19_, v___f_22_, v___x_24_, v___y_21_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg___lam__2___boxed(lean_object* v_part_26_, lean_object* v_G_27_, lean_object* v_inst_28_, lean_object* v_n_29_, lean_object* v_r_30_, lean_object* v___f_31_, lean_object* v_q_32_, lean_object* v_i_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg___lam__2(v_part_26_, v_G_27_, v_inst_28_, v_n_29_, v_r_30_, v___f_31_, v_q_32_, v_i_33_, v___y_34_);
lean_dec(v_q_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg(lean_object* v_inst_36_, lean_object* v_n_37_, lean_object* v_q_38_, lean_object* v_r_39_, lean_object* v_Z_40_, lean_object* v_part_41_){
_start:
{
lean_object* v_c_42_; lean_object* v_G_43_; lean_object* v_E_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_54_; 
v_c_42_ = lean_ctor_get(v_Z_40_, 1);
v_G_43_ = lean_ctor_get(v_Z_40_, 2);
v_E_44_ = lean_ctor_get(v_Z_40_, 3);
v_isSharedCheck_54_ = !lean_is_exclusive(v_Z_40_);
if (v_isSharedCheck_54_ == 0)
{
lean_object* v_unused_55_; 
v_unused_55_ = lean_ctor_get(v_Z_40_, 0);
lean_dec(v_unused_55_);
v___x_46_ = v_Z_40_;
v_isShared_47_ = v_isSharedCheck_54_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_E_44_);
lean_inc(v_G_43_);
lean_inc(v_c_42_);
lean_dec(v_Z_40_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_54_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___f_48_; lean_object* v___f_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
lean_inc(v_G_43_);
lean_inc_ref(v_part_41_);
v___f_48_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg___lam__0), 4, 2);
lean_closure_set(v___f_48_, 0, v_part_41_);
lean_closure_set(v___f_48_, 1, v_G_43_);
lean_inc(v_q_38_);
lean_inc(v_n_37_);
v___f_49_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_49_, 0, v_part_41_);
lean_closure_set(v___f_49_, 1, v_G_43_);
lean_closure_set(v___f_49_, 2, v_inst_36_);
lean_closure_set(v___f_49_, 3, v_n_37_);
lean_closure_set(v___f_49_, 4, v_r_39_);
lean_closure_set(v___f_49_, 5, v___f_48_);
lean_closure_set(v___f_49_, 6, v_q_38_);
v___x_50_ = lean_nat_add(v_q_38_, v_n_37_);
lean_dec(v_n_37_);
lean_dec(v_q_38_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 2, v___f_49_);
lean_ctor_set(v___x_46_, 0, v___x_50_);
v___x_52_ = v___x_46_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_c_42_);
lean_ctor_set(v_reuseFailAlloc_53_, 2, v___f_49_);
lean_ctor_set(v_reuseFailAlloc_53_, 3, v_E_44_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceBy(lean_object* v_00_U0001d54b_56_, lean_object* v_inst_57_, lean_object* v_n_58_, lean_object* v_q_59_, lean_object* v_r_60_, lean_object* v_Z_61_, lean_object* v_part_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg(v_inst_57_, v_n_58_, v_q_59_, v_r_60_, v_Z_61_, v_part_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___redArg___lam__0(lean_object* v_Z_64_, lean_object* v_j_65_, lean_object* v_inst_66_, lean_object* v_i_67_){
_start:
{
lean_object* v_G_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_G_68_ = lean_ctor_get(v_Z_64_, 2);
lean_inc(v_G_68_);
lean_dec_ref(v_Z_64_);
v___x_69_ = lean_apply_2(v_G_68_, v_i_67_, v_j_65_);
v___x_70_ = lp_CORALean_CORALean_Float_absolute___redArg(v_inst_66_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___redArg(lean_object* v_inst_71_, lean_object* v_n_72_, lean_object* v_Z_73_, lean_object* v_j_74_){
_start:
{
lean_object* v___f_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
lean_inc_ref_n(v_inst_71_, 3);
v___f_75_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___redArg___lam__0), 4, 3);
lean_closure_set(v___f_75_, 0, v_Z_73_);
lean_closure_set(v___f_75_, 1, v_j_74_);
lean_closure_set(v___f_75_, 2, v_inst_71_);
lean_inc_ref(v___f_75_);
v___x_76_ = lp_CORALean_CORALean_Float_sumUp___redArg(v_inst_71_, v_n_72_, v___f_75_);
v___x_77_ = lp_CORALean_CORALean_Float_maximumOver___redArg(v_inst_71_, v_n_72_, v___f_75_);
v___x_78_ = lp_CORALean_CORALean_Float_subDown___redArg(v_inst_71_, v___x_76_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___redArg___boxed(lean_object* v_inst_79_, lean_object* v_n_80_, lean_object* v_Z_81_, lean_object* v_j_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___redArg(v_inst_79_, v_n_80_, v_Z_81_, v_j_82_);
lean_dec(v_n_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric(lean_object* v_00_U0001d54b_84_, lean_object* v_inst_85_, lean_object* v_n_86_, lean_object* v_Z_87_, lean_object* v_j_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___redArg(v_inst_85_, v_n_86_, v_Z_87_, v_j_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___boxed(lean_object* v_00_U0001d54b_90_, lean_object* v_inst_91_, lean_object* v_n_92_, lean_object* v_Z_93_, lean_object* v_j_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric(v_00_U0001d54b_90_, v_inst_91_, v_n_92_, v_Z_93_, v_j_94_);
lean_dec(v_n_92_);
return v_res_95_;
}
}
LEAN_EXPORT uint8_t lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg___lam__0(lean_object* v_inst_96_, lean_object* v_n_97_, lean_object* v_Z_98_, lean_object* v_j_u2081_99_, lean_object* v_j_u2082_100_){
_start:
{
lean_object* v_le_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_le_101_ = lean_ctor_get(v_inst_96_, 8);
lean_inc_ref(v_le_101_);
lean_inc_ref(v_Z_98_);
lean_inc_ref(v_inst_96_);
v___x_102_ = lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___redArg(v_inst_96_, v_n_97_, v_Z_98_, v_j_u2082_100_);
v___x_103_ = lp_CORALean_CORALean_Float_Zonotope_aux__girardMetric___redArg(v_inst_96_, v_n_97_, v_Z_98_, v_j_u2081_99_);
v___x_104_ = lean_apply_2(v_le_101_, v___x_102_, v___x_103_);
v___x_105_ = lean_unbox(v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg___lam__0___boxed(lean_object* v_inst_106_, lean_object* v_n_107_, lean_object* v_Z_108_, lean_object* v_j_u2081_109_, lean_object* v_j_u2082_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg___lam__0(v_inst_106_, v_n_107_, v_Z_108_, v_j_u2081_109_, v_j_u2082_110_);
lean_dec(v_n_107_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg(lean_object* v_inst_113_, lean_object* v_n_114_, lean_object* v_Z_115_, lean_object* v_o_116_){
_start:
{
lean_object* v_h_117_; lean_object* v___f_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_h_117_ = lean_ctor_get(v_Z_115_, 0);
lean_inc_n(v_h_117_, 2);
lean_inc(v_n_114_);
v___f_118_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_118_, 0, v_inst_113_);
lean_closure_set(v___f_118_, 1, v_n_114_);
lean_closure_set(v___f_118_, 2, v_Z_115_);
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_sub(v_o_116_, v___x_119_);
v___x_121_ = lean_nat_mul(v___x_120_, v_n_114_);
lean_dec(v_n_114_);
lean_dec(v___x_120_);
v___x_122_ = lean_nat_sub(v_h_117_, v___x_121_);
lean_inc(v___x_122_);
lean_inc(v___x_121_);
v___x_123_ = lp_CORALean_CORALean_Partition_split(v___x_121_, v___x_122_);
v___x_124_ = lp_CORALean_CORALean_sortPerm(v_h_117_, v___f_118_);
v___x_125_ = lp_mathlib_Equiv_symm___redArg(v___x_124_);
v___x_126_ = lean_nat_add(v___x_121_, v___x_122_);
lean_dec(v___x_122_);
lean_dec(v___x_121_);
v___x_127_ = lp_mathlib_finCongr(v_h_117_, v___x_126_, lean_box(0));
lean_dec(v___x_126_);
lean_dec(v_h_117_);
v___x_128_ = lp_mathlib_Equiv_trans___redArg(v___x_125_, v___x_127_);
v___x_129_ = lp_CORALean_CORALean_Partition_reindex___redArg(v___x_123_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg___boxed(lean_object* v_inst_130_, lean_object* v_n_131_, lean_object* v_Z_132_, lean_object* v_o_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg(v_inst_130_, v_n_131_, v_Z_132_, v_o_133_);
lean_dec(v_o_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit(lean_object* v_00_U0001d54b_135_, lean_object* v_inst_136_, lean_object* v_n_137_, lean_object* v_Z_138_, lean_object* v_o_139_, lean_object* v_hlt_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg(v_inst_136_, v_n_137_, v_Z_138_, v_o_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___boxed(lean_object* v_00_U0001d54b_142_, lean_object* v_inst_143_, lean_object* v_n_144_, lean_object* v_Z_145_, lean_object* v_o_146_, lean_object* v_hlt_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit(v_00_U0001d54b_142_, v_inst_143_, v_n_144_, v_Z_145_, v_o_146_, v_hlt_147_);
lean_dec(v_o_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceGirard___redArg(lean_object* v_inst_149_, lean_object* v_n_150_, lean_object* v_Z_151_, lean_object* v_o_152_){
_start:
{
lean_object* v_h_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v_h_153_ = lean_ctor_get(v_Z_151_, 0);
v___x_154_ = lean_nat_mul(v_o_152_, v_n_150_);
v___x_155_ = lean_nat_dec_lt(v___x_154_, v_h_153_);
lean_dec(v___x_154_);
if (v___x_155_ == 0)
{
lean_dec(v_n_150_);
lean_dec_ref(v_inst_149_);
return v_Z_151_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = lean_nat_sub(v_o_152_, v___x_156_);
v___x_158_ = lean_nat_mul(v___x_157_, v_n_150_);
lean_dec(v___x_157_);
v___x_159_ = lean_nat_sub(v_h_153_, v___x_158_);
lean_inc_ref(v_Z_151_);
lean_inc(v_n_150_);
lean_inc_ref(v_inst_149_);
v___x_160_ = lp_CORALean_CORALean_Float_Zonotope_aux__girardSplit___redArg(v_inst_149_, v_n_150_, v_Z_151_, v_o_152_);
v___x_161_ = lp_CORALean_CORALean_Float_Zonotope_reduceBy___redArg(v_inst_149_, v_n_150_, v___x_158_, v___x_159_, v_Z_151_, v___x_160_);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceGirard___redArg___boxed(lean_object* v_inst_162_, lean_object* v_n_163_, lean_object* v_Z_164_, lean_object* v_o_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = lp_CORALean_CORALean_Float_Zonotope_reduceGirard___redArg(v_inst_162_, v_n_163_, v_Z_164_, v_o_165_);
lean_dec(v_o_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceGirard(lean_object* v_00_U0001d54b_167_, lean_object* v_inst_168_, lean_object* v_n_169_, lean_object* v_Z_170_, lean_object* v_o_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lp_CORALean_CORALean_Float_Zonotope_reduceGirard___redArg(v_inst_168_, v_n_169_, v_Z_170_, v_o_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceGirard___boxed(lean_object* v_00_U0001d54b_173_, lean_object* v_inst_174_, lean_object* v_n_175_, lean_object* v_Z_176_, lean_object* v_o_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = lp_CORALean_CORALean_Float_Zonotope_reduceGirard(v_00_U0001d54b_173_, v_inst_174_, v_n_175_, v_Z_176_, v_o_177_);
lean_dec(v_o_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduce___redArg(lean_object* v_inst_179_, lean_object* v_n_180_, lean_object* v_Z_181_, lean_object* v_o_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lp_CORALean_CORALean_Float_Zonotope_reduceGirard___redArg(v_inst_179_, v_n_180_, v_Z_181_, v_o_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduce___redArg___boxed(lean_object* v_inst_184_, lean_object* v_n_185_, lean_object* v_Z_186_, lean_object* v_o_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = lp_CORALean_CORALean_Float_Zonotope_reduce___redArg(v_inst_184_, v_n_185_, v_Z_186_, v_o_187_);
lean_dec(v_o_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduce(lean_object* v_00_U0001d54b_189_, lean_object* v_inst_190_, lean_object* v_n_191_, lean_object* v_Z_192_, lean_object* v_o_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lp_CORALean_CORALean_Float_Zonotope_reduceGirard___redArg(v_inst_190_, v_n_191_, v_Z_192_, v_o_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduce___boxed(lean_object* v_00_U0001d54b_195_, lean_object* v_inst_196_, lean_object* v_n_197_, lean_object* v_Z_198_, lean_object* v_o_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = lp_CORALean_CORALean_Float_Zonotope_reduce(v_00_U0001d54b_195_, v_inst_196_, v_n_197_, v_Z_198_, v_o_199_);
lean_dec(v_o_199_);
return v_res_200_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Zonotope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Operations_Reduce(uint8_t builtin) {
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
