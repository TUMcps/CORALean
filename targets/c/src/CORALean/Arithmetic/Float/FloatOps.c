// Lean compiler output
// Module: CORALean.Arithmetic.Float.FloatOps
// Imports: public import Init public meta import Init public import CORALean.Global.API
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Fin_succ___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_subUp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_subUp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_subDown___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_subDown(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumUp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumDown___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumDown___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumDown(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_absolute___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_absolute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotDown___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotDown___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotDown___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotUp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotUp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotUp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_radius___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_radius___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_radius___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_radius(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_radius___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_subUp___redArg(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
lean_object* v_neg_4_; lean_object* v_addUp_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_neg_4_ = lean_ctor_get(v_inst_1_, 1);
lean_inc(v_neg_4_);
v_addUp_5_ = lean_ctor_get(v_inst_1_, 2);
lean_inc(v_addUp_5_);
lean_dec_ref(v_inst_1_);
v___x_6_ = lean_apply_1(v_neg_4_, v_b_3_);
v___x_7_ = lean_apply_2(v_addUp_5_, v_a_2_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_subUp(lean_object* v_F_8_, lean_object* v_inst_9_, lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_CORALean_CORALean_Arithmetic_Float_subUp___redArg(v_inst_9_, v_a_10_, v_b_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_subDown___redArg(lean_object* v_inst_13_, lean_object* v_a_14_, lean_object* v_b_15_){
_start:
{
lean_object* v_neg_16_; lean_object* v_addDown_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_neg_16_ = lean_ctor_get(v_inst_13_, 1);
lean_inc(v_neg_16_);
v_addDown_17_ = lean_ctor_get(v_inst_13_, 3);
lean_inc(v_addDown_17_);
lean_dec_ref(v_inst_13_);
v___x_18_ = lean_apply_1(v_neg_16_, v_b_15_);
v___x_19_ = lean_apply_2(v_addDown_17_, v_a_14_, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_subDown(lean_object* v_F_20_, lean_object* v_inst_21_, lean_object* v_a_22_, lean_object* v_b_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_CORALean_CORALean_Arithmetic_Float_subDown___redArg(v_inst_21_, v_a_22_, v_b_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg___lam__0(lean_object* v_x_25_, lean_object* v_i_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = l_Fin_succ___redArg(v_i_26_);
v___x_28_ = lean_apply_1(v_x_25_, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg___lam__0___boxed(lean_object* v_x_29_, lean_object* v_i_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg___lam__0(v_x_29_, v_i_30_);
lean_dec(v_i_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg(lean_object* v_inst_32_, lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_zero_35_; uint8_t v_isZero_36_; 
v_zero_35_ = lean_unsigned_to_nat(0u);
v_isZero_36_ = lean_nat_dec_eq(v_x_33_, v_zero_35_);
if (v_isZero_36_ == 1)
{
lean_object* v_zero_37_; 
lean_dec(v_x_34_);
v_zero_37_ = lean_ctor_get(v_inst_32_, 0);
lean_inc(v_zero_37_);
lean_dec_ref(v_inst_32_);
return v_zero_37_;
}
else
{
lean_object* v_addUp_38_; lean_object* v___f_39_; lean_object* v_one_40_; lean_object* v_n_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_addUp_38_ = lean_ctor_get(v_inst_32_, 2);
lean_inc(v_addUp_38_);
lean_inc(v_x_34_);
v___f_39_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_39_, 0, v_x_34_);
v_one_40_ = lean_unsigned_to_nat(1u);
v_n_41_ = lean_nat_sub(v_x_33_, v_one_40_);
v___x_42_ = lean_nat_add(v_n_41_, v_one_40_);
v___x_43_ = lean_nat_mod(v_zero_35_, v___x_42_);
lean_dec(v___x_42_);
v___x_44_ = lean_apply_1(v_x_34_, v___x_43_);
v___x_45_ = lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg(v_inst_32_, v_n_41_, v___f_39_);
lean_dec(v_n_41_);
v___x_46_ = lean_apply_2(v_addUp_38_, v___x_44_, v___x_45_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg___boxed(lean_object* v_inst_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg(v_inst_47_, v_x_48_, v_x_49_);
lean_dec(v_x_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumUp(lean_object* v_F_51_, lean_object* v_inst_52_, lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg(v_inst_52_, v_x_53_, v_x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumUp___boxed(lean_object* v_F_56_, lean_object* v_inst_57_, lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_CORALean_CORALean_Arithmetic_Float_sumUp(v_F_56_, v_inst_57_, v_x_58_, v_x_59_);
lean_dec(v_x_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumDown___redArg(lean_object* v_inst_61_, lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
lean_object* v_zero_64_; uint8_t v_isZero_65_; 
v_zero_64_ = lean_unsigned_to_nat(0u);
v_isZero_65_ = lean_nat_dec_eq(v_x_62_, v_zero_64_);
if (v_isZero_65_ == 1)
{
lean_object* v_zero_66_; 
lean_dec(v_x_63_);
v_zero_66_ = lean_ctor_get(v_inst_61_, 0);
lean_inc(v_zero_66_);
lean_dec_ref(v_inst_61_);
return v_zero_66_;
}
else
{
lean_object* v_addDown_67_; lean_object* v___f_68_; lean_object* v_one_69_; lean_object* v_n_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_addDown_67_ = lean_ctor_get(v_inst_61_, 3);
lean_inc(v_addDown_67_);
lean_inc(v_x_63_);
v___f_68_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_68_, 0, v_x_63_);
v_one_69_ = lean_unsigned_to_nat(1u);
v_n_70_ = lean_nat_sub(v_x_62_, v_one_69_);
v___x_71_ = lean_nat_add(v_n_70_, v_one_69_);
v___x_72_ = lean_nat_mod(v_zero_64_, v___x_71_);
lean_dec(v___x_71_);
v___x_73_ = lean_apply_1(v_x_63_, v___x_72_);
v___x_74_ = lp_CORALean_CORALean_Arithmetic_Float_sumDown___redArg(v_inst_61_, v_n_70_, v___f_68_);
lean_dec(v_n_70_);
v___x_75_ = lean_apply_2(v_addDown_67_, v___x_73_, v___x_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumDown___redArg___boxed(lean_object* v_inst_76_, lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_CORALean_CORALean_Arithmetic_Float_sumDown___redArg(v_inst_76_, v_x_77_, v_x_78_);
lean_dec(v_x_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumDown(lean_object* v_F_80_, lean_object* v_inst_81_, lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lp_CORALean_CORALean_Arithmetic_Float_sumDown___redArg(v_inst_81_, v_x_82_, v_x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_sumDown___boxed(lean_object* v_F_85_, lean_object* v_inst_86_, lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = lp_CORALean_CORALean_Arithmetic_Float_sumDown(v_F_85_, v_inst_86_, v_x_87_, v_x_88_);
lean_dec(v_x_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_absolute___redArg(lean_object* v_inst_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_neg_92_; lean_object* v_maximum_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_neg_92_ = lean_ctor_get(v_inst_90_, 1);
lean_inc(v_neg_92_);
v_maximum_93_ = lean_ctor_get(v_inst_90_, 7);
lean_inc(v_maximum_93_);
lean_dec_ref(v_inst_90_);
lean_inc(v_a_91_);
v___x_94_ = lean_apply_1(v_neg_92_, v_a_91_);
v___x_95_ = lean_apply_2(v_maximum_93_, v_a_91_, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_absolute(lean_object* v_F_96_, lean_object* v_inst_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lp_CORALean_CORALean_Arithmetic_Float_absolute___redArg(v_inst_97_, v_a_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotDown___redArg___lam__0(lean_object* v_inst_100_, lean_object* v_a_101_, lean_object* v_b_102_, lean_object* v_k_103_){
_start:
{
lean_object* v_mulDown_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_mulDown_104_ = lean_ctor_get(v_inst_100_, 5);
lean_inc(v_mulDown_104_);
lean_dec_ref(v_inst_100_);
lean_inc(v_k_103_);
v___x_105_ = lean_apply_1(v_a_101_, v_k_103_);
v___x_106_ = lean_apply_1(v_b_102_, v_k_103_);
v___x_107_ = lean_apply_2(v_mulDown_104_, v___x_105_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotDown___redArg(lean_object* v_inst_108_, lean_object* v_n_109_, lean_object* v_a_110_, lean_object* v_b_111_){
_start:
{
lean_object* v___f_112_; lean_object* v___x_113_; 
lean_inc_ref(v_inst_108_);
v___f_112_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Arithmetic_Float_dotDown___redArg___lam__0), 4, 3);
lean_closure_set(v___f_112_, 0, v_inst_108_);
lean_closure_set(v___f_112_, 1, v_a_110_);
lean_closure_set(v___f_112_, 2, v_b_111_);
v___x_113_ = lp_CORALean_CORALean_Arithmetic_Float_sumDown___redArg(v_inst_108_, v_n_109_, v___f_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotDown___redArg___boxed(lean_object* v_inst_114_, lean_object* v_n_115_, lean_object* v_a_116_, lean_object* v_b_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_CORALean_CORALean_Arithmetic_Float_dotDown___redArg(v_inst_114_, v_n_115_, v_a_116_, v_b_117_);
lean_dec(v_n_115_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotDown(lean_object* v_F_119_, lean_object* v_inst_120_, lean_object* v_n_121_, lean_object* v_a_122_, lean_object* v_b_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lp_CORALean_CORALean_Arithmetic_Float_dotDown___redArg(v_inst_120_, v_n_121_, v_a_122_, v_b_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotDown___boxed(lean_object* v_F_125_, lean_object* v_inst_126_, lean_object* v_n_127_, lean_object* v_a_128_, lean_object* v_b_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = lp_CORALean_CORALean_Arithmetic_Float_dotDown(v_F_125_, v_inst_126_, v_n_127_, v_a_128_, v_b_129_);
lean_dec(v_n_127_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotUp___redArg___lam__0(lean_object* v_inst_131_, lean_object* v_a_132_, lean_object* v_b_133_, lean_object* v_k_134_){
_start:
{
lean_object* v_mulUp_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_mulUp_135_ = lean_ctor_get(v_inst_131_, 4);
lean_inc(v_mulUp_135_);
lean_dec_ref(v_inst_131_);
lean_inc(v_k_134_);
v___x_136_ = lean_apply_1(v_a_132_, v_k_134_);
v___x_137_ = lean_apply_1(v_b_133_, v_k_134_);
v___x_138_ = lean_apply_2(v_mulUp_135_, v___x_136_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotUp___redArg(lean_object* v_inst_139_, lean_object* v_n_140_, lean_object* v_a_141_, lean_object* v_b_142_){
_start:
{
lean_object* v___f_143_; lean_object* v___x_144_; 
lean_inc_ref(v_inst_139_);
v___f_143_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Arithmetic_Float_dotUp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_143_, 0, v_inst_139_);
lean_closure_set(v___f_143_, 1, v_a_141_);
lean_closure_set(v___f_143_, 2, v_b_142_);
v___x_144_ = lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg(v_inst_139_, v_n_140_, v___f_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotUp___redArg___boxed(lean_object* v_inst_145_, lean_object* v_n_146_, lean_object* v_a_147_, lean_object* v_b_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = lp_CORALean_CORALean_Arithmetic_Float_dotUp___redArg(v_inst_145_, v_n_146_, v_a_147_, v_b_148_);
lean_dec(v_n_146_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotUp(lean_object* v_F_150_, lean_object* v_inst_151_, lean_object* v_n_152_, lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lp_CORALean_CORALean_Arithmetic_Float_dotUp___redArg(v_inst_151_, v_n_152_, v_a_153_, v_b_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_dotUp___boxed(lean_object* v_F_156_, lean_object* v_inst_157_, lean_object* v_n_158_, lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = lp_CORALean_CORALean_Arithmetic_Float_dotUp(v_F_156_, v_inst_157_, v_n_158_, v_a_159_, v_b_160_);
lean_dec(v_n_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_radius___redArg___lam__0(lean_object* v_G_162_, lean_object* v_i_163_, lean_object* v_inst_164_, lean_object* v_j_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_apply_2(v_G_162_, v_i_163_, v_j_165_);
v___x_167_ = lp_CORALean_CORALean_Arithmetic_Float_absolute___redArg(v_inst_164_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_radius___redArg(lean_object* v_inst_168_, lean_object* v_h_169_, lean_object* v_G_170_, lean_object* v_i_171_){
_start:
{
lean_object* v___f_172_; lean_object* v___x_173_; 
lean_inc_ref(v_inst_168_);
v___f_172_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Arithmetic_Float_radius___redArg___lam__0), 4, 3);
lean_closure_set(v___f_172_, 0, v_G_170_);
lean_closure_set(v___f_172_, 1, v_i_171_);
lean_closure_set(v___f_172_, 2, v_inst_168_);
v___x_173_ = lp_CORALean_CORALean_Arithmetic_Float_sumUp___redArg(v_inst_168_, v_h_169_, v___f_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_radius___redArg___boxed(lean_object* v_inst_174_, lean_object* v_h_175_, lean_object* v_G_176_, lean_object* v_i_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = lp_CORALean_CORALean_Arithmetic_Float_radius___redArg(v_inst_174_, v_h_175_, v_G_176_, v_i_177_);
lean_dec(v_h_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_radius(lean_object* v_F_179_, lean_object* v_inst_180_, lean_object* v_n_181_, lean_object* v_h_182_, lean_object* v_G_183_, lean_object* v_i_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lp_CORALean_CORALean_Arithmetic_Float_radius___redArg(v_inst_180_, v_h_182_, v_G_183_, v_i_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_radius___boxed(lean_object* v_F_186_, lean_object* v_inst_187_, lean_object* v_n_188_, lean_object* v_h_189_, lean_object* v_G_190_, lean_object* v_i_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = lp_CORALean_CORALean_Arithmetic_Float_radius(v_F_186_, v_inst_187_, v_n_188_, v_h_189_, v_G_190_, v_i_191_);
lean_dec(v_h_189_);
lean_dec(v_n_188_);
return v_res_192_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Global_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Arithmetic_Float_FloatOps(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Global_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
