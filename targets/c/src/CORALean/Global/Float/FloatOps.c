// Lean compiler output
// Module: CORALean.Global.Float.FloatOps
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_subUp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_subUp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_subDown___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_subDown(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumUp___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumUp___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumUp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumUp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumUp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumDown___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumDown___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumDown(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_maximumOver___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_maximumOver___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_maximumOver(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_maximumOver___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_absolute___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_absolute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotDown___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotDown___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotDown___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotUp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotUp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotUp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_radius___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_radius___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_radius___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_radius(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_radius___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_diagonalBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_diagonalBlock___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_diagonalBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_diagonalBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecDown___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecDown___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecUp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecUp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDown___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDown___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDown___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulUp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulUp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDiff___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDiff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDiff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_subUp___redArg(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_){
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_subUp(lean_object* v_00_U0001d54b_8_, lean_object* v_inst_9_, lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_CORALean_CORALean_Float_subUp___redArg(v_inst_9_, v_a_10_, v_b_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_subDown___redArg(lean_object* v_inst_13_, lean_object* v_a_14_, lean_object* v_b_15_){
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_subDown(lean_object* v_00_U0001d54b_20_, lean_object* v_inst_21_, lean_object* v_a_22_, lean_object* v_b_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_CORALean_CORALean_Float_subDown___redArg(v_inst_21_, v_a_22_, v_b_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumUp___redArg___lam__0(lean_object* v_x_25_, lean_object* v_i_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = l_Fin_succ___redArg(v_i_26_);
v___x_28_ = lean_apply_1(v_x_25_, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumUp___redArg___lam__0___boxed(lean_object* v_x_29_, lean_object* v_i_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_CORALean_CORALean_Float_sumUp___redArg___lam__0(v_x_29_, v_i_30_);
lean_dec(v_i_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumUp___redArg(lean_object* v_inst_32_, lean_object* v_x_33_, lean_object* v_x_34_){
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
v___f_39_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_sumUp___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_39_, 0, v_x_34_);
v_one_40_ = lean_unsigned_to_nat(1u);
v_n_41_ = lean_nat_sub(v_x_33_, v_one_40_);
v___x_42_ = lean_nat_add(v_n_41_, v_one_40_);
v___x_43_ = lean_nat_mod(v_zero_35_, v___x_42_);
lean_dec(v___x_42_);
v___x_44_ = lean_apply_1(v_x_34_, v___x_43_);
v___x_45_ = lp_CORALean_CORALean_Float_sumUp___redArg(v_inst_32_, v_n_41_, v___f_39_);
lean_dec(v_n_41_);
v___x_46_ = lean_apply_2(v_addUp_38_, v___x_44_, v___x_45_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumUp___redArg___boxed(lean_object* v_inst_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_CORALean_CORALean_Float_sumUp___redArg(v_inst_47_, v_x_48_, v_x_49_);
lean_dec(v_x_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumUp(lean_object* v_00_U0001d54b_51_, lean_object* v_inst_52_, lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_CORALean_CORALean_Float_sumUp___redArg(v_inst_52_, v_x_53_, v_x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumUp___boxed(lean_object* v_00_U0001d54b_56_, lean_object* v_inst_57_, lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_CORALean_CORALean_Float_sumUp(v_00_U0001d54b_56_, v_inst_57_, v_x_58_, v_x_59_);
lean_dec(v_x_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumDown___redArg(lean_object* v_inst_61_, lean_object* v_x_62_, lean_object* v_x_63_){
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
v___f_68_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_sumUp___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_68_, 0, v_x_63_);
v_one_69_ = lean_unsigned_to_nat(1u);
v_n_70_ = lean_nat_sub(v_x_62_, v_one_69_);
v___x_71_ = lean_nat_add(v_n_70_, v_one_69_);
v___x_72_ = lean_nat_mod(v_zero_64_, v___x_71_);
lean_dec(v___x_71_);
v___x_73_ = lean_apply_1(v_x_63_, v___x_72_);
v___x_74_ = lp_CORALean_CORALean_Float_sumDown___redArg(v_inst_61_, v_n_70_, v___f_68_);
lean_dec(v_n_70_);
v___x_75_ = lean_apply_2(v_addDown_67_, v___x_73_, v___x_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumDown___redArg___boxed(lean_object* v_inst_76_, lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_CORALean_CORALean_Float_sumDown___redArg(v_inst_76_, v_x_77_, v_x_78_);
lean_dec(v_x_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumDown(lean_object* v_00_U0001d54b_80_, lean_object* v_inst_81_, lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lp_CORALean_CORALean_Float_sumDown___redArg(v_inst_81_, v_x_82_, v_x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_sumDown___boxed(lean_object* v_00_U0001d54b_85_, lean_object* v_inst_86_, lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = lp_CORALean_CORALean_Float_sumDown(v_00_U0001d54b_85_, v_inst_86_, v_x_87_, v_x_88_);
lean_dec(v_x_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_maximumOver___redArg(lean_object* v_inst_90_, lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
lean_object* v_zero_93_; uint8_t v_isZero_94_; 
v_zero_93_ = lean_unsigned_to_nat(0u);
v_isZero_94_ = lean_nat_dec_eq(v_x_91_, v_zero_93_);
if (v_isZero_94_ == 1)
{
lean_object* v_zero_95_; 
lean_dec(v_x_92_);
v_zero_95_ = lean_ctor_get(v_inst_90_, 0);
lean_inc(v_zero_95_);
lean_dec_ref(v_inst_90_);
return v_zero_95_;
}
else
{
lean_object* v_maximum_96_; lean_object* v___f_97_; lean_object* v_one_98_; lean_object* v_n_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_maximum_96_ = lean_ctor_get(v_inst_90_, 7);
lean_inc(v_maximum_96_);
lean_inc(v_x_92_);
v___f_97_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_sumUp___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_97_, 0, v_x_92_);
v_one_98_ = lean_unsigned_to_nat(1u);
v_n_99_ = lean_nat_sub(v_x_91_, v_one_98_);
v___x_100_ = lean_nat_add(v_n_99_, v_one_98_);
v___x_101_ = lean_nat_mod(v_zero_93_, v___x_100_);
lean_dec(v___x_100_);
v___x_102_ = lean_apply_1(v_x_92_, v___x_101_);
v___x_103_ = lp_CORALean_CORALean_Float_maximumOver___redArg(v_inst_90_, v_n_99_, v___f_97_);
lean_dec(v_n_99_);
v___x_104_ = lean_apply_2(v_maximum_96_, v___x_102_, v___x_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_maximumOver___redArg___boxed(lean_object* v_inst_105_, lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lp_CORALean_CORALean_Float_maximumOver___redArg(v_inst_105_, v_x_106_, v_x_107_);
lean_dec(v_x_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_maximumOver(lean_object* v_00_U0001d54b_109_, lean_object* v_inst_110_, lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lp_CORALean_CORALean_Float_maximumOver___redArg(v_inst_110_, v_x_111_, v_x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_maximumOver___boxed(lean_object* v_00_U0001d54b_114_, lean_object* v_inst_115_, lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_CORALean_CORALean_Float_maximumOver(v_00_U0001d54b_114_, v_inst_115_, v_x_116_, v_x_117_);
lean_dec(v_x_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_absolute___redArg(lean_object* v_inst_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_neg_121_; lean_object* v_maximum_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_neg_121_ = lean_ctor_get(v_inst_119_, 1);
lean_inc(v_neg_121_);
v_maximum_122_ = lean_ctor_get(v_inst_119_, 7);
lean_inc(v_maximum_122_);
lean_dec_ref(v_inst_119_);
lean_inc(v_a_120_);
v___x_123_ = lean_apply_1(v_neg_121_, v_a_120_);
v___x_124_ = lean_apply_2(v_maximum_122_, v_a_120_, v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_absolute(lean_object* v_00_U0001d54b_125_, lean_object* v_inst_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lp_CORALean_CORALean_Float_absolute___redArg(v_inst_126_, v_a_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotDown___redArg___lam__0(lean_object* v_inst_129_, lean_object* v_a_130_, lean_object* v_b_131_, lean_object* v_k_132_){
_start:
{
lean_object* v_mulDown_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_mulDown_133_ = lean_ctor_get(v_inst_129_, 5);
lean_inc(v_mulDown_133_);
lean_dec_ref(v_inst_129_);
lean_inc(v_k_132_);
v___x_134_ = lean_apply_1(v_a_130_, v_k_132_);
v___x_135_ = lean_apply_1(v_b_131_, v_k_132_);
v___x_136_ = lean_apply_2(v_mulDown_133_, v___x_134_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotDown___redArg(lean_object* v_inst_137_, lean_object* v_n_138_, lean_object* v_a_139_, lean_object* v_b_140_){
_start:
{
lean_object* v___f_141_; lean_object* v___x_142_; 
lean_inc_ref(v_inst_137_);
v___f_141_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_dotDown___redArg___lam__0), 4, 3);
lean_closure_set(v___f_141_, 0, v_inst_137_);
lean_closure_set(v___f_141_, 1, v_a_139_);
lean_closure_set(v___f_141_, 2, v_b_140_);
v___x_142_ = lp_CORALean_CORALean_Float_sumDown___redArg(v_inst_137_, v_n_138_, v___f_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotDown___redArg___boxed(lean_object* v_inst_143_, lean_object* v_n_144_, lean_object* v_a_145_, lean_object* v_b_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = lp_CORALean_CORALean_Float_dotDown___redArg(v_inst_143_, v_n_144_, v_a_145_, v_b_146_);
lean_dec(v_n_144_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotDown(lean_object* v_00_U0001d54b_148_, lean_object* v_inst_149_, lean_object* v_n_150_, lean_object* v_a_151_, lean_object* v_b_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lp_CORALean_CORALean_Float_dotDown___redArg(v_inst_149_, v_n_150_, v_a_151_, v_b_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotDown___boxed(lean_object* v_00_U0001d54b_154_, lean_object* v_inst_155_, lean_object* v_n_156_, lean_object* v_a_157_, lean_object* v_b_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = lp_CORALean_CORALean_Float_dotDown(v_00_U0001d54b_154_, v_inst_155_, v_n_156_, v_a_157_, v_b_158_);
lean_dec(v_n_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotUp___redArg___lam__0(lean_object* v_inst_160_, lean_object* v_a_161_, lean_object* v_b_162_, lean_object* v_k_163_){
_start:
{
lean_object* v_mulUp_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_mulUp_164_ = lean_ctor_get(v_inst_160_, 4);
lean_inc(v_mulUp_164_);
lean_dec_ref(v_inst_160_);
lean_inc(v_k_163_);
v___x_165_ = lean_apply_1(v_a_161_, v_k_163_);
v___x_166_ = lean_apply_1(v_b_162_, v_k_163_);
v___x_167_ = lean_apply_2(v_mulUp_164_, v___x_165_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotUp___redArg(lean_object* v_inst_168_, lean_object* v_n_169_, lean_object* v_a_170_, lean_object* v_b_171_){
_start:
{
lean_object* v___f_172_; lean_object* v___x_173_; 
lean_inc_ref(v_inst_168_);
v___f_172_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_dotUp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_172_, 0, v_inst_168_);
lean_closure_set(v___f_172_, 1, v_a_170_);
lean_closure_set(v___f_172_, 2, v_b_171_);
v___x_173_ = lp_CORALean_CORALean_Float_sumUp___redArg(v_inst_168_, v_n_169_, v___f_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotUp___redArg___boxed(lean_object* v_inst_174_, lean_object* v_n_175_, lean_object* v_a_176_, lean_object* v_b_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = lp_CORALean_CORALean_Float_dotUp___redArg(v_inst_174_, v_n_175_, v_a_176_, v_b_177_);
lean_dec(v_n_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotUp(lean_object* v_00_U0001d54b_179_, lean_object* v_inst_180_, lean_object* v_n_181_, lean_object* v_a_182_, lean_object* v_b_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lp_CORALean_CORALean_Float_dotUp___redArg(v_inst_180_, v_n_181_, v_a_182_, v_b_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_dotUp___boxed(lean_object* v_00_U0001d54b_185_, lean_object* v_inst_186_, lean_object* v_n_187_, lean_object* v_a_188_, lean_object* v_b_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = lp_CORALean_CORALean_Float_dotUp(v_00_U0001d54b_185_, v_inst_186_, v_n_187_, v_a_188_, v_b_189_);
lean_dec(v_n_187_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_radius___redArg___lam__0(lean_object* v_G_191_, lean_object* v_i_192_, lean_object* v_inst_193_, lean_object* v_j_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_apply_2(v_G_191_, v_i_192_, v_j_194_);
v___x_196_ = lp_CORALean_CORALean_Float_absolute___redArg(v_inst_193_, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_radius___redArg(lean_object* v_inst_197_, lean_object* v_h_198_, lean_object* v_G_199_, lean_object* v_i_200_){
_start:
{
lean_object* v___f_201_; lean_object* v___x_202_; 
lean_inc_ref(v_inst_197_);
v___f_201_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_radius___redArg___lam__0), 4, 3);
lean_closure_set(v___f_201_, 0, v_G_199_);
lean_closure_set(v___f_201_, 1, v_i_200_);
lean_closure_set(v___f_201_, 2, v_inst_197_);
v___x_202_ = lp_CORALean_CORALean_Float_sumUp___redArg(v_inst_197_, v_h_198_, v___f_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_radius___redArg___boxed(lean_object* v_inst_203_, lean_object* v_h_204_, lean_object* v_G_205_, lean_object* v_i_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = lp_CORALean_CORALean_Float_radius___redArg(v_inst_203_, v_h_204_, v_G_205_, v_i_206_);
lean_dec(v_h_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_radius(lean_object* v_00_U0001d54b_208_, lean_object* v_inst_209_, lean_object* v_n_210_, lean_object* v_h_211_, lean_object* v_G_212_, lean_object* v_i_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lp_CORALean_CORALean_Float_radius___redArg(v_inst_209_, v_h_211_, v_G_212_, v_i_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_radius___boxed(lean_object* v_00_U0001d54b_215_, lean_object* v_inst_216_, lean_object* v_n_217_, lean_object* v_h_218_, lean_object* v_G_219_, lean_object* v_i_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = lp_CORALean_CORALean_Float_radius(v_00_U0001d54b_215_, v_inst_216_, v_n_217_, v_h_218_, v_G_219_, v_i_220_);
lean_dec(v_h_218_);
lean_dec(v_n_217_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_diagonalBlock___redArg(lean_object* v_inst_222_, lean_object* v_v_223_, lean_object* v_i_224_, lean_object* v_l_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = lean_nat_dec_eq(v_i_224_, v_l_225_);
if (v___x_226_ == 0)
{
lean_object* v_zero_227_; 
lean_dec(v_i_224_);
lean_dec(v_v_223_);
v_zero_227_ = lean_ctor_get(v_inst_222_, 0);
lean_inc(v_zero_227_);
return v_zero_227_;
}
else
{
lean_object* v___x_228_; 
v___x_228_ = lean_apply_1(v_v_223_, v_i_224_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_diagonalBlock___redArg___boxed(lean_object* v_inst_229_, lean_object* v_v_230_, lean_object* v_i_231_, lean_object* v_l_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = lp_CORALean_CORALean_Float_diagonalBlock___redArg(v_inst_229_, v_v_230_, v_i_231_, v_l_232_);
lean_dec(v_l_232_);
lean_dec_ref(v_inst_229_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_diagonalBlock(lean_object* v_00_U0001d54b_234_, lean_object* v_inst_235_, lean_object* v_n_236_, lean_object* v_v_237_, lean_object* v_i_238_, lean_object* v_l_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lp_CORALean_CORALean_Float_diagonalBlock___redArg(v_inst_235_, v_v_237_, v_i_238_, v_l_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_diagonalBlock___boxed(lean_object* v_00_U0001d54b_241_, lean_object* v_inst_242_, lean_object* v_n_243_, lean_object* v_v_244_, lean_object* v_i_245_, lean_object* v_l_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = lp_CORALean_CORALean_Float_diagonalBlock(v_00_U0001d54b_241_, v_inst_242_, v_n_243_, v_v_244_, v_i_245_, v_l_246_);
lean_dec(v_l_246_);
lean_dec(v_n_243_);
lean_dec_ref(v_inst_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecDown___redArg(lean_object* v_inst_248_, lean_object* v_n_249_, lean_object* v_M_250_, lean_object* v_v_251_, lean_object* v_i_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_apply_1(v_M_250_, v_i_252_);
v___x_254_ = lp_CORALean_CORALean_Float_dotDown___redArg(v_inst_248_, v_n_249_, v___x_253_, v_v_251_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecDown___redArg___boxed(lean_object* v_inst_255_, lean_object* v_n_256_, lean_object* v_M_257_, lean_object* v_v_258_, lean_object* v_i_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = lp_CORALean_CORALean_Float_mulVecDown___redArg(v_inst_255_, v_n_256_, v_M_257_, v_v_258_, v_i_259_);
lean_dec(v_n_256_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecDown(lean_object* v_00_U0001d54b_261_, lean_object* v_inst_262_, lean_object* v_m_263_, lean_object* v_n_264_, lean_object* v_M_265_, lean_object* v_v_266_, lean_object* v_i_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lp_CORALean_CORALean_Float_mulVecDown___redArg(v_inst_262_, v_n_264_, v_M_265_, v_v_266_, v_i_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecDown___boxed(lean_object* v_00_U0001d54b_269_, lean_object* v_inst_270_, lean_object* v_m_271_, lean_object* v_n_272_, lean_object* v_M_273_, lean_object* v_v_274_, lean_object* v_i_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = lp_CORALean_CORALean_Float_mulVecDown(v_00_U0001d54b_269_, v_inst_270_, v_m_271_, v_n_272_, v_M_273_, v_v_274_, v_i_275_);
lean_dec(v_n_272_);
lean_dec(v_m_271_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecUp___redArg(lean_object* v_inst_277_, lean_object* v_n_278_, lean_object* v_M_279_, lean_object* v_v_280_, lean_object* v_i_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_apply_1(v_M_279_, v_i_281_);
v___x_283_ = lp_CORALean_CORALean_Float_dotUp___redArg(v_inst_277_, v_n_278_, v___x_282_, v_v_280_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecUp___redArg___boxed(lean_object* v_inst_284_, lean_object* v_n_285_, lean_object* v_M_286_, lean_object* v_v_287_, lean_object* v_i_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = lp_CORALean_CORALean_Float_mulVecUp___redArg(v_inst_284_, v_n_285_, v_M_286_, v_v_287_, v_i_288_);
lean_dec(v_n_285_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecUp(lean_object* v_00_U0001d54b_290_, lean_object* v_inst_291_, lean_object* v_m_292_, lean_object* v_n_293_, lean_object* v_M_294_, lean_object* v_v_295_, lean_object* v_i_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = lp_CORALean_CORALean_Float_mulVecUp___redArg(v_inst_291_, v_n_293_, v_M_294_, v_v_295_, v_i_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_mulVecUp___boxed(lean_object* v_00_U0001d54b_298_, lean_object* v_inst_299_, lean_object* v_m_300_, lean_object* v_n_301_, lean_object* v_M_302_, lean_object* v_v_303_, lean_object* v_i_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = lp_CORALean_CORALean_Float_mulVecUp(v_00_U0001d54b_298_, v_inst_299_, v_m_300_, v_n_301_, v_M_302_, v_v_303_, v_i_304_);
lean_dec(v_n_301_);
lean_dec(v_m_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDown___redArg___lam__0(lean_object* v_M_u2082_306_, lean_object* v_j_307_, lean_object* v_l_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = lean_apply_2(v_M_u2082_306_, v_l_308_, v_j_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDown___redArg(lean_object* v_inst_310_, lean_object* v_n_311_, lean_object* v_M_u2081_312_, lean_object* v_M_u2082_313_, lean_object* v_i_314_, lean_object* v_j_315_){
_start:
{
lean_object* v___f_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___f_316_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_matMulDown___redArg___lam__0), 3, 2);
lean_closure_set(v___f_316_, 0, v_M_u2082_313_);
lean_closure_set(v___f_316_, 1, v_j_315_);
v___x_317_ = lean_apply_1(v_M_u2081_312_, v_i_314_);
v___x_318_ = lp_CORALean_CORALean_Float_dotDown___redArg(v_inst_310_, v_n_311_, v___x_317_, v___f_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDown___redArg___boxed(lean_object* v_inst_319_, lean_object* v_n_320_, lean_object* v_M_u2081_321_, lean_object* v_M_u2082_322_, lean_object* v_i_323_, lean_object* v_j_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = lp_CORALean_CORALean_Float_matMulDown___redArg(v_inst_319_, v_n_320_, v_M_u2081_321_, v_M_u2082_322_, v_i_323_, v_j_324_);
lean_dec(v_n_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDown(lean_object* v_00_U0001d54b_326_, lean_object* v_inst_327_, lean_object* v_m_328_, lean_object* v_n_329_, lean_object* v_k_330_, lean_object* v_M_u2081_331_, lean_object* v_M_u2082_332_, lean_object* v_i_333_, lean_object* v_j_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lp_CORALean_CORALean_Float_matMulDown___redArg(v_inst_327_, v_n_329_, v_M_u2081_331_, v_M_u2082_332_, v_i_333_, v_j_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDown___boxed(lean_object* v_00_U0001d54b_336_, lean_object* v_inst_337_, lean_object* v_m_338_, lean_object* v_n_339_, lean_object* v_k_340_, lean_object* v_M_u2081_341_, lean_object* v_M_u2082_342_, lean_object* v_i_343_, lean_object* v_j_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = lp_CORALean_CORALean_Float_matMulDown(v_00_U0001d54b_336_, v_inst_337_, v_m_338_, v_n_339_, v_k_340_, v_M_u2081_341_, v_M_u2082_342_, v_i_343_, v_j_344_);
lean_dec(v_k_340_);
lean_dec(v_n_339_);
lean_dec(v_m_338_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulUp___redArg(lean_object* v_inst_346_, lean_object* v_n_347_, lean_object* v_M_u2081_348_, lean_object* v_M_u2082_349_, lean_object* v_i_350_, lean_object* v_j_351_){
_start:
{
lean_object* v___f_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___f_352_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_matMulDown___redArg___lam__0), 3, 2);
lean_closure_set(v___f_352_, 0, v_M_u2082_349_);
lean_closure_set(v___f_352_, 1, v_j_351_);
v___x_353_ = lean_apply_1(v_M_u2081_348_, v_i_350_);
v___x_354_ = lp_CORALean_CORALean_Float_dotUp___redArg(v_inst_346_, v_n_347_, v___x_353_, v___f_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulUp___redArg___boxed(lean_object* v_inst_355_, lean_object* v_n_356_, lean_object* v_M_u2081_357_, lean_object* v_M_u2082_358_, lean_object* v_i_359_, lean_object* v_j_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = lp_CORALean_CORALean_Float_matMulUp___redArg(v_inst_355_, v_n_356_, v_M_u2081_357_, v_M_u2082_358_, v_i_359_, v_j_360_);
lean_dec(v_n_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulUp(lean_object* v_00_U0001d54b_362_, lean_object* v_inst_363_, lean_object* v_m_364_, lean_object* v_n_365_, lean_object* v_k_366_, lean_object* v_M_u2081_367_, lean_object* v_M_u2082_368_, lean_object* v_i_369_, lean_object* v_j_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lp_CORALean_CORALean_Float_matMulUp___redArg(v_inst_363_, v_n_365_, v_M_u2081_367_, v_M_u2082_368_, v_i_369_, v_j_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulUp___boxed(lean_object* v_00_U0001d54b_372_, lean_object* v_inst_373_, lean_object* v_m_374_, lean_object* v_n_375_, lean_object* v_k_376_, lean_object* v_M_u2081_377_, lean_object* v_M_u2082_378_, lean_object* v_i_379_, lean_object* v_j_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = lp_CORALean_CORALean_Float_matMulUp(v_00_U0001d54b_372_, v_inst_373_, v_m_374_, v_n_375_, v_k_376_, v_M_u2081_377_, v_M_u2082_378_, v_i_379_, v_j_380_);
lean_dec(v_k_376_);
lean_dec(v_n_375_);
lean_dec(v_m_374_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDiff___redArg(lean_object* v_inst_382_, lean_object* v_n_383_, lean_object* v_M_u2081_384_, lean_object* v_M_u2082_385_, lean_object* v_i_386_, lean_object* v_j_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
lean_inc(v_j_387_);
lean_inc(v_i_386_);
lean_inc(v_M_u2082_385_);
lean_inc(v_M_u2081_384_);
lean_inc_ref_n(v_inst_382_, 2);
v___x_388_ = lp_CORALean_CORALean_Float_matMulUp___redArg(v_inst_382_, v_n_383_, v_M_u2081_384_, v_M_u2082_385_, v_i_386_, v_j_387_);
v___x_389_ = lp_CORALean_CORALean_Float_matMulDown___redArg(v_inst_382_, v_n_383_, v_M_u2081_384_, v_M_u2082_385_, v_i_386_, v_j_387_);
v___x_390_ = lp_CORALean_CORALean_Float_subUp___redArg(v_inst_382_, v___x_388_, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDiff___redArg___boxed(lean_object* v_inst_391_, lean_object* v_n_392_, lean_object* v_M_u2081_393_, lean_object* v_M_u2082_394_, lean_object* v_i_395_, lean_object* v_j_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = lp_CORALean_CORALean_Float_matMulDiff___redArg(v_inst_391_, v_n_392_, v_M_u2081_393_, v_M_u2082_394_, v_i_395_, v_j_396_);
lean_dec(v_n_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDiff(lean_object* v_00_U0001d54b_398_, lean_object* v_inst_399_, lean_object* v_m_400_, lean_object* v_n_401_, lean_object* v_k_402_, lean_object* v_M_u2081_403_, lean_object* v_M_u2082_404_, lean_object* v_i_405_, lean_object* v_j_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lp_CORALean_CORALean_Float_matMulDiff___redArg(v_inst_399_, v_n_401_, v_M_u2081_403_, v_M_u2082_404_, v_i_405_, v_j_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_matMulDiff___boxed(lean_object* v_00_U0001d54b_408_, lean_object* v_inst_409_, lean_object* v_m_410_, lean_object* v_n_411_, lean_object* v_k_412_, lean_object* v_M_u2081_413_, lean_object* v_M_u2082_414_, lean_object* v_i_415_, lean_object* v_j_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = lp_CORALean_CORALean_Float_matMulDiff(v_00_U0001d54b_408_, v_inst_409_, v_m_410_, v_n_411_, v_k_412_, v_M_u2081_413_, v_M_u2082_414_, v_i_415_, v_j_416_);
lean_dec(v_k_412_);
lean_dec(v_n_411_);
lean_dec(v_m_410_);
return v_res_417_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Global_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Global_Float_FloatOps(uint8_t builtin) {
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
