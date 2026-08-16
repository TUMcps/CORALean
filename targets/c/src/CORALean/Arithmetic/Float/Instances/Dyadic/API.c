// Lean compiler output
// Module: CORALean.Arithmetic.Float.Instances.Dyadic.API
// Imports: public import Init public meta import Init public import CORALean.Arithmetic.Float.SoundFloatArithmetic
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
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_log2(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_neg___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_neg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_neg___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_shift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_shift___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundDown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundDown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundUp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundUp___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half___redArg___closed__0;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_minimum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_minimum___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_minimum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_minimum___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_maximum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_maximum___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_maximum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_maximum___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_addUp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_addUp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_addDown(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_addDown___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_mulUp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_mulUp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_mulDown(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_mulDown___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_neg___redArg(lean_object* v_d_1_){
_start:
{
lean_object* v_mantissa_2_; lean_object* v_exponent_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_11_; 
v_mantissa_2_ = lean_ctor_get(v_d_1_, 0);
v_exponent_3_ = lean_ctor_get(v_d_1_, 1);
v_isSharedCheck_11_ = !lean_is_exclusive(v_d_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_5_ = v_d_1_;
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_exponent_3_);
lean_inc(v_mantissa_2_);
lean_dec(v_d_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_9_; 
v___x_7_ = lean_int_neg(v_mantissa_2_);
lean_dec(v_mantissa_2_);
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v___x_7_);
lean_ctor_set(v_reuseFailAlloc_10_, 1, v_exponent_3_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_neg(lean_object* v_p_12_, lean_object* v_d_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_neg___redArg(v_d_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_neg___boxed(lean_object* v_p_15_, lean_object* v_d_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_neg(v_p_15_, v_d_16_);
lean_dec(v_p_15_);
return v_res_17_;
}
}
static lean_object* _init_lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(2u);
v___x_19_ = lean_nat_to_int(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg(lean_object* v_a_20_, lean_object* v_b_21_){
_start:
{
lean_object* v_mantissa_22_; lean_object* v_exponent_23_; lean_object* v_mantissa_24_; lean_object* v_exponent_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_45_; 
v_mantissa_22_ = lean_ctor_get(v_a_20_, 0);
lean_inc(v_mantissa_22_);
v_exponent_23_ = lean_ctor_get(v_a_20_, 1);
lean_inc(v_exponent_23_);
lean_dec_ref(v_a_20_);
v_mantissa_24_ = lean_ctor_get(v_b_21_, 0);
v_exponent_25_ = lean_ctor_get(v_b_21_, 1);
v_isSharedCheck_45_ = !lean_is_exclusive(v_b_21_);
if (v_isSharedCheck_45_ == 0)
{
v___x_27_ = v_b_21_;
v_isShared_28_ = v_isSharedCheck_45_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_exponent_25_);
lean_inc(v_mantissa_24_);
lean_dec(v_b_21_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_45_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___y_30_; uint8_t v___x_44_; 
v___x_44_ = lean_int_dec_le(v_exponent_23_, v_exponent_25_);
if (v___x_44_ == 0)
{
lean_inc(v_exponent_25_);
v___y_30_ = v_exponent_25_;
goto v___jp_29_;
}
else
{
lean_inc(v_exponent_23_);
v___y_30_ = v_exponent_23_;
goto v___jp_29_;
}
v___jp_29_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_31_ = lean_obj_once(&lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0, &lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0_once, _init_lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0);
v___x_32_ = lean_int_sub(v_exponent_23_, v___y_30_);
lean_dec(v_exponent_23_);
v___x_33_ = l_Int_toNat(v___x_32_);
lean_dec(v___x_32_);
v___x_34_ = l_Int_pow(v___x_31_, v___x_33_);
lean_dec(v___x_33_);
v___x_35_ = lean_int_mul(v_mantissa_22_, v___x_34_);
lean_dec(v___x_34_);
lean_dec(v_mantissa_22_);
v___x_36_ = lean_int_sub(v_exponent_25_, v___y_30_);
lean_dec(v_exponent_25_);
v___x_37_ = l_Int_toNat(v___x_36_);
lean_dec(v___x_36_);
v___x_38_ = l_Int_pow(v___x_31_, v___x_37_);
lean_dec(v___x_37_);
v___x_39_ = lean_int_mul(v_mantissa_24_, v___x_38_);
lean_dec(v___x_38_);
lean_dec(v_mantissa_24_);
v___x_40_ = lean_int_add(v___x_35_, v___x_39_);
lean_dec(v___x_39_);
lean_dec(v___x_35_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 1, v___y_30_);
lean_ctor_set(v___x_27_, 0, v___x_40_);
v___x_42_ = v___x_27_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___y_30_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd(lean_object* v_p_46_, lean_object* v_a_47_, lean_object* v_b_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg(v_a_47_, v_b_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___boxed(lean_object* v_p_50_, lean_object* v_a_51_, lean_object* v_b_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd(v_p_50_, v_a_51_, v_b_52_);
lean_dec(v_p_50_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul___redArg(lean_object* v_a_54_, lean_object* v_b_55_){
_start:
{
lean_object* v_mantissa_56_; lean_object* v_exponent_57_; lean_object* v_mantissa_58_; lean_object* v_exponent_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_68_; 
v_mantissa_56_ = lean_ctor_get(v_a_54_, 0);
v_exponent_57_ = lean_ctor_get(v_a_54_, 1);
v_mantissa_58_ = lean_ctor_get(v_b_55_, 0);
v_exponent_59_ = lean_ctor_get(v_b_55_, 1);
v_isSharedCheck_68_ = !lean_is_exclusive(v_b_55_);
if (v_isSharedCheck_68_ == 0)
{
v___x_61_ = v_b_55_;
v_isShared_62_ = v_isSharedCheck_68_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_exponent_59_);
lean_inc(v_mantissa_58_);
lean_dec(v_b_55_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_68_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_63_ = lean_int_mul(v_mantissa_56_, v_mantissa_58_);
lean_dec(v_mantissa_58_);
v___x_64_ = lean_int_add(v_exponent_57_, v_exponent_59_);
lean_dec(v_exponent_59_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_64_);
lean_ctor_set(v___x_61_, 0, v___x_63_);
v___x_66_ = v___x_61_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul___redArg___boxed(lean_object* v_a_69_, lean_object* v_b_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul___redArg(v_a_69_, v_b_70_);
lean_dec_ref(v_a_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul(lean_object* v_p_72_, lean_object* v_a_73_, lean_object* v_b_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul___redArg(v_a_73_, v_b_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul___boxed(lean_object* v_p_76_, lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul(v_p_76_, v_a_77_, v_b_78_);
lean_dec_ref(v_a_77_);
lean_dec(v_p_76_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_shift(lean_object* v_p_80_, lean_object* v_d_81_){
_start:
{
lean_object* v_mantissa_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_mantissa_82_ = lean_ctor_get(v_d_81_, 0);
v___x_83_ = lean_nat_abs(v_mantissa_82_);
v___x_84_ = lean_nat_log2(v___x_83_);
lean_dec(v___x_83_);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v___x_84_, v___x_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_nat_sub(v___x_86_, v_p_80_);
lean_dec(v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_shift___boxed(lean_object* v_p_88_, lean_object* v_d_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_shift(v_p_88_, v_d_89_);
lean_dec_ref(v_d_89_);
lean_dec(v_p_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundDown(lean_object* v_p_91_, lean_object* v_d_92_){
_start:
{
lean_object* v_mantissa_93_; lean_object* v_exponent_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_107_; 
v_mantissa_93_ = lean_ctor_get(v_d_92_, 0);
lean_inc(v_mantissa_93_);
v_exponent_94_ = lean_ctor_get(v_d_92_, 1);
lean_inc(v_exponent_94_);
v___x_95_ = lean_obj_once(&lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0, &lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0_once, _init_lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0);
v___x_96_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_shift(v_p_91_, v_d_92_);
v_isSharedCheck_107_ = !lean_is_exclusive(v_d_92_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; lean_object* v_unused_109_; 
v_unused_108_ = lean_ctor_get(v_d_92_, 1);
lean_dec(v_unused_108_);
v_unused_109_ = lean_ctor_get(v_d_92_, 0);
lean_dec(v_unused_109_);
v___x_98_ = v_d_92_;
v_isShared_99_ = v_isSharedCheck_107_;
goto v_resetjp_97_;
}
else
{
lean_dec(v_d_92_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_107_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_100_ = l_Int_pow(v___x_95_, v___x_96_);
v___x_101_ = lean_int_ediv(v_mantissa_93_, v___x_100_);
lean_dec(v___x_100_);
lean_dec(v_mantissa_93_);
v___x_102_ = lean_nat_to_int(v___x_96_);
v___x_103_ = lean_int_add(v_exponent_94_, v___x_102_);
lean_dec(v___x_102_);
lean_dec(v_exponent_94_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_103_);
lean_ctor_set(v___x_98_, 0, v___x_101_);
v___x_105_ = v___x_98_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundDown___boxed(lean_object* v_p_110_, lean_object* v_d_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundDown(v_p_110_, v_d_111_);
lean_dec(v_p_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundUp(lean_object* v_p_113_, lean_object* v_d_114_){
_start:
{
lean_object* v_mantissa_115_; lean_object* v_exponent_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_131_; 
v_mantissa_115_ = lean_ctor_get(v_d_114_, 0);
v_exponent_116_ = lean_ctor_get(v_d_114_, 1);
lean_inc(v_exponent_116_);
v___x_117_ = lean_int_neg(v_mantissa_115_);
v___x_118_ = lean_obj_once(&lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0, &lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0_once, _init_lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0);
v___x_119_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_shift(v_p_113_, v_d_114_);
v_isSharedCheck_131_ = !lean_is_exclusive(v_d_114_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; lean_object* v_unused_133_; 
v_unused_132_ = lean_ctor_get(v_d_114_, 1);
lean_dec(v_unused_132_);
v_unused_133_ = lean_ctor_get(v_d_114_, 0);
lean_dec(v_unused_133_);
v___x_121_ = v_d_114_;
v_isShared_122_ = v_isSharedCheck_131_;
goto v_resetjp_120_;
}
else
{
lean_dec(v_d_114_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_131_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_123_ = l_Int_pow(v___x_118_, v___x_119_);
v___x_124_ = lean_int_ediv(v___x_117_, v___x_123_);
lean_dec(v___x_123_);
lean_dec(v___x_117_);
v___x_125_ = lean_int_neg(v___x_124_);
lean_dec(v___x_124_);
v___x_126_ = lean_nat_to_int(v___x_119_);
v___x_127_ = lean_int_add(v_exponent_116_, v___x_126_);
lean_dec(v___x_126_);
lean_dec(v_exponent_116_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_127_);
lean_ctor_set(v___x_121_, 0, v___x_125_);
v___x_129_ = v___x_121_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundUp___boxed(lean_object* v_p_134_, lean_object* v_d_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundUp(v_p_134_, v_d_135_);
lean_dec(v_p_134_);
return v_res_136_;
}
}
LEAN_EXPORT uint8_t lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le___redArg(lean_object* v_a_137_, lean_object* v_b_138_){
_start:
{
lean_object* v_mantissa_139_; lean_object* v_exponent_140_; lean_object* v_mantissa_141_; lean_object* v_exponent_142_; lean_object* v___x_143_; lean_object* v___y_145_; uint8_t v___x_155_; 
v_mantissa_139_ = lean_ctor_get(v_a_137_, 0);
v_exponent_140_ = lean_ctor_get(v_a_137_, 1);
v_mantissa_141_ = lean_ctor_get(v_b_138_, 0);
v_exponent_142_ = lean_ctor_get(v_b_138_, 1);
v___x_143_ = lean_obj_once(&lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0, &lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0_once, _init_lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg___closed__0);
v___x_155_ = lean_int_dec_le(v_exponent_140_, v_exponent_142_);
if (v___x_155_ == 0)
{
v___y_145_ = v_exponent_142_;
goto v___jp_144_;
}
else
{
v___y_145_ = v_exponent_140_;
goto v___jp_144_;
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_146_ = lean_int_sub(v_exponent_140_, v___y_145_);
v___x_147_ = l_Int_toNat(v___x_146_);
lean_dec(v___x_146_);
v___x_148_ = l_Int_pow(v___x_143_, v___x_147_);
lean_dec(v___x_147_);
v___x_149_ = lean_int_mul(v_mantissa_139_, v___x_148_);
lean_dec(v___x_148_);
v___x_150_ = lean_int_sub(v_exponent_142_, v___y_145_);
v___x_151_ = l_Int_toNat(v___x_150_);
lean_dec(v___x_150_);
v___x_152_ = l_Int_pow(v___x_143_, v___x_151_);
lean_dec(v___x_151_);
v___x_153_ = lean_int_mul(v_mantissa_141_, v___x_152_);
lean_dec(v___x_152_);
v___x_154_ = lean_int_dec_le(v___x_149_, v___x_153_);
lean_dec(v___x_153_);
lean_dec(v___x_149_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le___redArg___boxed(lean_object* v_a_156_, lean_object* v_b_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le___redArg(v_a_156_, v_b_157_);
lean_dec_ref(v_b_157_);
lean_dec_ref(v_a_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT uint8_t lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le(lean_object* v_p_160_, lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
uint8_t v___x_163_; 
v___x_163_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le___redArg(v_a_161_, v_b_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le___boxed(lean_object* v_p_164_, lean_object* v_a_165_, lean_object* v_b_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le(v_p_164_, v_a_165_, v_b_166_);
lean_dec_ref(v_b_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_p_164_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
static lean_object* _init_lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half___redArg___closed__0(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_nat_to_int(v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half___redArg(lean_object* v_a_171_){
_start:
{
lean_object* v_mantissa_172_; lean_object* v_exponent_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_182_; 
v_mantissa_172_ = lean_ctor_get(v_a_171_, 0);
v_exponent_173_ = lean_ctor_get(v_a_171_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_a_171_);
if (v_isSharedCheck_182_ == 0)
{
v___x_175_ = v_a_171_;
v_isShared_176_ = v_isSharedCheck_182_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_exponent_173_);
lean_inc(v_mantissa_172_);
lean_dec(v_a_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_182_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_177_ = lean_obj_once(&lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half___redArg___closed__0, &lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half___redArg___closed__0_once, _init_lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half___redArg___closed__0);
v___x_178_ = lean_int_sub(v_exponent_173_, v___x_177_);
lean_dec(v_exponent_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_178_);
v___x_180_ = v___x_175_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_mantissa_172_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half(lean_object* v_p_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half___redArg(v_a_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half___boxed(lean_object* v_p_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_half(v_p_186_, v_a_187_);
lean_dec(v_p_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_minimum___redArg(lean_object* v_a_189_, lean_object* v_b_190_){
_start:
{
uint8_t v___x_191_; 
v___x_191_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le___redArg(v_a_189_, v_b_190_);
if (v___x_191_ == 0)
{
lean_inc_ref(v_b_190_);
return v_b_190_;
}
else
{
lean_inc_ref(v_a_189_);
return v_a_189_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_minimum___redArg___boxed(lean_object* v_a_192_, lean_object* v_b_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_minimum___redArg(v_a_192_, v_b_193_);
lean_dec_ref(v_b_193_);
lean_dec_ref(v_a_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_minimum(lean_object* v_p_195_, lean_object* v_a_196_, lean_object* v_b_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_minimum___redArg(v_a_196_, v_b_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_minimum___boxed(lean_object* v_p_199_, lean_object* v_a_200_, lean_object* v_b_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_minimum(v_p_199_, v_a_200_, v_b_201_);
lean_dec_ref(v_b_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_p_199_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_maximum___redArg(lean_object* v_a_203_, lean_object* v_b_204_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_le___redArg(v_a_203_, v_b_204_);
if (v___x_205_ == 0)
{
lean_inc_ref(v_a_203_);
return v_a_203_;
}
else
{
lean_inc_ref(v_b_204_);
return v_b_204_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_maximum___redArg___boxed(lean_object* v_a_206_, lean_object* v_b_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_maximum___redArg(v_a_206_, v_b_207_);
lean_dec_ref(v_b_207_);
lean_dec_ref(v_a_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_maximum(lean_object* v_p_209_, lean_object* v_a_210_, lean_object* v_b_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_maximum___redArg(v_a_210_, v_b_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_maximum___boxed(lean_object* v_p_213_, lean_object* v_a_214_, lean_object* v_b_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_maximum(v_p_213_, v_a_214_, v_b_215_);
lean_dec_ref(v_b_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_p_213_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_addUp(lean_object* v_p_217_, lean_object* v_a_218_, lean_object* v_b_219_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg(v_a_218_, v_b_219_);
v___x_221_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundUp(v_p_217_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_addUp___boxed(lean_object* v_p_222_, lean_object* v_a_223_, lean_object* v_b_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_addUp(v_p_222_, v_a_223_, v_b_224_);
lean_dec(v_p_222_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_addDown(lean_object* v_p_226_, lean_object* v_a_227_, lean_object* v_b_228_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactAdd___redArg(v_a_227_, v_b_228_);
v___x_230_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundDown(v_p_226_, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_addDown___boxed(lean_object* v_p_231_, lean_object* v_a_232_, lean_object* v_b_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_addDown(v_p_231_, v_a_232_, v_b_233_);
lean_dec(v_p_231_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_mulUp(lean_object* v_p_235_, lean_object* v_a_236_, lean_object* v_b_237_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul___redArg(v_a_236_, v_b_237_);
v___x_239_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundUp(v_p_235_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_mulUp___boxed(lean_object* v_p_240_, lean_object* v_a_241_, lean_object* v_b_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_mulUp(v_p_240_, v_a_241_, v_b_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_p_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_mulDown(lean_object* v_p_244_, lean_object* v_a_245_, lean_object* v_b_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_exactMul___redArg(v_a_245_, v_b_246_);
v___x_248_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_roundDown(v_p_244_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Arithmetic_Float_Dyadic_mulDown___boxed(lean_object* v_p_249_, lean_object* v_a_250_, lean_object* v_b_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = lp_CORALean_CORALean_Arithmetic_Float_Dyadic_mulDown(v_p_249_, v_a_250_, v_b_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_p_249_);
return v_res_252_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Arithmetic_Float_SoundFloatArithmetic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Arithmetic_Float_Instances_Dyadic_API(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Arithmetic_Float_SoundFloatArithmetic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
