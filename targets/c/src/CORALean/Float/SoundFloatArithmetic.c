// Lean compiler output
// Module: CORALean.Float.SoundFloatArithmetic
// Imports: public import Init public meta import Init public import CORALean.Float.FloatOps
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_toRealVec___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_toRealVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_toRealVec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_toRealMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_toRealMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_toRealMat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instScalar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instScalar___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instScalar___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instScalar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instScalar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean___private_CORALean_Float_SoundFloatArithmetic_0__CORALean_Float_sumUp_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean___private_CORALean_Float_SoundFloatArithmetic_0__CORALean_Float_sumUp_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean___private_CORALean_Float_SoundFloatArithmetic_0__CORALean_Float_sumUp_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean___private_CORALean_Float_SoundFloatArithmetic_0__CORALean_Float_sumUp_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_toRealVec___redArg(lean_object* v_inst_1_, lean_object* v_v_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_v_2_, v_i_3_);
v___x_5_ = lean_apply_1(v_inst_1_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_toRealVec(lean_object* v_00_U0001d54b_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_n_9_, lean_object* v_v_10_, lean_object* v_i_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_CORALean_CORALean_Float_toRealVec___redArg(v_inst_8_, v_v_10_, v_i_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_toRealVec___boxed(lean_object* v_00_U0001d54b_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_n_16_, lean_object* v_v_17_, lean_object* v_i_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_CORALean_CORALean_Float_toRealVec(v_00_U0001d54b_13_, v_inst_14_, v_inst_15_, v_n_16_, v_v_17_, v_i_18_);
lean_dec(v_n_16_);
lean_dec_ref(v_inst_14_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_toRealMat___redArg(lean_object* v_inst_20_, lean_object* v_M_21_, lean_object* v_i_22_, lean_object* v_j_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_apply_2(v_M_21_, v_i_22_, v_j_23_);
v___x_25_ = lean_apply_1(v_inst_20_, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_toRealMat(lean_object* v_00_U0001d54b_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_n_29_, lean_object* v_m_30_, lean_object* v_M_31_, lean_object* v_i_32_, lean_object* v_j_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_CORALean_CORALean_Float_toRealMat___redArg(v_inst_28_, v_M_31_, v_i_32_, v_j_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_toRealMat___boxed(lean_object* v_00_U0001d54b_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_n_38_, lean_object* v_m_39_, lean_object* v_M_40_, lean_object* v_i_41_, lean_object* v_j_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_CORALean_CORALean_Float_toRealMat(v_00_U0001d54b_35_, v_inst_36_, v_inst_37_, v_n_38_, v_m_39_, v_M_40_, v_i_41_, v_j_42_);
lean_dec(v_m_39_);
lean_dec(v_n_38_);
lean_dec_ref(v_inst_36_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instScalar___redArg___lam__0(lean_object* v_inst_44_, lean_object* v_m_45_, lean_object* v_n_46_, lean_object* v_M_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lp_CORALean_CORALean_Float_toRealMat___redArg(v_inst_44_, v_M_47_, v___y_48_, v___y_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instScalar___redArg___lam__0___boxed(lean_object* v_inst_51_, lean_object* v_m_52_, lean_object* v_n_53_, lean_object* v_M_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_CORALean_CORALean_Float_instScalar___redArg___lam__0(v_inst_51_, v_m_52_, v_n_53_, v_M_54_, v___y_55_, v___y_56_);
lean_dec(v_n_53_);
lean_dec(v_m_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instScalar___redArg(lean_object* v_inst_58_){
_start:
{
lean_object* v___f_59_; 
v___f_59_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_instScalar___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_59_, 0, v_inst_58_);
return v___f_59_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instScalar(lean_object* v_00_U0001d54b_60_, lean_object* v_inst_61_, lean_object* v_inst_62_){
_start:
{
lean_object* v___f_63_; 
v___f_63_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_instScalar___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_63_, 0, v_inst_62_);
return v___f_63_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instScalar___boxed(lean_object* v_00_U0001d54b_64_, lean_object* v_inst_65_, lean_object* v_inst_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_CORALean_CORALean_Float_instScalar(v_00_U0001d54b_64_, v_inst_65_, v_inst_66_);
lean_dec_ref(v_inst_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_CORALean___private_CORALean_Float_SoundFloatArithmetic_0__CORALean_Float_sumUp_match__1_splitter___redArg(lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
lean_object* v_zero_72_; uint8_t v_isZero_73_; 
v_zero_72_ = lean_unsigned_to_nat(0u);
v_isZero_73_ = lean_nat_dec_eq(v_x_68_, v_zero_72_);
if (v_isZero_73_ == 1)
{
lean_object* v___x_74_; 
lean_dec(v_h__2_71_);
v___x_74_ = lean_apply_1(v_h__1_70_, v_x_69_);
return v___x_74_;
}
else
{
lean_object* v_one_75_; lean_object* v_n_76_; lean_object* v___x_77_; 
lean_dec(v_h__1_70_);
v_one_75_ = lean_unsigned_to_nat(1u);
v_n_76_ = lean_nat_sub(v_x_68_, v_one_75_);
v___x_77_ = lean_apply_2(v_h__2_71_, v_n_76_, v_x_69_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean___private_CORALean_Float_SoundFloatArithmetic_0__CORALean_Float_sumUp_match__1_splitter___redArg___boxed(lean_object* v_x_78_, lean_object* v_x_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lp_CORALean___private_CORALean_Float_SoundFloatArithmetic_0__CORALean_Float_sumUp_match__1_splitter___redArg(v_x_78_, v_x_79_, v_h__1_80_, v_h__2_81_);
lean_dec(v_x_78_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* lp_CORALean___private_CORALean_Float_SoundFloatArithmetic_0__CORALean_Float_sumUp_match__1_splitter(lean_object* v_00_U0001d54b_83_, lean_object* v_motive_84_, lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
lean_object* v_zero_89_; uint8_t v_isZero_90_; 
v_zero_89_ = lean_unsigned_to_nat(0u);
v_isZero_90_ = lean_nat_dec_eq(v_x_85_, v_zero_89_);
if (v_isZero_90_ == 1)
{
lean_object* v___x_91_; 
lean_dec(v_h__2_88_);
v___x_91_ = lean_apply_1(v_h__1_87_, v_x_86_);
return v___x_91_;
}
else
{
lean_object* v_one_92_; lean_object* v_n_93_; lean_object* v___x_94_; 
lean_dec(v_h__1_87_);
v_one_92_ = lean_unsigned_to_nat(1u);
v_n_93_ = lean_nat_sub(v_x_85_, v_one_92_);
v___x_94_ = lean_apply_2(v_h__2_88_, v_n_93_, v_x_86_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean___private_CORALean_Float_SoundFloatArithmetic_0__CORALean_Float_sumUp_match__1_splitter___boxed(lean_object* v_00_U0001d54b_95_, lean_object* v_motive_96_, lean_object* v_x_97_, lean_object* v_x_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_CORALean___private_CORALean_Float_SoundFloatArithmetic_0__CORALean_Float_sumUp_match__1_splitter(v_00_U0001d54b_95_, v_motive_96_, v_x_97_, v_x_98_, v_h__1_99_, v_h__2_100_);
lean_dec(v_x_97_);
return v_res_101_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_FloatOps(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Float_SoundFloatArithmetic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_FloatOps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
