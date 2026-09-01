// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Float.Operations.Plus
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
lean_object* lp_CORALean_CORALean_Float_Interval_residual___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_addCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Interval_plus___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_centerResidual___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_centerResidual___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_centerResidual___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_centerResidual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_centerResidual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_plus___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_plus___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_plus___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_plus___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_plus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_plus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_centerResidual___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_, lean_object* v_i_4_){
_start:
{
lean_object* v_addDown_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_addDown_5_ = lean_ctor_get(v_inst_1_, 3);
lean_inc(v_addDown_5_);
lean_dec_ref(v_inst_1_);
lean_inc(v_i_4_);
v___x_6_ = lean_apply_1(v_a_2_, v_i_4_);
v___x_7_ = lean_apply_1(v_b_3_, v_i_4_);
v___x_8_ = lean_apply_2(v_addDown_5_, v___x_6_, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_centerResidual___redArg___lam__1(lean_object* v_inst_9_, lean_object* v_a_10_, lean_object* v_b_11_, lean_object* v_i_12_){
_start:
{
lean_object* v_addUp_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_addUp_13_ = lean_ctor_get(v_inst_9_, 2);
lean_inc(v_addUp_13_);
lean_dec_ref(v_inst_9_);
lean_inc(v_i_12_);
v___x_14_ = lean_apply_1(v_a_10_, v_i_12_);
v___x_15_ = lean_apply_1(v_b_11_, v_i_12_);
v___x_16_ = lean_apply_2(v_addUp_13_, v___x_14_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_centerResidual___redArg(lean_object* v_inst_17_, lean_object* v_a_18_, lean_object* v_b_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___x_22_; 
lean_inc(v_b_19_);
lean_inc(v_a_18_);
lean_inc_ref_n(v_inst_17_, 2);
v___f_20_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_centerResidual___redArg___lam__0), 4, 3);
lean_closure_set(v___f_20_, 0, v_inst_17_);
lean_closure_set(v___f_20_, 1, v_a_18_);
lean_closure_set(v___f_20_, 2, v_b_19_);
v___f_21_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_centerResidual___redArg___lam__1), 4, 3);
lean_closure_set(v___f_21_, 0, v_inst_17_);
lean_closure_set(v___f_21_, 1, v_a_18_);
lean_closure_set(v___f_21_, 2, v_b_19_);
lean_inc_ref(v___f_20_);
v___x_22_ = lp_CORALean_CORALean_Float_Interval_residual___redArg(v_inst_17_, v___f_20_, v___f_21_, v___f_20_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_centerResidual(lean_object* v_00_U0001d54b_23_, lean_object* v_inst_24_, lean_object* v_n_25_, lean_object* v_a_26_, lean_object* v_b_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_CORALean_CORALean_Float_Zonotope_centerResidual___redArg(v_inst_24_, v_a_26_, v_b_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_centerResidual___boxed(lean_object* v_00_U0001d54b_29_, lean_object* v_inst_30_, lean_object* v_n_31_, lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_CORALean_CORALean_Float_Zonotope_centerResidual(v_00_U0001d54b_29_, v_inst_30_, v_n_31_, v_a_32_, v_b_33_);
lean_dec(v_n_31_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_plus___redArg___lam__0(lean_object* v_inst_35_, lean_object* v_c_36_, lean_object* v_c_37_, lean_object* v_i_38_){
_start:
{
lean_object* v_addDown_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_addDown_39_ = lean_ctor_get(v_inst_35_, 3);
lean_inc(v_addDown_39_);
lean_dec_ref(v_inst_35_);
lean_inc(v_i_38_);
v___x_40_ = lean_apply_1(v_c_36_, v_i_38_);
v___x_41_ = lean_apply_1(v_c_37_, v_i_38_);
v___x_42_ = lean_apply_2(v_addDown_39_, v___x_40_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_plus___redArg___lam__1(lean_object* v_G_43_, lean_object* v_G_44_, lean_object* v_h_45_, lean_object* v_i_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
lean_inc(v_i_46_);
v___x_48_ = lean_apply_1(v_G_43_, v_i_46_);
v___x_49_ = lean_apply_1(v_G_44_, v_i_46_);
v___x_50_ = l_Fin_addCases___redArg(v_h_45_, v___x_48_, v___x_49_, v___y_47_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_plus___redArg___lam__1___boxed(lean_object* v_G_51_, lean_object* v_G_52_, lean_object* v_h_53_, lean_object* v_i_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_CORALean_CORALean_Float_Zonotope_plus___redArg___lam__1(v_G_51_, v_G_52_, v_h_53_, v_i_54_, v___y_55_);
lean_dec(v_h_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_plus___redArg(lean_object* v_inst_57_, lean_object* v_Z_u2081_58_, lean_object* v_Z_u2082_59_){
_start:
{
lean_object* v_h_60_; lean_object* v_c_61_; lean_object* v_G_62_; lean_object* v_E_63_; lean_object* v_h_64_; lean_object* v_c_65_; lean_object* v_G_66_; lean_object* v_E_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_80_; 
v_h_60_ = lean_ctor_get(v_Z_u2081_58_, 0);
lean_inc(v_h_60_);
v_c_61_ = lean_ctor_get(v_Z_u2081_58_, 1);
lean_inc(v_c_61_);
v_G_62_ = lean_ctor_get(v_Z_u2081_58_, 2);
lean_inc(v_G_62_);
v_E_63_ = lean_ctor_get(v_Z_u2081_58_, 3);
lean_inc_ref(v_E_63_);
lean_dec_ref(v_Z_u2081_58_);
v_h_64_ = lean_ctor_get(v_Z_u2082_59_, 0);
v_c_65_ = lean_ctor_get(v_Z_u2082_59_, 1);
v_G_66_ = lean_ctor_get(v_Z_u2082_59_, 2);
v_E_67_ = lean_ctor_get(v_Z_u2082_59_, 3);
v_isSharedCheck_80_ = !lean_is_exclusive(v_Z_u2082_59_);
if (v_isSharedCheck_80_ == 0)
{
v___x_69_ = v_Z_u2082_59_;
v_isShared_70_ = v_isSharedCheck_80_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_E_67_);
lean_inc(v_G_66_);
lean_inc(v_c_65_);
lean_inc(v_h_64_);
lean_dec(v_Z_u2082_59_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_80_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
lean_inc(v_c_65_);
lean_inc(v_c_61_);
lean_inc_ref_n(v_inst_57_, 3);
v___f_71_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_plus___redArg___lam__0), 4, 3);
lean_closure_set(v___f_71_, 0, v_inst_57_);
lean_closure_set(v___f_71_, 1, v_c_61_);
lean_closure_set(v___f_71_, 2, v_c_65_);
lean_inc(v_h_60_);
v___f_72_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_plus___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_72_, 0, v_G_62_);
lean_closure_set(v___f_72_, 1, v_G_66_);
lean_closure_set(v___f_72_, 2, v_h_60_);
v___x_73_ = lean_nat_add(v_h_60_, v_h_64_);
lean_dec(v_h_64_);
lean_dec(v_h_60_);
v___x_74_ = lp_CORALean_CORALean_Float_Interval_plus___redArg(v_inst_57_, v_E_63_, v_E_67_);
v___x_75_ = lp_CORALean_CORALean_Float_Zonotope_centerResidual___redArg(v_inst_57_, v_c_61_, v_c_65_);
v___x_76_ = lp_CORALean_CORALean_Float_Interval_plus___redArg(v_inst_57_, v___x_74_, v___x_75_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 3, v___x_76_);
lean_ctor_set(v___x_69_, 2, v___f_72_);
lean_ctor_set(v___x_69_, 1, v___f_71_);
lean_ctor_set(v___x_69_, 0, v___x_73_);
v___x_78_ = v___x_69_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v___f_71_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v___f_72_);
lean_ctor_set(v_reuseFailAlloc_79_, 3, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_plus(lean_object* v_00_U0001d54b_81_, lean_object* v_inst_82_, lean_object* v_n_83_, lean_object* v_Z_u2081_84_, lean_object* v_Z_u2082_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lp_CORALean_CORALean_Float_Zonotope_plus___redArg(v_inst_82_, v_Z_u2081_84_, v_Z_u2082_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_plus___boxed(lean_object* v_00_U0001d54b_87_, lean_object* v_inst_88_, lean_object* v_n_89_, lean_object* v_Z_u2081_90_, lean_object* v_Z_u2082_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = lp_CORALean_CORALean_Float_Zonotope_plus(v_00_U0001d54b_87_, v_inst_88_, v_n_89_, v_Z_u2081_90_, v_Z_u2082_91_);
lean_dec(v_n_89_);
return v_res_92_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Zonotope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Float_Operations_Plus(uint8_t builtin) {
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
