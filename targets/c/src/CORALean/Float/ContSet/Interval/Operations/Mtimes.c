// Lean compiler output
// Module: CORALean.Float.ContSet.Interval.Operations.Mtimes
// Imports: public import Init public meta import Init public import CORALean.Float.ContSet.Interval.Interval
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
lean_object* lp_CORALean_CORALean_Float_sumDown___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_sumUp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_I_2_, lean_object* v_M_3_, lean_object* v_i_4_, lean_object* v_k_5_){
_start:
{
lean_object* v_mulDown_6_; lean_object* v_minimum_7_; lean_object* v_inf_8_; lean_object* v_sup_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_mulDown_6_ = lean_ctor_get(v_inst_1_, 5);
lean_inc_n(v_mulDown_6_, 2);
v_minimum_7_ = lean_ctor_get(v_inst_1_, 6);
lean_inc(v_minimum_7_);
lean_dec_ref(v_inst_1_);
v_inf_8_ = lean_ctor_get(v_I_2_, 0);
lean_inc(v_inf_8_);
v_sup_9_ = lean_ctor_get(v_I_2_, 1);
lean_inc(v_sup_9_);
lean_dec_ref(v_I_2_);
lean_inc_n(v_k_5_, 2);
v___x_10_ = lean_apply_2(v_M_3_, v_i_4_, v_k_5_);
v___x_11_ = lean_apply_1(v_inf_8_, v_k_5_);
lean_inc(v___x_10_);
v___x_12_ = lean_apply_2(v_mulDown_6_, v___x_10_, v___x_11_);
v___x_13_ = lean_apply_1(v_sup_9_, v_k_5_);
v___x_14_ = lean_apply_2(v_mulDown_6_, v___x_10_, v___x_13_);
v___x_15_ = lean_apply_2(v_minimum_7_, v___x_12_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__1(lean_object* v_inst_16_, lean_object* v_I_17_, lean_object* v_M_18_, lean_object* v_n_19_, lean_object* v_i_20_){
_start:
{
lean_object* v___f_21_; lean_object* v___x_22_; 
lean_inc_ref(v_inst_16_);
v___f_21_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__0), 5, 4);
lean_closure_set(v___f_21_, 0, v_inst_16_);
lean_closure_set(v___f_21_, 1, v_I_17_);
lean_closure_set(v___f_21_, 2, v_M_18_);
lean_closure_set(v___f_21_, 3, v_i_20_);
v___x_22_ = lp_CORALean_CORALean_Float_sumDown___redArg(v_inst_16_, v_n_19_, v___f_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__1___boxed(lean_object* v_inst_23_, lean_object* v_I_24_, lean_object* v_M_25_, lean_object* v_n_26_, lean_object* v_i_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__1(v_inst_23_, v_I_24_, v_M_25_, v_n_26_, v_i_27_);
lean_dec(v_n_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__2(lean_object* v_inst_29_, lean_object* v_I_30_, lean_object* v_M_31_, lean_object* v_i_32_, lean_object* v_k_33_){
_start:
{
lean_object* v_mulUp_34_; lean_object* v_maximum_35_; lean_object* v_inf_36_; lean_object* v_sup_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_mulUp_34_ = lean_ctor_get(v_inst_29_, 4);
lean_inc_n(v_mulUp_34_, 2);
v_maximum_35_ = lean_ctor_get(v_inst_29_, 7);
lean_inc(v_maximum_35_);
lean_dec_ref(v_inst_29_);
v_inf_36_ = lean_ctor_get(v_I_30_, 0);
lean_inc(v_inf_36_);
v_sup_37_ = lean_ctor_get(v_I_30_, 1);
lean_inc(v_sup_37_);
lean_dec_ref(v_I_30_);
lean_inc_n(v_k_33_, 2);
v___x_38_ = lean_apply_2(v_M_31_, v_i_32_, v_k_33_);
v___x_39_ = lean_apply_1(v_inf_36_, v_k_33_);
lean_inc(v___x_38_);
v___x_40_ = lean_apply_2(v_mulUp_34_, v___x_38_, v___x_39_);
v___x_41_ = lean_apply_1(v_sup_37_, v_k_33_);
v___x_42_ = lean_apply_2(v_mulUp_34_, v___x_38_, v___x_41_);
v___x_43_ = lean_apply_2(v_maximum_35_, v___x_40_, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__3(lean_object* v_inst_44_, lean_object* v_I_45_, lean_object* v_M_46_, lean_object* v_n_47_, lean_object* v_i_48_){
_start:
{
lean_object* v___f_49_; lean_object* v___x_50_; 
lean_inc_ref(v_inst_44_);
v___f_49_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__2), 5, 4);
lean_closure_set(v___f_49_, 0, v_inst_44_);
lean_closure_set(v___f_49_, 1, v_I_45_);
lean_closure_set(v___f_49_, 2, v_M_46_);
lean_closure_set(v___f_49_, 3, v_i_48_);
v___x_50_ = lp_CORALean_CORALean_Float_sumUp___redArg(v_inst_44_, v_n_47_, v___f_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__3___boxed(lean_object* v_inst_51_, lean_object* v_I_52_, lean_object* v_M_53_, lean_object* v_n_54_, lean_object* v_i_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__3(v_inst_51_, v_I_52_, v_M_53_, v_n_54_, v_i_55_);
lean_dec(v_n_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___redArg(lean_object* v_inst_57_, lean_object* v_n_58_, lean_object* v_M_59_, lean_object* v_I_60_){
_start:
{
lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___x_63_; 
lean_inc(v_n_58_);
lean_inc(v_M_59_);
lean_inc_ref(v_I_60_);
lean_inc_ref(v_inst_57_);
v___f_61_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_61_, 0, v_inst_57_);
lean_closure_set(v___f_61_, 1, v_I_60_);
lean_closure_set(v___f_61_, 2, v_M_59_);
lean_closure_set(v___f_61_, 3, v_n_58_);
v___f_62_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Interval_mtimes___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_62_, 0, v_inst_57_);
lean_closure_set(v___f_62_, 1, v_I_60_);
lean_closure_set(v___f_62_, 2, v_M_59_);
lean_closure_set(v___f_62_, 3, v_n_58_);
v___x_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_63_, 0, v___f_61_);
lean_ctor_set(v___x_63_, 1, v___f_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes(lean_object* v_00_U0001d54b_64_, lean_object* v_inst_65_, lean_object* v_n_66_, lean_object* v_m_67_, lean_object* v_M_68_, lean_object* v_I_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lp_CORALean_CORALean_Float_Interval_mtimes___redArg(v_inst_65_, v_n_66_, v_M_68_, v_I_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Interval_mtimes___boxed(lean_object* v_00_U0001d54b_71_, lean_object* v_inst_72_, lean_object* v_n_73_, lean_object* v_m_74_, lean_object* v_M_75_, lean_object* v_I_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_CORALean_CORALean_Float_Interval_mtimes(v_00_U0001d54b_71_, v_inst_72_, v_n_73_, v_m_74_, v_M_75_, v_I_76_);
lean_dec(v_m_74_);
return v_res_77_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Interval_Interval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Float_ContSet_Interval_Operations_Mtimes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Interval_Interval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
