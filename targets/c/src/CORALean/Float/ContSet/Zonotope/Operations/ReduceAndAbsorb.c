// Lean compiler output
// Module: CORALean.Float.ContSet.Zonotope.Operations.ReduceAndAbsorb
// Imports: public import Init public meta import Init public import CORALean.Float.ContSet.Zonotope.Operations.AbsorbError
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
lean_object* lp_CORALean_CORALean_Partition_left___redArg(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_diagonalBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_addCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Partition_right___redArg(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_radius___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Zonotope_errorRadius___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Zonotope_shiftUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Interval_residual___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__0(lean_object* v_Z_1_, lean_object* v_part_2_, lean_object* v_i_3_, lean_object* v_l_4_){
_start:
{
lean_object* v_G_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_G_5_ = lean_ctor_get(v_Z_1_, 2);
lean_inc(v_G_5_);
lean_dec_ref(v_Z_1_);
v___x_6_ = lp_CORALean_CORALean_Partition_right___redArg(v_part_2_, v_l_4_);
v___x_7_ = lean_apply_2(v_G_5_, v_i_3_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__1(lean_object* v_inst_8_, lean_object* v_r_9_, lean_object* v___f_10_, lean_object* v_Z_11_, lean_object* v_i_12_){
_start:
{
lean_object* v_addUp_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_addUp_13_ = lean_ctor_get(v_inst_8_, 2);
lean_inc(v_addUp_13_);
lean_inc(v_i_12_);
lean_inc_ref(v_inst_8_);
v___x_14_ = lp_CORALean_CORALean_Float_radius___redArg(v_inst_8_, v_r_9_, v___f_10_, v_i_12_);
v___x_15_ = lp_CORALean_CORALean_Float_Zonotope_errorRadius___redArg(v_inst_8_, v_Z_11_, v_i_12_);
v___x_16_ = lean_apply_2(v_addUp_13_, v___x_14_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__1___boxed(lean_object* v_inst_17_, lean_object* v_r_18_, lean_object* v___f_19_, lean_object* v_Z_20_, lean_object* v_i_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__1(v_inst_17_, v_r_18_, v___f_19_, v_Z_20_, v_i_21_);
lean_dec(v_r_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__2(lean_object* v_Z_23_, lean_object* v_part_24_, lean_object* v_i_25_, lean_object* v_l_26_){
_start:
{
lean_object* v_G_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_G_27_ = lean_ctor_get(v_Z_23_, 2);
lean_inc(v_G_27_);
lean_dec_ref(v_Z_23_);
v___x_28_ = lp_CORALean_CORALean_Partition_left___redArg(v_part_24_, v_l_26_);
v___x_29_ = lean_apply_2(v_G_27_, v_i_25_, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__3(lean_object* v_Z_30_, lean_object* v_part_31_, lean_object* v_inst_32_, lean_object* v_n_33_, lean_object* v___f_34_, lean_object* v_q_35_, lean_object* v_i_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
lean_inc(v_i_36_);
v___f_38_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__2), 4, 3);
lean_closure_set(v___f_38_, 0, v_Z_30_);
lean_closure_set(v___f_38_, 1, v_part_31_);
lean_closure_set(v___f_38_, 2, v_i_36_);
v___x_39_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_diagonalBlock___boxed), 6, 5);
lean_closure_set(v___x_39_, 0, lean_box(0));
lean_closure_set(v___x_39_, 1, v_inst_32_);
lean_closure_set(v___x_39_, 2, v_n_33_);
lean_closure_set(v___x_39_, 3, v___f_34_);
lean_closure_set(v___x_39_, 4, v_i_36_);
v___x_40_ = l_Fin_addCases___redArg(v_q_35_, v___f_38_, v___x_39_, v___y_37_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__3___boxed(lean_object* v_Z_41_, lean_object* v_part_42_, lean_object* v_inst_43_, lean_object* v_n_44_, lean_object* v___f_45_, lean_object* v_q_46_, lean_object* v_i_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__3(v_Z_41_, v_part_42_, v_inst_43_, v_n_44_, v___f_45_, v_q_46_, v_i_47_, v___y_48_);
lean_dec(v_q_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg(lean_object* v_inst_50_, lean_object* v_n_51_, lean_object* v_q_52_, lean_object* v_r_53_, lean_object* v_Z_54_, lean_object* v_part_55_){
_start:
{
lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
lean_inc_ref(v_part_55_);
lean_inc_ref_n(v_Z_54_, 4);
v___f_56_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__0), 4, 2);
lean_closure_set(v___f_56_, 0, v_Z_54_);
lean_closure_set(v___f_56_, 1, v_part_55_);
lean_inc_ref_n(v_inst_50_, 4);
v___f_57_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_57_, 0, v_inst_50_);
lean_closure_set(v___f_57_, 1, v_r_53_);
lean_closure_set(v___f_57_, 2, v___f_56_);
lean_closure_set(v___f_57_, 3, v_Z_54_);
lean_inc(v_q_52_);
lean_inc_n(v_n_51_, 2);
v___f_58_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg___lam__3___boxed), 8, 6);
lean_closure_set(v___f_58_, 0, v_Z_54_);
lean_closure_set(v___f_58_, 1, v_part_55_);
lean_closure_set(v___f_58_, 2, v_inst_50_);
lean_closure_set(v___f_58_, 3, v_n_51_);
lean_closure_set(v___f_58_, 4, v___f_57_);
lean_closure_set(v___f_58_, 5, v_q_52_);
v___x_59_ = lean_nat_add(v_q_52_, v_n_51_);
lean_dec(v_q_52_);
v___x_60_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_shiftDown___boxed), 5, 4);
lean_closure_set(v___x_60_, 0, lean_box(0));
lean_closure_set(v___x_60_, 1, v_inst_50_);
lean_closure_set(v___x_60_, 2, v_n_51_);
lean_closure_set(v___x_60_, 3, v_Z_54_);
v___x_61_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Zonotope_shiftUp___boxed), 5, 4);
lean_closure_set(v___x_61_, 0, lean_box(0));
lean_closure_set(v___x_61_, 1, v_inst_50_);
lean_closure_set(v___x_61_, 2, v_n_51_);
lean_closure_set(v___x_61_, 3, v_Z_54_);
lean_inc_ref_n(v___x_60_, 2);
v___x_62_ = lp_CORALean_CORALean_Float_Interval_residual___redArg(v_inst_50_, v___x_60_, v___x_61_, v___x_60_);
v___x_63_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_63_, 0, v___x_59_);
lean_ctor_set(v___x_63_, 1, v___x_60_);
lean_ctor_set(v___x_63_, 2, v___f_58_);
lean_ctor_set(v___x_63_, 3, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy(lean_object* v_00_U0001d54b_64_, lean_object* v_inst_65_, lean_object* v_n_66_, lean_object* v_q_67_, lean_object* v_r_68_, lean_object* v_Z_69_, lean_object* v_part_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_CORALean_CORALean_Float_Zonotope_reduceAndAbsorbBy___redArg(v_inst_65_, v_n_66_, v_q_67_, v_r_68_, v_Z_69_, v_part_70_);
return v___x_71_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Operations_AbsorbError(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Operations_ReduceAndAbsorb(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Operations_AbsorbError(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
