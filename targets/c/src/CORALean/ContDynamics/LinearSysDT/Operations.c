// Lean compiler output
// Module: CORALean.ContDynamics.LinearSysDT.Operations
// Imports: public import Init public meta import Init public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg(lean_object* v_n_1_, lean_object* v_inst_2_, lean_object* v_inst_3_, lean_object* v_sys_4_, lean_object* v_o_5_, lean_object* v_R_u2080_6_, lean_object* v_U_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; lean_object* v_zero_10_; uint8_t v_isZero_11_; 
lean_inc_ref(v_inst_2_);
lean_inc(v_n_1_);
v___x_9_ = lean_apply_1(v_inst_2_, v_n_1_);
v_zero_10_ = lean_unsigned_to_nat(0u);
v_isZero_11_ = lean_nat_dec_eq(v_x_8_, v_zero_10_);
if (v_isZero_11_ == 1)
{
lean_dec_ref(v___x_9_);
lean_dec(v_U_7_);
lean_dec(v_o_5_);
lean_dec(v_sys_4_);
lean_dec(v_inst_3_);
lean_dec_ref(v_inst_2_);
lean_dec(v_n_1_);
lean_inc(v_R_u2080_6_);
return v_R_u2080_6_;
}
else
{
lean_object* v_plus_12_; lean_object* v_reduce_13_; lean_object* v_one_14_; lean_object* v_n_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_plus_12_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_plus_12_);
v_reduce_13_ = lean_ctor_get(v___x_9_, 2);
lean_inc(v_reduce_13_);
lean_dec_ref(v___x_9_);
v_one_14_ = lean_unsigned_to_nat(1u);
v_n_15_ = lean_nat_sub(v_x_8_, v_one_14_);
lean_inc(v_U_7_);
lean_inc(v_o_5_);
lean_inc(v_sys_4_);
lean_inc(v_inst_3_);
lean_inc_n(v_n_1_, 2);
v___x_16_ = lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg(v_n_1_, v_inst_2_, v_inst_3_, v_sys_4_, v_o_5_, v_R_u2080_6_, v_U_7_, v_n_15_);
lean_dec(v_n_15_);
v___x_17_ = lean_apply_4(v_inst_3_, v_n_1_, v_n_1_, v_sys_4_, v___x_16_);
v___x_18_ = lean_apply_2(v_plus_12_, v___x_17_, v_U_7_);
v___x_19_ = lean_apply_2(v_reduce_13_, v___x_18_, v_o_5_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg___boxed(lean_object* v_n_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_sys_23_, lean_object* v_o_24_, lean_object* v_R_u2080_25_, lean_object* v_U_26_, lean_object* v_x_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg(v_n_20_, v_inst_21_, v_inst_22_, v_sys_23_, v_o_24_, v_R_u2080_25_, v_U_26_, v_x_27_);
lean_dec(v_x_27_);
lean_dec(v_R_u2080_25_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach(lean_object* v_n_29_, lean_object* v_00_U0001d54b_30_, lean_object* v_inst_31_, lean_object* v_S_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_sys_36_, lean_object* v_o_37_, lean_object* v_R_u2080_38_, lean_object* v_U_39_, lean_object* v_x_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg(v_n_29_, v_inst_34_, v_inst_35_, v_sys_36_, v_o_37_, v_R_u2080_38_, v_U_39_, v_x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach___boxed(lean_object* v_n_42_, lean_object* v_00_U0001d54b_43_, lean_object* v_inst_44_, lean_object* v_S_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_sys_49_, lean_object* v_o_50_, lean_object* v_R_u2080_51_, lean_object* v_U_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_CORALean_CORALean_Real_LinearSysDT_reach(v_n_42_, v_00_U0001d54b_43_, v_inst_44_, v_S_45_, v_inst_46_, v_inst_47_, v_inst_48_, v_sys_49_, v_o_50_, v_R_u2080_51_, v_U_52_, v_x_53_);
lean_dec(v_x_53_);
lean_dec(v_R_u2080_51_);
lean_dec_ref(v_inst_46_);
lean_dec(v_inst_44_);
return v_res_54_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSysDT_LinearSysDT(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContDynamics_LinearSysDT_Operations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContDynamics_LinearSysDT_LinearSysDT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
