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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg(lean_object* v_n_1_, lean_object* v_inst_2_, lean_object* v_sys_3_, lean_object* v_o_4_, lean_object* v_R_u2080_5_, lean_object* v_U_6_, lean_object* v_x_7_){
_start:
{
lean_object* v_toMtimes_8_; lean_object* v_plus_9_; lean_object* v_reduce_10_; lean_object* v_zero_11_; uint8_t v_isZero_12_; 
v_toMtimes_8_ = lean_ctor_get(v_inst_2_, 0);
lean_inc(v_toMtimes_8_);
v_plus_9_ = lean_ctor_get(v_inst_2_, 1);
lean_inc(v_plus_9_);
v_reduce_10_ = lean_ctor_get(v_inst_2_, 3);
lean_inc(v_reduce_10_);
v_zero_11_ = lean_unsigned_to_nat(0u);
v_isZero_12_ = lean_nat_dec_eq(v_x_7_, v_zero_11_);
if (v_isZero_12_ == 1)
{
lean_dec(v_reduce_10_);
lean_dec(v_plus_9_);
lean_dec(v_toMtimes_8_);
lean_dec(v_U_6_);
lean_dec(v_o_4_);
lean_dec(v_sys_3_);
lean_dec_ref(v_inst_2_);
lean_dec(v_n_1_);
lean_inc(v_R_u2080_5_);
return v_R_u2080_5_;
}
else
{
lean_object* v_one_13_; lean_object* v_n_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_one_13_ = lean_unsigned_to_nat(1u);
v_n_14_ = lean_nat_sub(v_x_7_, v_one_13_);
lean_inc(v_U_6_);
lean_inc(v_o_4_);
lean_inc(v_sys_3_);
lean_inc_n(v_n_1_, 4);
v___x_15_ = lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg(v_n_1_, v_inst_2_, v_sys_3_, v_o_4_, v_R_u2080_5_, v_U_6_, v_n_14_);
lean_dec(v_n_14_);
v___x_16_ = lean_apply_4(v_toMtimes_8_, v_n_1_, v_n_1_, v_sys_3_, v___x_15_);
v___x_17_ = lean_apply_3(v_plus_9_, v_n_1_, v___x_16_, v_U_6_);
v___x_18_ = lean_apply_3(v_reduce_10_, v_n_1_, v___x_17_, v_o_4_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg___boxed(lean_object* v_n_19_, lean_object* v_inst_20_, lean_object* v_sys_21_, lean_object* v_o_22_, lean_object* v_R_u2080_23_, lean_object* v_U_24_, lean_object* v_x_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg(v_n_19_, v_inst_20_, v_sys_21_, v_o_22_, v_R_u2080_23_, v_U_24_, v_x_25_);
lean_dec(v_x_25_);
lean_dec(v_R_u2080_23_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach(lean_object* v_n_27_, lean_object* v_00_U0001d54b_28_, lean_object* v_inst_29_, lean_object* v_S_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_sys_33_, lean_object* v_o_34_, lean_object* v_R_u2080_35_, lean_object* v_U_36_, lean_object* v_x_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_CORALean_CORALean_Real_LinearSysDT_reach___redArg(v_n_27_, v_inst_32_, v_sys_33_, v_o_34_, v_R_u2080_35_, v_U_36_, v_x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_LinearSysDT_reach___boxed(lean_object* v_n_39_, lean_object* v_00_U0001d54b_40_, lean_object* v_inst_41_, lean_object* v_S_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_sys_45_, lean_object* v_o_46_, lean_object* v_R_u2080_47_, lean_object* v_U_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_CORALean_CORALean_Real_LinearSysDT_reach(v_n_39_, v_00_U0001d54b_40_, v_inst_41_, v_S_42_, v_inst_43_, v_inst_44_, v_sys_45_, v_o_46_, v_R_u2080_47_, v_U_48_, v_x_49_);
lean_dec(v_x_49_);
lean_dec(v_R_u2080_47_);
lean_dec_ref(v_inst_43_);
lean_dec(v_inst_41_);
return v_res_50_;
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
