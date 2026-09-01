// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Real.Operations.Reduce
// Imports: public import Init public meta import Init public import CORALean.ContSet.Zonotope.Real.Zonotope
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
lean_object* lp_mathlib_Equiv_refl(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_CORALean_CORALean_Partition_left___redArg(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Partition_right___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_abs___at___00EReal_abs_spec__0(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Fin_addCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg___lam__0(lean_object* v_d_1_, lean_object* v_i_2_, lean_object* v_j_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_nat_dec_eq(v_i_2_, v_j_3_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
lean_dec(v_i_2_);
lean_dec(v_d_1_);
v___x_5_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return v___x_5_;
}
else
{
lean_object* v___x_6_; 
v___x_6_ = lean_apply_1(v_d_1_, v_i_2_);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg___lam__0___boxed(lean_object* v_d_7_, lean_object* v_i_8_, lean_object* v_j_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg___lam__0(v_d_7_, v_i_8_, v_j_9_);
lean_dec(v_j_9_);
return v_res_10_;
}
}
static lean_object* _init_lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg(lean_object* v_d_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_15_; lean_object* v_toFun_16_; lean_object* v___f_17_; lean_object* v___x_18_; 
v___x_15_ = lean_obj_once(&lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg___closed__0, &lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg___closed__0_once, _init_lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg___closed__0);
v_toFun_16_ = lean_ctor_get(v___x_15_, 0);
v___f_17_ = lean_alloc_closure((void*)(lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_17_, 0, v_d_12_);
lean_inc(v_toFun_16_);
v___x_18_ = lean_apply_3(v_toFun_16_, v___f_17_, v_a_13_, v_a_14_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0(lean_object* v_n_19_, lean_object* v_d_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg(v_d_20_, v_a_21_, v_a_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___boxed(lean_object* v_n_24_, lean_object* v_d_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0(v_n_24_, v_d_25_, v_a_26_, v_a_27_);
lean_dec(v_n_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__0(lean_object* v_part_29_, lean_object* v_G_30_, lean_object* v_i_31_, lean_object* v_l_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lp_CORALean_CORALean_Partition_right___redArg(v_part_29_, v_l_32_);
v___x_34_ = lean_apply_2(v_G_30_, v_i_31_, v___x_33_);
v___x_35_ = lp_mathlib_abs___at___00EReal_abs_spec__0(v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__1(lean_object* v_part_36_, lean_object* v_G_37_, lean_object* v_r_38_, lean_object* v_i_39_){
_start:
{
lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___f_40_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__0), 4, 3);
lean_closure_set(v___f_40_, 0, v_part_36_);
lean_closure_set(v___f_40_, 1, v_G_37_);
lean_closure_set(v___f_40_, 2, v_i_39_);
v___x_41_ = l_List_finRange(v_r_38_);
v___x_42_ = lp_CORALean_Finset_sum___at___00CORALean_Real_Interval_mtimes_spec__0___redArg(v___x_41_, v___f_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__2(lean_object* v___f_43_, lean_object* v_i_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg(v___f_43_, v_i_44_, v___y_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__3(lean_object* v_part_47_, lean_object* v_G_48_, lean_object* v_i_49_, lean_object* v_l_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lp_CORALean_CORALean_Partition_left___redArg(v_part_47_, v_l_50_);
v___x_52_ = lean_apply_2(v_G_48_, v_i_49_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__4(lean_object* v___f_53_, lean_object* v_part_54_, lean_object* v_G_55_, lean_object* v_q_56_, lean_object* v_i_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___f_59_; lean_object* v___f_60_; lean_object* v___x_61_; 
lean_inc(v_i_57_);
v___f_59_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__2), 3, 2);
lean_closure_set(v___f_59_, 0, v___f_53_);
lean_closure_set(v___f_59_, 1, v_i_57_);
v___f_60_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__3), 4, 3);
lean_closure_set(v___f_60_, 0, v_part_54_);
lean_closure_set(v___f_60_, 1, v_G_55_);
lean_closure_set(v___f_60_, 2, v_i_57_);
v___x_61_ = l_Fin_addCases___redArg(v_q_56_, v___f_60_, v___f_59_, v___y_58_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__4___boxed(lean_object* v___f_62_, lean_object* v_part_63_, lean_object* v_G_64_, lean_object* v_q_65_, lean_object* v_i_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__4(v___f_62_, v_part_63_, v_G_64_, v_q_65_, v_i_66_, v___y_67_);
lean_dec(v_q_65_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy(lean_object* v_n_69_, lean_object* v_q_70_, lean_object* v_r_71_, lean_object* v_Z_72_, lean_object* v_part_73_){
_start:
{
lean_object* v_c_74_; lean_object* v_G_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_85_; 
v_c_74_ = lean_ctor_get(v_Z_72_, 1);
v_G_75_ = lean_ctor_get(v_Z_72_, 2);
v_isSharedCheck_85_ = !lean_is_exclusive(v_Z_72_);
if (v_isSharedCheck_85_ == 0)
{
lean_object* v_unused_86_; 
v_unused_86_ = lean_ctor_get(v_Z_72_, 0);
lean_dec(v_unused_86_);
v___x_77_ = v_Z_72_;
v_isShared_78_ = v_isSharedCheck_85_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_G_75_);
lean_inc(v_c_74_);
lean_dec(v_Z_72_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_85_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___f_79_; lean_object* v___f_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
lean_inc(v_G_75_);
lean_inc_ref(v_part_73_);
v___f_79_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__1), 4, 3);
lean_closure_set(v___f_79_, 0, v_part_73_);
lean_closure_set(v___f_79_, 1, v_G_75_);
lean_closure_set(v___f_79_, 2, v_r_71_);
lean_inc(v_q_70_);
v___f_80_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__4___boxed), 6, 4);
lean_closure_set(v___f_80_, 0, v___f_79_);
lean_closure_set(v___f_80_, 1, v_part_73_);
lean_closure_set(v___f_80_, 2, v_G_75_);
lean_closure_set(v___f_80_, 3, v_q_70_);
v___x_81_ = lean_nat_add(v_q_70_, v_n_69_);
lean_dec(v_q_70_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 2, v___f_80_);
lean_ctor_set(v___x_77_, 0, v___x_81_);
v___x_83_ = v___x_77_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_c_74_);
lean_ctor_set(v_reuseFailAlloc_84_, 2, v___f_80_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___boxed(lean_object* v_n_87_, lean_object* v_q_88_, lean_object* v_r_89_, lean_object* v_Z_90_, lean_object* v_part_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = lp_CORALean_CORALean_Real_Zonotope_reduceBy(v_n_87_, v_q_88_, v_r_89_, v_Z_90_, v_part_91_);
lean_dec(v_n_87_);
return v_res_92_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Zonotope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Zonotope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
