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
lean_object* l_Fin_addCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_CORALean_Finset_sum___at___00dotProduct___at___00CORALean_matMulLeft_spec__0_spec__0___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__0(lean_object* v_part_29_, lean_object* v_G_30_, lean_object* v_l_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lp_CORALean_CORALean_Partition_left___redArg(v_part_29_, v_l_31_);
v___x_34_ = lean_apply_2(v_G_30_, v___x_33_, v___y_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__1(lean_object* v_part_35_, lean_object* v_G_36_, lean_object* v_i_37_, lean_object* v_l_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lp_CORALean_CORALean_Partition_right___redArg(v_part_35_, v_l_38_);
v___x_40_ = lean_apply_2(v_G_36_, v___x_39_, v_i_37_);
v___x_41_ = lp_mathlib_abs___at___00EReal_abs_spec__0(v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__2(lean_object* v_part_42_, lean_object* v_G_43_, lean_object* v_r_44_, lean_object* v_i_45_){
_start:
{
lean_object* v___f_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___f_46_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__1), 4, 3);
lean_closure_set(v___f_46_, 0, v_part_42_);
lean_closure_set(v___f_46_, 1, v_G_43_);
lean_closure_set(v___f_46_, 2, v_i_45_);
v___x_47_ = l_List_finRange(v_r_44_);
v___x_48_ = lp_CORALean_Finset_sum___at___00dotProduct___at___00CORALean_matMulLeft_spec__0_spec__0___redArg(v___x_47_, v___f_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__3(lean_object* v___f_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lp_CORALean_Matrix_diagonal___at___00CORALean_Real_Zonotope_reduceBy_spec__0___redArg(v___f_49_, v___y_50_, v___y_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__4(lean_object* v_q_53_, lean_object* v___f_54_, lean_object* v___f_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_106__overap_58_; lean_object* v___x_59_; 
v___x_106__overap_58_ = l_Fin_addCases___redArg(v_q_53_, v___f_54_, v___f_55_, v___y_56_);
v___x_59_ = lean_apply_1(v___x_106__overap_58_, v___y_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__4___boxed(lean_object* v_q_60_, lean_object* v___f_61_, lean_object* v___f_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__4(v_q_60_, v___f_61_, v___f_62_, v___y_63_, v___y_64_);
lean_dec(v_q_60_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy(lean_object* v_n_66_, lean_object* v_q_67_, lean_object* v_r_68_, lean_object* v_Z_69_, lean_object* v_part_70_){
_start:
{
lean_object* v_c_71_; lean_object* v_G_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_84_; 
v_c_71_ = lean_ctor_get(v_Z_69_, 1);
v_G_72_ = lean_ctor_get(v_Z_69_, 2);
v_isSharedCheck_84_ = !lean_is_exclusive(v_Z_69_);
if (v_isSharedCheck_84_ == 0)
{
lean_object* v_unused_85_; 
v_unused_85_ = lean_ctor_get(v_Z_69_, 0);
lean_dec(v_unused_85_);
v___x_74_ = v_Z_69_;
v_isShared_75_ = v_isSharedCheck_84_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_G_72_);
lean_inc(v_c_71_);
lean_dec(v_Z_69_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_84_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___f_76_; lean_object* v___f_77_; lean_object* v___f_78_; lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
lean_inc(v_G_72_);
lean_inc_ref(v_part_70_);
v___f_76_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__0), 4, 2);
lean_closure_set(v___f_76_, 0, v_part_70_);
lean_closure_set(v___f_76_, 1, v_G_72_);
v___f_77_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__2), 4, 3);
lean_closure_set(v___f_77_, 0, v_part_70_);
lean_closure_set(v___f_77_, 1, v_G_72_);
lean_closure_set(v___f_77_, 2, v_r_68_);
v___f_78_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__3), 3, 1);
lean_closure_set(v___f_78_, 0, v___f_77_);
lean_inc(v_q_67_);
v___f_79_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_reduceBy___lam__4___boxed), 5, 3);
lean_closure_set(v___f_79_, 0, v_q_67_);
lean_closure_set(v___f_79_, 1, v___f_76_);
lean_closure_set(v___f_79_, 2, v___f_78_);
v___x_80_ = lean_nat_add(v_q_67_, v_n_66_);
lean_dec(v_q_67_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 2, v___f_79_);
lean_ctor_set(v___x_74_, 0, v___x_80_);
v___x_82_ = v___x_74_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_c_71_);
lean_ctor_set(v_reuseFailAlloc_83_, 2, v___f_79_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_reduceBy___boxed(lean_object* v_n_86_, lean_object* v_q_87_, lean_object* v_r_88_, lean_object* v_Z_89_, lean_object* v_part_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = lp_CORALean_CORALean_Real_Zonotope_reduceBy(v_n_86_, v_q_87_, v_r_88_, v_Z_89_, v_part_90_);
lean_dec(v_n_86_);
return v_res_91_;
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
