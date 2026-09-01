// Lean compiler output
// Module: CORALean.Global.Sort
// Imports: public import Init public meta import Init public import CORALean.Global.Mathlib
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_mathlib_finCongr(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_findIdx_go___at___00List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_findIdx_go___at___00List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_sortPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_findIdx_go___at___00List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_findIdx_go___at___00List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg___lam__0(lean_object* v_l_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_List_get___redArg(v_l_1_, v_i_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg___lam__0___boxed(lean_object* v_l_4_, lean_object* v_i_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg___lam__0(v_l_4_, v_i_5_);
lean_dec(v_l_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_List_findIdx_go___at___00List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0_spec__1___redArg(lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
if (lean_obj_tag(v_a_8_) == 0)
{
return v_a_9_;
}
else
{
lean_object* v_head_10_; lean_object* v_tail_11_; uint8_t v___x_12_; 
v_head_10_ = lean_ctor_get(v_a_8_, 0);
v_tail_11_ = lean_ctor_get(v_a_8_, 1);
v___x_12_ = lean_nat_dec_eq(v_head_10_, v_a_7_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = lean_nat_add(v_a_9_, v___x_13_);
lean_dec(v_a_9_);
v_a_8_ = v_tail_11_;
v_a_9_ = v___x_14_;
goto _start;
}
else
{
return v_a_9_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_List_findIdx_go___at___00List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_CORALean_List_findIdx_go___at___00List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0_spec__1___redArg(v_a_16_, v_a_17_, v_a_18_);
lean_dec(v_a_17_);
lean_dec(v_a_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0(lean_object* v_n_20_, lean_object* v_a_21_, lean_object* v_l_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lp_CORALean_List_findIdx_go___at___00List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0_spec__1___redArg(v_a_21_, v_l_22_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0___boxed(lean_object* v_n_25_, lean_object* v_a_26_, lean_object* v_l_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_CORALean_List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0(v_n_25_, v_a_26_, v_l_27_);
lean_dec(v_l_27_);
lean_dec(v_a_26_);
lean_dec(v_n_25_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg___lam__1(lean_object* v_n_29_, lean_object* v_l_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_CORALean_List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0(v_n_29_, v_a_31_, v_l_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg___lam__1___boxed(lean_object* v_n_33_, lean_object* v_l_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg___lam__1(v_n_33_, v_l_34_, v_a_35_);
lean_dec(v_a_35_);
lean_dec(v_l_34_);
lean_dec(v_n_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg(lean_object* v_n_37_, lean_object* v_l_38_){
_start:
{
lean_object* v___f_39_; lean_object* v___f_40_; lean_object* v___x_41_; 
lean_inc(v_l_38_);
v___f_39_ = lean_alloc_closure((void*)(lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_39_, 0, v_l_38_);
v___f_40_ = lean_alloc_closure((void*)(lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_40_, 0, v_n_37_);
lean_closure_set(v___f_40_, 1, v_l_38_);
v___x_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_41_, 0, v___f_39_);
lean_ctor_set(v___x_41_, 1, v___f_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_sortPerm(lean_object* v_n_42_, lean_object* v_r_43_){
_start:
{
lean_object* v___x_44_; lean_object* v_l_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
lean_inc(v_n_42_);
v___x_44_ = l_List_finRange(v_n_42_);
v_l_45_ = l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(v___x_44_, v_r_43_);
v___x_46_ = l_List_lengthTR___redArg(v_l_45_);
v___x_47_ = lp_mathlib_finCongr(v_n_42_, v___x_46_, lean_box(0));
lean_dec(v___x_46_);
v___x_48_ = lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg(v_n_42_, v_l_45_);
v___x_49_ = lp_mathlib_Equiv_trans___redArg(v___x_47_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0(lean_object* v_n_50_, lean_object* v_l_51_, lean_object* v_nd_52_, lean_object* v_h_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_CORALean_List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0___redArg(v_n_50_, v_l_51_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_List_findIdx_go___at___00List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0_spec__1(lean_object* v_n_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_CORALean_List_findIdx_go___at___00List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0_spec__1___redArg(v_a_56_, v_a_57_, v_a_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_List_findIdx_go___at___00List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0_spec__1___boxed(lean_object* v_n_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_CORALean_List_findIdx_go___at___00List_idxOf___at___00List_Nodup_getEquivOfForallMemList___at___00CORALean_sortPerm_spec__0_spec__0_spec__1(v_n_60_, v_a_61_, v_a_62_, v_a_63_);
lean_dec(v_a_62_);
lean_dec(v_a_61_);
lean_dec(v_n_60_);
return v_res_64_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Global_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Global_Sort(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Global_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
