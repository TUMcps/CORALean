// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Real.Operations.Map
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_map___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_map___redArg___lam__0(lean_object* v_G_1_, lean_object* v_f_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_G_1_, v_j_3_);
v___x_5_ = lean_apply_1(v_f_2_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_map___redArg(lean_object* v_f_6_, lean_object* v_Z_7_){
_start:
{
lean_object* v_h_8_; lean_object* v_c_9_; lean_object* v_G_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_19_; 
v_h_8_ = lean_ctor_get(v_Z_7_, 0);
v_c_9_ = lean_ctor_get(v_Z_7_, 1);
v_G_10_ = lean_ctor_get(v_Z_7_, 2);
v_isSharedCheck_19_ = !lean_is_exclusive(v_Z_7_);
if (v_isSharedCheck_19_ == 0)
{
v___x_12_ = v_Z_7_;
v_isShared_13_ = v_isSharedCheck_19_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_G_10_);
lean_inc(v_c_9_);
lean_inc(v_h_8_);
lean_dec(v_Z_7_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_19_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___f_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_f_6_);
v___f_14_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Real_Zonotope_map___redArg___lam__0), 3, 2);
lean_closure_set(v___f_14_, 0, v_G_10_);
lean_closure_set(v___f_14_, 1, v_f_6_);
v___x_15_ = lean_apply_1(v_f_6_, v_c_9_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 2, v___f_14_);
lean_ctor_set(v___x_12_, 1, v___x_15_);
v___x_17_ = v___x_12_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_h_8_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_18_, 2, v___f_14_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_map(lean_object* v_00_u03b1_20_, lean_object* v_00_u03b2_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_f_26_, lean_object* v_Z_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_CORALean_CORALean_Real_Zonotope_map___redArg(v_f_26_, v_Z_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_map___boxed(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_f_35_, lean_object* v_Z_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_CORALean_CORALean_Real_Zonotope_map(v_00_u03b1_29_, v_00_u03b2_30_, v_inst_31_, v_inst_32_, v_inst_33_, v_inst_34_, v_f_35_, v_Z_36_);
lean_dec(v_inst_34_);
lean_dec_ref(v_inst_33_);
lean_dec(v_inst_32_);
lean_dec_ref(v_inst_31_);
return v_res_37_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Zonotope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_Map(uint8_t builtin) {
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
