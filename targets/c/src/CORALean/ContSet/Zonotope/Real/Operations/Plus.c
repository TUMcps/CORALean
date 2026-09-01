// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Real.Operations.Plus
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Fin_append___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus___redArg(lean_object* v_inst_1_, lean_object* v_Z_u2081_2_, lean_object* v_Z_u2082_3_){
_start:
{
lean_object* v_toAddMonoid_4_; lean_object* v_h_5_; lean_object* v_c_6_; lean_object* v_G_7_; lean_object* v_h_8_; lean_object* v_c_9_; lean_object* v_G_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_21_; 
v_toAddMonoid_4_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toAddMonoid_4_);
lean_dec_ref(v_inst_1_);
v_h_5_ = lean_ctor_get(v_Z_u2081_2_, 0);
lean_inc(v_h_5_);
v_c_6_ = lean_ctor_get(v_Z_u2081_2_, 1);
lean_inc(v_c_6_);
v_G_7_ = lean_ctor_get(v_Z_u2081_2_, 2);
lean_inc(v_G_7_);
lean_dec_ref(v_Z_u2081_2_);
v_h_8_ = lean_ctor_get(v_Z_u2082_3_, 0);
v_c_9_ = lean_ctor_get(v_Z_u2082_3_, 1);
v_G_10_ = lean_ctor_get(v_Z_u2082_3_, 2);
v_isSharedCheck_21_ = !lean_is_exclusive(v_Z_u2082_3_);
if (v_isSharedCheck_21_ == 0)
{
v___x_12_ = v_Z_u2082_3_;
v_isShared_13_ = v_isSharedCheck_21_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_G_10_);
lean_inc(v_c_9_);
lean_inc(v_h_8_);
lean_dec(v_Z_u2082_3_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_21_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v_toAddSemigroup_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_19_; 
v_toAddSemigroup_14_ = lean_ctor_get(v_toAddMonoid_4_, 0);
lean_inc(v_toAddSemigroup_14_);
lean_dec_ref(v_toAddMonoid_4_);
v___x_15_ = lean_nat_add(v_h_5_, v_h_8_);
v___x_16_ = lean_apply_2(v_toAddSemigroup_14_, v_c_6_, v_c_9_);
v___x_17_ = lean_alloc_closure((void*)(lp_mathlib_Fin_append___boxed), 6, 5);
lean_closure_set(v___x_17_, 0, v_h_5_);
lean_closure_set(v___x_17_, 1, v_h_8_);
lean_closure_set(v___x_17_, 2, lean_box(0));
lean_closure_set(v___x_17_, 3, v_G_7_);
lean_closure_set(v___x_17_, 4, v_G_10_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 2, v___x_17_);
lean_ctor_set(v___x_12_, 1, v___x_16_);
lean_ctor_set(v___x_12_, 0, v___x_15_);
v___x_19_ = v___x_12_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v___x_16_);
lean_ctor_set(v_reuseFailAlloc_20_, 2, v___x_17_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_plus(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_, lean_object* v_Z_u2081_24_, lean_object* v_Z_u2082_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_CORALean_CORALean_Real_Zonotope_plus___redArg(v_inst_23_, v_Z_u2081_24_, v_Z_u2082_25_);
return v___x_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Zonotope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_Plus(uint8_t builtin) {
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
