// Lean compiler output
// Module: CORALean.Float.ContSet.Zonotope.Operations.GeneratorError
// Imports: public import Init public meta import Init public import CORALean.Float.ContSet.Zonotope.Zonotope
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
lean_object* lp_CORALean_CORALean_Float_radius___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Interval_symmetric___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_generatorError___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_generatorError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_generatorError___redArg(lean_object* v_inst_1_, lean_object* v_n_2_, lean_object* v_h_3_, lean_object* v_G_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
lean_inc_ref(v_inst_1_);
v___x_5_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_radius___boxed), 6, 5);
lean_closure_set(v___x_5_, 0, lean_box(0));
lean_closure_set(v___x_5_, 1, v_inst_1_);
lean_closure_set(v___x_5_, 2, v_n_2_);
lean_closure_set(v___x_5_, 3, v_h_3_);
lean_closure_set(v___x_5_, 4, v_G_4_);
v___x_6_ = lp_CORALean_CORALean_Float_Interval_symmetric___redArg(v_inst_1_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_Zonotope_generatorError(lean_object* v_00_U0001d54b_7_, lean_object* v_inst_8_, lean_object* v_n_9_, lean_object* v_h_10_, lean_object* v_G_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_CORALean_CORALean_Float_Zonotope_generatorError___redArg(v_inst_8_, v_n_9_, v_h_10_, v_G_11_);
return v___x_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Zonotope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Float_ContSet_Zonotope_Operations_GeneratorError(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_ContSet_Zonotope_Zonotope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
