// Lean compiler output
// Module: CORALean.ContSet.Zonotope.Real.Operations.LinMtimes
// Imports: public import Init public meta import Init public import CORALean.ContSet.Zonotope.Real.Operations.Map
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
lean_object* lp_CORALean_CORALean_Real_Zonotope_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mapOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mapOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mapOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mapOf___redArg(lean_object* v_f_1_, lean_object* v_Z_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lp_CORALean_CORALean_Real_Zonotope_map___redArg(v_f_1_, v_Z_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mapOf(lean_object* v_00_u03b1_4_, lean_object* v_00_u03b2_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_f_10_, lean_object* v_Z_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_CORALean_CORALean_Real_Zonotope_map___redArg(v_f_10_, v_Z_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_Zonotope_mapOf___boxed(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_f_19_, lean_object* v_Z_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_CORALean_CORALean_Real_Zonotope_mapOf(v_00_u03b1_13_, v_00_u03b2_14_, v_inst_15_, v_inst_16_, v_inst_17_, v_inst_18_, v_f_19_, v_Z_20_);
lean_dec(v_inst_18_);
lean_dec_ref(v_inst_17_);
lean_dec(v_inst_16_);
lean_dec_ref(v_inst_15_);
return v_res_21_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_Map(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_LinMtimes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_ContSet_Zonotope_Real_Operations_Map(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
