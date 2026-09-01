// Lean compiler output
// Module: CORALean.ContSet.ContSet.ContSet
// Imports: public import Init public meta import Init public import CORALean.Global.API
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instContSetMatRealOfScalar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instContSetMatRealOfScalar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instContSetMatRealOfScalar(lean_object* v_00_U0001d54b_1_, lean_object* v_inst_2_, lean_object* v_m_3_, lean_object* v_n_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_box(0);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instContSetMatRealOfScalar___boxed(lean_object* v_00_U0001d54b_6_, lean_object* v_inst_7_, lean_object* v_m_8_, lean_object* v_n_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_CORALean_CORALean_instContSetMatRealOfScalar(v_00_U0001d54b_6_, v_inst_7_, v_m_8_, v_n_9_);
lean_dec(v_n_9_);
lean_dec(v_m_8_);
lean_dec(v_inst_7_);
return v_res_10_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Global_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_ContSet_ContSet_ContSet(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Global_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
