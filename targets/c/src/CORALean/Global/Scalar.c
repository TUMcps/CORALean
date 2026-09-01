// Lean compiler output
// Module: CORALean.Global.Scalar
// Imports: public import Init public meta import Init public import CORALean.Global.Tensor
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instScalarReal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instScalarReal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_CORALean_CORALean_instScalarReal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_CORALean_CORALean_instScalarReal___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_CORALean_CORALean_instScalarReal___closed__0 = (const lean_object*)&lp_CORALean_CORALean_instScalarReal___closed__0_value;
LEAN_EXPORT const lean_object* lp_CORALean_CORALean_instScalarReal = (const lean_object*)&lp_CORALean_CORALean_instScalarReal___closed__0_value;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instScalarReal___lam__0(lean_object* v_m_1_, lean_object* v_n_2_, lean_object* v_M_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_apply_2(v_M_3_, v___y_4_, v___y_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instScalarReal___lam__0___boxed(lean_object* v_m_7_, lean_object* v_n_8_, lean_object* v_M_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_CORALean_CORALean_instScalarReal___lam__0(v_m_7_, v_n_8_, v_M_9_, v___y_10_, v___y_11_);
lean_dec(v_n_8_);
lean_dec(v_m_7_);
return v_res_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Global_Tensor(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Global_Scalar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Global_Tensor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
