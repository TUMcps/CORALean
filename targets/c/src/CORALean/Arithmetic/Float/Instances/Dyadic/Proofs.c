// Lean compiler output
// Module: CORALean.Arithmetic.Float.Instances.Dyadic.Proofs
// Imports: public import Init public meta import Init public import CORALean.Arithmetic.Float.Instances.Dyadic.Proofs.Exact public import CORALean.Arithmetic.Float.Instances.Dyadic.Proofs.Rounding public import CORALean.Arithmetic.Float.Instances.Dyadic.Proofs.Order
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Arithmetic_Float_Instances_Dyadic_Proofs_Exact(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Arithmetic_Float_Instances_Dyadic_Proofs_Rounding(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Arithmetic_Float_Instances_Dyadic_Proofs_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Arithmetic_Float_Instances_Dyadic_Proofs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Arithmetic_Float_Instances_Dyadic_Proofs_Exact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Arithmetic_Float_Instances_Dyadic_Proofs_Rounding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Arithmetic_Float_Instances_Dyadic_Proofs_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
