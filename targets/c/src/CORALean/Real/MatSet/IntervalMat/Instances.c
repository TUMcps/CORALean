// Lean compiler output
// Module: CORALean.Real.MatSet.IntervalMat.Instances
// Imports: public import Init public meta import Init public import CORALean.Real.MatSet.IntervalMat.IntervalMat
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
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Real_instMatSetIntervalMat;
static lean_object* _init_lp_CORALean_CORALean_Real_instMatSetIntervalMat(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Real_MatSet_IntervalMat_IntervalMat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Real_MatSet_IntervalMat_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Real_MatSet_IntervalMat_IntervalMat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_CORALean_CORALean_Real_instMatSetIntervalMat = _init_lp_CORALean_CORALean_Real_instMatSetIntervalMat();
lean_mark_persistent(lp_CORALean_CORALean_Real_instMatSetIntervalMat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
