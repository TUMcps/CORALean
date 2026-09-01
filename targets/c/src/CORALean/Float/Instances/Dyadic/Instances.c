// Lean compiler output
// Module: CORALean.Float.Instances.Dyadic.Instances
// Imports: public import Init public meta import Init public import CORALean.Float.Instances.Dyadic.Theorems.API
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_CORALean_CORALean_Float_Dyadic_neg___boxed(lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Dyadic_addUp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Dyadic_addDown___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Dyadic_mulUp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Dyadic_mulDown___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Dyadic_minimum___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Dyadic_maximum___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Dyadic_le___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_CORALean_CORALean_Float_Dyadic_half___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_CORALean_CORALean_Float_instFloatOpsDyadic___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_CORALean_CORALean_Float_instFloatOpsDyadic___closed__0;
static lean_once_cell_t lp_CORALean_CORALean_Float_instFloatOpsDyadic___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_CORALean_CORALean_Float_instFloatOpsDyadic___closed__1;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instFloatOpsDyadic(lean_object*);
static lean_object* _init_lp_CORALean_CORALean_Float_instFloatOpsDyadic___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_CORALean_CORALean_Float_instFloatOpsDyadic___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_CORALean_CORALean_Float_instFloatOpsDyadic___closed__0, &lp_CORALean_CORALean_Float_instFloatOpsDyadic___closed__0_once, _init_lp_CORALean_CORALean_Float_instFloatOpsDyadic___closed__0);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
lean_ctor_set(v___x_4_, 1, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Float_instFloatOpsDyadic(lean_object* v_p_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_6_ = lean_obj_once(&lp_CORALean_CORALean_Float_instFloatOpsDyadic___closed__1, &lp_CORALean_CORALean_Float_instFloatOpsDyadic___closed__1_once, _init_lp_CORALean_CORALean_Float_instFloatOpsDyadic___closed__1);
lean_inc_n(v_p_5_, 8);
v___x_7_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Dyadic_neg___boxed), 2, 1);
lean_closure_set(v___x_7_, 0, v_p_5_);
v___x_8_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Dyadic_addUp___boxed), 3, 1);
lean_closure_set(v___x_8_, 0, v_p_5_);
v___x_9_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Dyadic_addDown___boxed), 3, 1);
lean_closure_set(v___x_9_, 0, v_p_5_);
v___x_10_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Dyadic_mulUp___boxed), 3, 1);
lean_closure_set(v___x_10_, 0, v_p_5_);
v___x_11_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Dyadic_mulDown___boxed), 3, 1);
lean_closure_set(v___x_11_, 0, v_p_5_);
v___x_12_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Dyadic_minimum___boxed), 3, 1);
lean_closure_set(v___x_12_, 0, v_p_5_);
v___x_13_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Dyadic_maximum___boxed), 3, 1);
lean_closure_set(v___x_13_, 0, v_p_5_);
v___x_14_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Dyadic_le___boxed), 3, 1);
lean_closure_set(v___x_14_, 0, v_p_5_);
v___x_15_ = lean_alloc_closure((void*)(lp_CORALean_CORALean_Float_Dyadic_half___boxed), 2, 1);
lean_closure_set(v___x_15_, 0, v_p_5_);
v___x_16_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_16_, 0, v___x_6_);
lean_ctor_set(v___x_16_, 1, v___x_7_);
lean_ctor_set(v___x_16_, 2, v___x_8_);
lean_ctor_set(v___x_16_, 3, v___x_9_);
lean_ctor_set(v___x_16_, 4, v___x_10_);
lean_ctor_set(v___x_16_, 5, v___x_11_);
lean_ctor_set(v___x_16_, 6, v___x_12_);
lean_ctor_set(v___x_16_, 7, v___x_13_);
lean_ctor_set(v___x_16_, 8, v___x_14_);
lean_ctor_set(v___x_16_, 9, v___x_15_);
return v___x_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Float_Instances_Dyadic_Theorems_API(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Float_Instances_Dyadic_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CORALean_CORALean_Float_Instances_Dyadic_Theorems_API(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
