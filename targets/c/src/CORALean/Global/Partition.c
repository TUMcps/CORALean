// Lean compiler output
// Module: CORALean.Global.Partition
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_finSumFinEquiv(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
static const lean_string_object lp_CORALean_CORALean_termSplit__Into___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CORALean"};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__0 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__0_value;
static const lean_string_object lp_CORALean_CORALean_termSplit__Into___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "termSplit_Into_"};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__1 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__1_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 160, 144, 195, 199, 248, 246, 52)}};
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__2_value_aux_0),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 135, 239, 76, 71, 187, 235, 50)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__2 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__2_value;
static const lean_string_object lp_CORALean_CORALean_termSplit__Into___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__3 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__3_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__4 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__4_value;
static const lean_string_object lp_CORALean_CORALean_termSplit__Into___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Split "};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__5 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__5_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__5_value)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__6 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__6_value;
static const lean_string_object lp_CORALean_CORALean_termSplit__Into___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__7 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__7_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__8 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__8_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__8_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__9 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__9_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__4_value),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__6_value),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__9_value)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__10 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__10_value;
static const lean_string_object lp_CORALean_CORALean_termSplit__Into___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " into "};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__11 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__11_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__11_value)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__12 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__12_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__4_value),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__10_value),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__12_value)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__13 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__13_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__4_value),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__13_value),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__9_value)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__14 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__14_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into___00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__2_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__14_value)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into___00__closed__15 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__15_value;
LEAN_EXPORT const lean_object* lp_CORALean_CORALean_termSplit__Into__ = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__15_value;
static const lean_string_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__0 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__0_value;
static const lean_string_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__1 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__1_value;
static const lean_string_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__2 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__2_value;
static const lean_string_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__3 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__3_value;
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4_value_aux_0),((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4_value_aux_1),((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4_value_aux_2),((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4_value;
static const lean_string_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "CORALean.Partition"};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__5 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__5_value;
static lean_once_cell_t lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__6;
static const lean_string_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Partition"};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__7 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__7_value;
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 160, 144, 195, 199, 248, 246, 52)}};
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__8_value_aux_0),((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 41, 252, 19, 3, 158, 46, 89)}};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__8 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__8_value;
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__9 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__9_value;
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__8_value)}};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__10 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__10_value;
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__11 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__11_value;
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__9_value),((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__11_value)}};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__12 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__12_value;
static const lean_string_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__13 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__13_value;
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__14 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__14_value;
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1___closed__0 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1___closed__0_value;
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1___closed__1 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1___closed__1_value;
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_CORALean_CORALean_termSplit__Into__And___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "termSplit_Into_And_"};
static const lean_object* lp_CORALean_CORALean_termSplit__Into__And___00__closed__0 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__0_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into__And___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 160, 144, 195, 199, 248, 246, 52)}};
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into__And___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__1_value_aux_0),((lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 208, 132, 104, 231, 0, 132, 172)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into__And___00__closed__1 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__1_value;
static const lean_string_object lp_CORALean_CORALean_termSplit__Into__And___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " and "};
static const lean_object* lp_CORALean_CORALean_termSplit__Into__And___00__closed__2 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__2_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into__And___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__2_value)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into__And___00__closed__3 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__3_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into__And___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__4_value),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__14_value),((lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__3_value)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into__And___00__closed__4 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__4_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into__And___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__4_value),((lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__4_value),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__9_value)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into__And___00__closed__5 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__5_value;
static const lean_ctor_object lp_CORALean_CORALean_termSplit__Into__And___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__5_value)}};
static const lean_object* lp_CORALean_CORALean_termSplit__Into__And___00__closed__6 = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__6_value;
LEAN_EXPORT const lean_object* lp_CORALean_CORALean_termSplit__Into__And__ = (const lean_object*)&lp_CORALean_CORALean_termSplit__Into__And___00__closed__6_value;
static const lean_string_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 19, .m_data = "CORALean.Partition₂"};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__0 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__0_value;
static lean_once_cell_t lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__1;
static const lean_string_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 10, .m_data = "Partition₂"};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__2 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__2_value;
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_CORALean_CORALean_termSplit__Into___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 160, 144, 195, 199, 248, 246, 52)}};
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__3_value_aux_0),((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 119, 242, 244, 43, 14, 242, 199)}};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__3 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__3_value;
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__4 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__4_value;
static const lean_ctor_object lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__5 = (const lean_object*)&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__5_value;
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition_u2082__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition_u2082__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__3___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Pair_equivSum___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Pair_equivSum___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Pair_equivSum___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Pair_equivSum___lam__1___boxed(lean_object*);
static const lean_closure_object lp_CORALean_CORALean_Pair_equivSum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_CORALean_CORALean_Pair_equivSum___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_CORALean_CORALean_Pair_equivSum___closed__0 = (const lean_object*)&lp_CORALean_CORALean_Pair_equivSum___closed__0_value;
static const lean_closure_object lp_CORALean_CORALean_Pair_equivSum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_CORALean_CORALean_Pair_equivSum___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_CORALean_CORALean_Pair_equivSum___closed__1 = (const lean_object*)&lp_CORALean_CORALean_Pair_equivSum___closed__1_value;
static const lean_ctor_object lp_CORALean_CORALean_Pair_equivSum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_CORALean_CORALean_Pair_equivSum___closed__0_value),((lean_object*)&lp_CORALean_CORALean_Pair_equivSum___closed__1_value)}};
static const lean_object* lp_CORALean_CORALean_Pair_equivSum___closed__2 = (const lean_object*)&lp_CORALean_CORALean_Pair_equivSum___closed__2_value;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Pair_equivSum(lean_object*, lean_object*);
static lean_once_cell_t lp_CORALean_CORALean_Partition_split___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_CORALean_CORALean_Partition_split___closed__0;
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_split(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_reindex___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_reindex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_on___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_on(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_left___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_left(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_right___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_right(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__6(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__5));
v___x_49_ = l_String_toRawSubstring_x27(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1(lean_object* v_x_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = ((lean_object*)(lp_CORALean_CORALean_termSplit__Into___00__closed__2));
lean_inc(v_x_68_);
v___x_72_ = l_Lean_Syntax_isOfKind(v_x_68_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v_x_68_);
v___x_73_ = lean_box(1);
v___x_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v_a_70_);
return v___x_74_;
}
else
{
lean_object* v_quotContext_75_; lean_object* v_currMacroScope_76_; lean_object* v_ref_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_quotContext_75_ = lean_ctor_get(v_a_69_, 1);
v_currMacroScope_76_ = lean_ctor_get(v_a_69_, 2);
v_ref_77_ = lean_ctor_get(v_a_69_, 5);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = l_Lean_Syntax_getArg(v_x_68_, v___x_78_);
v___x_80_ = lean_unsigned_to_nat(3u);
v___x_81_ = l_Lean_Syntax_getArg(v_x_68_, v___x_80_);
lean_dec(v_x_68_);
v___x_82_ = 0;
v___x_83_ = l_Lean_SourceInfo_fromRef(v_ref_77_, v___x_82_);
v___x_84_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4));
v___x_85_ = lean_obj_once(&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__6, &lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__6_once, _init_lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__6);
v___x_86_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__8));
lean_inc(v_currMacroScope_76_);
lean_inc(v_quotContext_75_);
v___x_87_ = l_Lean_addMacroScope(v_quotContext_75_, v___x_86_, v_currMacroScope_76_);
v___x_88_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__12));
lean_inc_n(v___x_83_, 2);
v___x_89_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_89_, 0, v___x_83_);
lean_ctor_set(v___x_89_, 1, v___x_85_);
lean_ctor_set(v___x_89_, 2, v___x_87_);
lean_ctor_set(v___x_89_, 3, v___x_88_);
v___x_90_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__14));
v___x_91_ = l_Lean_Syntax_node2(v___x_83_, v___x_90_, v___x_79_, v___x_81_);
v___x_92_ = l_Lean_Syntax_node2(v___x_83_, v___x_84_, v___x_89_, v___x_91_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v_a_70_);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___boxed(lean_object* v_x_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1(v_x_94_, v_a_95_, v_a_96_);
lean_dec_ref(v_a_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1(lean_object* v_x_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4));
lean_inc(v_x_101_);
v___x_105_ = l_Lean_Syntax_isOfKind(v_x_101_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v_x_101_);
v___x_106_ = lean_box(0);
v___x_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_a_103_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = l_Lean_Syntax_getArg(v_x_101_, v___x_108_);
v___x_110_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1___closed__1));
lean_inc(v___x_109_);
v___x_111_ = l_Lean_Syntax_isOfKind(v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v___x_109_);
lean_dec(v_x_101_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_a_103_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = l_Lean_Syntax_getArg(v_x_101_, v___x_114_);
lean_dec(v_x_101_);
v___x_116_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_115_);
v___x_117_ = l_Lean_Syntax_matchesNull(v___x_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v___x_115_);
lean_dec(v___x_109_);
v___x_118_ = lean_box(0);
v___x_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_a_103_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_ref_122_; uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_120_ = l_Lean_Syntax_getArg(v___x_115_, v___x_108_);
v___x_121_ = l_Lean_Syntax_getArg(v___x_115_, v___x_114_);
lean_dec(v___x_115_);
v_ref_122_ = l_Lean_replaceRef(v___x_109_, v_a_102_);
lean_dec(v___x_109_);
v___x_123_ = 0;
v___x_124_ = l_Lean_SourceInfo_fromRef(v_ref_122_, v___x_123_);
lean_dec(v_ref_122_);
v___x_125_ = ((lean_object*)(lp_CORALean_CORALean_termSplit__Into___00__closed__2));
v___x_126_ = ((lean_object*)(lp_CORALean_CORALean_termSplit__Into___00__closed__5));
lean_inc_n(v___x_124_, 2);
v___x_127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_124_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = ((lean_object*)(lp_CORALean_CORALean_termSplit__Into___00__closed__11));
v___x_129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_124_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = l_Lean_Syntax_node4(v___x_124_, v___x_125_, v___x_127_, v___x_120_, v___x_129_, v___x_121_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_a_103_);
return v___x_131_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1___boxed(lean_object* v_x_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1(v_x_132_, v_a_133_, v_a_134_);
lean_dec(v_a_133_);
return v_res_135_;
}
}
static lean_object* _init_lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__1(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__0));
v___x_158_ = l_String_toRawSubstring_x27(v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1(lean_object* v_x_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = ((lean_object*)(lp_CORALean_CORALean_termSplit__Into__And___00__closed__1));
lean_inc(v_x_169_);
v___x_173_ = l_Lean_Syntax_isOfKind(v_x_169_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v_x_169_);
v___x_174_ = lean_box(1);
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v_a_171_);
return v___x_175_;
}
else
{
lean_object* v_quotContext_176_; lean_object* v_currMacroScope_177_; lean_object* v_ref_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_quotContext_176_ = lean_ctor_get(v_a_170_, 1);
v_currMacroScope_177_ = lean_ctor_get(v_a_170_, 2);
v_ref_178_ = lean_ctor_get(v_a_170_, 5);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = l_Lean_Syntax_getArg(v_x_169_, v___x_179_);
v___x_181_ = lean_unsigned_to_nat(3u);
v___x_182_ = l_Lean_Syntax_getArg(v_x_169_, v___x_181_);
v___x_183_ = lean_unsigned_to_nat(5u);
v___x_184_ = l_Lean_Syntax_getArg(v_x_169_, v___x_183_);
lean_dec(v_x_169_);
v___x_185_ = 0;
v___x_186_ = l_Lean_SourceInfo_fromRef(v_ref_178_, v___x_185_);
v___x_187_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4));
v___x_188_ = lean_obj_once(&lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__1, &lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__1_once, _init_lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__1);
v___x_189_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__3));
lean_inc(v_currMacroScope_177_);
lean_inc(v_quotContext_176_);
v___x_190_ = l_Lean_addMacroScope(v_quotContext_176_, v___x_189_, v_currMacroScope_177_);
v___x_191_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___closed__5));
lean_inc_n(v___x_186_, 2);
v___x_192_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_192_, 0, v___x_186_);
lean_ctor_set(v___x_192_, 1, v___x_188_);
lean_ctor_set(v___x_192_, 2, v___x_190_);
lean_ctor_set(v___x_192_, 3, v___x_191_);
v___x_193_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__14));
v___x_194_ = l_Lean_Syntax_node3(v___x_186_, v___x_193_, v___x_180_, v___x_182_, v___x_184_);
v___x_195_ = l_Lean_Syntax_node2(v___x_186_, v___x_187_, v___x_192_, v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_171_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1___boxed(lean_object* v_x_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into__And____1(v_x_197_, v_a_198_, v_a_199_);
lean_dec_ref(v_a_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition_u2082__1(lean_object* v_x_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______macroRules__CORALean__termSplit__Into____1___closed__4));
lean_inc(v_x_201_);
v___x_205_ = l_Lean_Syntax_isOfKind(v_x_201_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v_x_201_);
v___x_206_ = lean_box(0);
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v_a_203_);
return v___x_207_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = l_Lean_Syntax_getArg(v_x_201_, v___x_208_);
v___x_210_ = ((lean_object*)(lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition__1___closed__1));
lean_inc(v___x_209_);
v___x_211_ = l_Lean_Syntax_isOfKind(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v___x_209_);
lean_dec(v_x_201_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_a_203_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = l_Lean_Syntax_getArg(v_x_201_, v___x_214_);
lean_dec(v_x_201_);
v___x_216_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_215_);
v___x_217_ = l_Lean_Syntax_matchesNull(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v___x_215_);
lean_dec(v___x_209_);
v___x_218_ = lean_box(0);
v___x_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v_a_203_);
return v___x_219_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_ref_224_; uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_220_ = l_Lean_Syntax_getArg(v___x_215_, v___x_208_);
v___x_221_ = l_Lean_Syntax_getArg(v___x_215_, v___x_214_);
v___x_222_ = lean_unsigned_to_nat(2u);
v___x_223_ = l_Lean_Syntax_getArg(v___x_215_, v___x_222_);
lean_dec(v___x_215_);
v_ref_224_ = l_Lean_replaceRef(v___x_209_, v_a_202_);
lean_dec(v___x_209_);
v___x_225_ = 0;
v___x_226_ = l_Lean_SourceInfo_fromRef(v_ref_224_, v___x_225_);
lean_dec(v_ref_224_);
v___x_227_ = ((lean_object*)(lp_CORALean_CORALean_termSplit__Into__And___00__closed__1));
v___x_228_ = ((lean_object*)(lp_CORALean_CORALean_termSplit__Into___00__closed__5));
lean_inc_n(v___x_226_, 3);
v___x_229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_226_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = ((lean_object*)(lp_CORALean_CORALean_termSplit__Into___00__closed__11));
v___x_231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_226_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = ((lean_object*)(lp_CORALean_CORALean_termSplit__Into__And___00__closed__2));
v___x_233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_226_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = l_Lean_Syntax_node6(v___x_226_, v___x_227_, v___x_229_, v___x_220_, v___x_231_, v___x_221_, v___x_233_, v___x_223_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v_a_203_);
return v___x_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition_u2082__1___boxed(lean_object* v_x_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = lp_CORALean_CORALean___aux__CORALean__Global__Partition______unexpand__CORALean__Partition_u2082__1(v_x_236_, v_a_237_, v_a_238_);
lean_dec(v_a_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__1___redArg(lean_object* v_inst_240_){
_start:
{
lean_inc(v_inst_240_);
return v_inst_240_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__1___redArg___boxed(lean_object* v_inst_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = lp_CORALean_CORALean_instFintypePair___aux__1___redArg(v_inst_241_);
lean_dec(v_inst_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__1(lean_object* v_00_u03b2_243_, lean_object* v_00_u03b3_244_, lean_object* v_inst_245_){
_start:
{
lean_inc(v_inst_245_);
return v_inst_245_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__1___boxed(lean_object* v_00_u03b2_246_, lean_object* v_00_u03b3_247_, lean_object* v_inst_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = lp_CORALean_CORALean_instFintypePair___aux__1(v_00_u03b2_246_, v_00_u03b3_247_, v_inst_248_);
lean_dec(v_inst_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__3___redArg(lean_object* v_inst_250_){
_start:
{
lean_inc(v_inst_250_);
return v_inst_250_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__3___redArg___boxed(lean_object* v_inst_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = lp_CORALean_CORALean_instFintypePair___aux__3___redArg(v_inst_251_);
lean_dec(v_inst_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__3(lean_object* v_00_u03b2_253_, lean_object* v_00_u03b3_254_, lean_object* v_inst_255_){
_start:
{
lean_inc(v_inst_255_);
return v_inst_255_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___aux__3___boxed(lean_object* v_00_u03b2_256_, lean_object* v_00_u03b3_257_, lean_object* v_inst_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = lp_CORALean_CORALean_instFintypePair___aux__3(v_00_u03b2_256_, v_00_u03b3_257_, v_inst_258_);
lean_dec(v_inst_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___redArg(lean_object* v_inst_260_, lean_object* v_inst_261_, uint8_t v_x_262_){
_start:
{
if (v_x_262_ == 0)
{
lean_inc(v_inst_261_);
return v_inst_261_;
}
else
{
lean_inc(v_inst_260_);
return v_inst_260_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___redArg___boxed(lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_x_24__boxed_266_; lean_object* v_res_267_; 
v_x_24__boxed_266_ = lean_unbox(v_x_265_);
v_res_267_ = lp_CORALean_CORALean_instFintypePair___redArg(v_inst_263_, v_inst_264_, v_x_24__boxed_266_);
lean_dec(v_inst_264_);
lean_dec(v_inst_263_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair(lean_object* v_00_u03b2_268_, lean_object* v_00_u03b3_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, uint8_t v_x_272_){
_start:
{
if (v_x_272_ == 0)
{
lean_inc(v_inst_271_);
return v_inst_271_;
}
else
{
lean_inc(v_inst_270_);
return v_inst_270_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_instFintypePair___boxed(lean_object* v_00_u03b2_273_, lean_object* v_00_u03b3_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_x_277_){
_start:
{
uint8_t v_x_33__boxed_278_; lean_object* v_res_279_; 
v_x_33__boxed_278_ = lean_unbox(v_x_277_);
v_res_279_ = lp_CORALean_CORALean_instFintypePair(v_00_u03b2_273_, v_00_u03b3_274_, v_inst_275_, v_inst_276_, v_x_33__boxed_278_);
lean_dec(v_inst_276_);
lean_dec(v_inst_275_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Pair_equivSum___lam__0(lean_object* v_x_280_){
_start:
{
lean_object* v_fst_281_; uint8_t v___x_282_; 
v_fst_281_ = lean_ctor_get(v_x_280_, 0);
v___x_282_ = lean_unbox(v_fst_281_);
if (v___x_282_ == 0)
{
lean_object* v_snd_283_; lean_object* v___x_284_; 
v_snd_283_ = lean_ctor_get(v_x_280_, 1);
lean_inc(v_snd_283_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v_snd_283_);
return v___x_284_;
}
else
{
lean_object* v_snd_285_; lean_object* v___x_286_; 
v_snd_285_ = lean_ctor_get(v_x_280_, 1);
lean_inc(v_snd_285_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v_snd_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Pair_equivSum___lam__0___boxed(lean_object* v_x_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = lp_CORALean_CORALean_Pair_equivSum___lam__0(v_x_287_);
lean_dec_ref(v_x_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Pair_equivSum___lam__1(lean_object* v_s_289_){
_start:
{
if (lean_obj_tag(v_s_289_) == 0)
{
lean_object* v_val_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_val_290_ = lean_ctor_get(v_s_289_, 0);
v___x_291_ = 1;
v___x_292_ = lean_box(v___x_291_);
lean_inc(v_val_290_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_val_290_);
return v___x_293_;
}
else
{
lean_object* v_val_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_val_294_ = lean_ctor_get(v_s_289_, 0);
v___x_295_ = 0;
v___x_296_ = lean_box(v___x_295_);
lean_inc(v_val_294_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_val_294_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Pair_equivSum___lam__1___boxed(lean_object* v_s_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = lp_CORALean_CORALean_Pair_equivSum___lam__1(v_s_298_);
lean_dec_ref(v_s_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Pair_equivSum(lean_object* v_00_u03b2_305_, lean_object* v_00_u03b3_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = ((lean_object*)(lp_CORALean_CORALean_Pair_equivSum___closed__2));
return v___x_307_;
}
}
static lean_object* _init_lp_CORALean_CORALean_Partition_split___closed__0(void){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lp_CORALean_CORALean_Pair_equivSum(lean_box(0), lean_box(0));
return v___x_308_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_split(lean_object* v_q_309_, lean_object* v_r_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_obj_once(&lp_CORALean_CORALean_Partition_split___closed__0, &lp_CORALean_CORALean_Partition_split___closed__0_once, _init_lp_CORALean_CORALean_Partition_split___closed__0);
v___x_312_ = lp_mathlib_finSumFinEquiv(v_q_309_, v_r_310_);
v___x_313_ = lp_mathlib_Equiv_trans___redArg(v___x_311_, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_reindex___redArg(lean_object* v_P_314_, lean_object* v_e_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lp_mathlib_Equiv_symm___redArg(v_e_315_);
v___x_317_ = lp_mathlib_Equiv_trans___redArg(v_P_314_, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_reindex(lean_object* v_00_u03b1_318_, lean_object* v_00_u03b1_x27_319_, lean_object* v_00_u03b2_u2097_320_, lean_object* v_00_u03b2_u1d63_321_, lean_object* v_P_322_, lean_object* v_e_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lp_CORALean_CORALean_Partition_reindex___redArg(v_P_322_, v_e_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_on___redArg(lean_object* v_P_325_, lean_object* v_k_326_, lean_object* v_l_327_){
_start:
{
lean_object* v_toFun_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
v_toFun_328_ = lean_ctor_get(v_P_325_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_P_325_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v_P_325_, 1);
lean_dec(v_unused_337_);
v___x_330_ = v_P_325_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_toFun_328_);
lean_dec(v_P_325_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v_l_327_);
lean_ctor_set(v___x_330_, 0, v_k_326_);
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_l_327_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_apply_1(v_toFun_328_, v___x_333_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_on(lean_object* v_00_u03b1_338_, lean_object* v_00_u03ba_339_, lean_object* v_00_u03b2_340_, lean_object* v_P_341_, lean_object* v_k_342_, lean_object* v_l_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lp_CORALean_CORALean_Partition_on___redArg(v_P_341_, v_k_342_, v_l_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_left___redArg(lean_object* v_P_345_, lean_object* v_l_346_){
_start:
{
uint8_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = 1;
v___x_348_ = lean_box(v___x_347_);
v___x_349_ = lp_CORALean_CORALean_Partition_on___redArg(v_P_345_, v___x_348_, v_l_346_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_left(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_u2097_351_, lean_object* v_00_u03b2_u1d63_352_, lean_object* v_P_353_, lean_object* v_l_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lp_CORALean_CORALean_Partition_left___redArg(v_P_353_, v_l_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_right___redArg(lean_object* v_P_356_, lean_object* v_l_357_){
_start:
{
uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = 0;
v___x_359_ = lean_box(v___x_358_);
v___x_360_ = lp_CORALean_CORALean_Partition_on___redArg(v_P_356_, v___x_359_, v_l_357_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* lp_CORALean_CORALean_Partition_right(lean_object* v_00_u03b1_361_, lean_object* v_00_u03b2_u2097_362_, lean_object* v_00_u03b2_u1d63_363_, lean_object* v_P_364_, lean_object* v_l_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lp_CORALean_CORALean_Partition_right___redArg(v_P_364_, v_l_365_);
return v___x_366_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CORALean_CORALean_Global_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CORALean_CORALean_Global_Partition(uint8_t builtin) {
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
