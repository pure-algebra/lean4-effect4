// Lean compiler output
// Module: Effect4.Program.Edit
// Imports: public import Init public meta import Init public import Effect4.Program.Typing.Splice public import Effect4.Program.Typing.PartsTable
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
lean_object* lp_effect4_List_repr_x27___at___00Effect4_Machine_instReprCapture_repr_spec__0___redArg(lean_object*);
lean_object* lp_effect4_Effect4_Program_Sketch_fillAt(lean_object*, lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_Sketch_annotate(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_Sketch_sigAt(lean_object*, lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_Annotate_check___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_effect4_Effect4_Program_instDecidableEqEffTy_decEq(lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_Table_splice(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lp_effect4_Effect4_Program_Sketch_omitAt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_Row_hole(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_effect4_Effect4_Program_instDecidableEqRow_decEq(lean_object*, lean_object*);
uint8_t lp_effect4_Effect4_Program_Ty_closed(lean_object*);
lean_object* lp_effect4_Effect4_Program_Ty_normalize(lean_object*);
uint8_t lp_effect4_Effect4_Program_Ty_beq(lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_Row_normalizeTypes(lean_object*);
lean_object* lp_effect4_Effect4_Program_Formation_instantiatedSites(lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_Formation_check(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_effect4_Effect4_Program_Node_at___00__redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_effect4_List_filterMapTR_go___at___00Effect4_Program_refusals_spec__0(lean_object*, lean_object*);
lean_object* lp_effect4_List_eraseDups___at___00Effect4_Program_refusals_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_fill_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_fill_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_omitAt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_omitAt_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_unchanged_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_unchanged_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_spliced_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_spliced_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_rechecked_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_rechecked_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq___closed__0 = (const lean_object*)&lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq___closed__0_value;
LEAN_EXPORT uint8_t lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_effect4_Effect4_Program_Edit_instDecidableEqDelta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_instDecidableEqDelta___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Std_Format_joinSep___at___00List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__0 = (const lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__1 = (const lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__1_value;
static const lean_string_object lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__2 = (const lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__2_value;
static const lean_string_object lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__3 = (const lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__4 = (const lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__5 = (const lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__5_value;
static const lean_string_object lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__6 = (const lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__7;
static lean_once_cell_t lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__8;
static const lean_ctor_object lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__9 = (const lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__10 = (const lean_object*)&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Effect4.Program.Edit.Delta.unchanged"};
static const lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__0 = (const lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__0_value;
static const lean_ctor_object lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__0_value)}};
static const lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__1 = (const lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__1_value;
static const lean_string_object lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Effect4.Program.Edit.Delta.rechecked"};
static const lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__2 = (const lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__2_value;
static const lean_ctor_object lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__2_value)}};
static const lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__3 = (const lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__3_value;
static lean_once_cell_t lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__4;
static lean_once_cell_t lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__5;
static const lean_string_object lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Effect4.Program.Edit.Delta.spliced"};
static const lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__6 = (const lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__6_value;
static const lean_ctor_object lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__6_value)}};
static const lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__7 = (const lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__7_value;
static const lean_ctor_object lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__8 = (const lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__8_value;
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_effect4_Effect4_Program_Edit_instReprDelta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_effect4_Effect4_Program_Edit_instReprDelta_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta___closed__0 = (const lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta___closed__0_value;
LEAN_EXPORT const lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta = (const lean_object*)&lp_effect4_Effect4_Program_Edit_instReprDelta___closed__0_value;
LEAN_EXPORT lean_object* lp_effect4_List_find_x3f___at___00Effect4_Program_Table_typedAt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Table_typedAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_EditSession_open(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_List_mapTR_loop___at___00Effect4_Program_EditSession_feed_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_EditSession_feed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_path(lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_path___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_EditSession_feedStep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_List_foldl___at___00Effect4_Program_EditSession_run_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_EditSession_run(lean_object*, lean_object*);
static const lean_array_object lp_effect4_Effect4_Program_EditSession_view___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_effect4_Effect4_Program_EditSession_view___closed__0 = (const lean_object*)&lp_effect4_Effect4_Program_EditSession_view___closed__0_value;
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_EditSession_view(lean_object*);
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_effect4_Effect4_Program_Edit_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
lean_object* v_path_8_; lean_object* v_program_9_; lean_object* v___x_10_; 
v_path_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_path_8_);
v_program_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_program_9_);
lean_dec_ref(v_t_6_);
v___x_10_ = lean_apply_2(v_k_7_, v_path_8_, v_program_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_effect4_Effect4_Program_Edit_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_effect4_Effect4_Program_Edit_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_fill_elim___redArg(lean_object* v_t_23_, lean_object* v_fill_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_effect4_Effect4_Program_Edit_ctorElim___redArg(v_t_23_, v_fill_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_fill_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_fill_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_effect4_Effect4_Program_Edit_ctorElim___redArg(v_t_27_, v_fill_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_omitAt_elim___redArg(lean_object* v_t_31_, lean_object* v_omitAt_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_effect4_Effect4_Program_Edit_ctorElim___redArg(v_t_31_, v_omitAt_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_omitAt_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_omitAt_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_effect4_Effect4_Program_Edit_ctorElim___redArg(v_t_35_, v_omitAt_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_ctorIdx(lean_object* v_x_39_){
_start:
{
switch(lean_obj_tag(v_x_39_))
{
case 0:
{
lean_object* v___x_40_; 
v___x_40_ = lean_unsigned_to_nat(0u);
return v___x_40_;
}
case 1:
{
lean_object* v___x_41_; 
v___x_41_ = lean_unsigned_to_nat(1u);
return v___x_41_;
}
default: 
{
lean_object* v___x_42_; 
v___x_42_ = lean_unsigned_to_nat(2u);
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_ctorIdx___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_effect4_Effect4_Program_Edit_Delta_ctorIdx(v_x_43_);
lean_dec(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_ctorElim___redArg(lean_object* v_t_45_, lean_object* v_k_46_){
_start:
{
if (lean_obj_tag(v_t_45_) == 1)
{
lean_object* v_shown_47_; lean_object* v___x_48_; 
v_shown_47_ = lean_ctor_get(v_t_45_, 0);
lean_inc(v_shown_47_);
lean_dec_ref_known(v_t_45_, 1);
v___x_48_ = lean_apply_1(v_k_46_, v_shown_47_);
return v___x_48_;
}
else
{
lean_dec(v_t_45_);
return v_k_46_;
}
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_ctorElim(lean_object* v_motive_49_, lean_object* v_ctorIdx_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_k_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_effect4_Effect4_Program_Edit_Delta_ctorElim___redArg(v_t_51_, v_k_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_ctorElim___boxed(lean_object* v_motive_55_, lean_object* v_ctorIdx_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_k_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_effect4_Effect4_Program_Edit_Delta_ctorElim(v_motive_55_, v_ctorIdx_56_, v_t_57_, v_h_58_, v_k_59_);
lean_dec(v_ctorIdx_56_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_unchanged_elim___redArg(lean_object* v_t_61_, lean_object* v_unchanged_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_effect4_Effect4_Program_Edit_Delta_ctorElim___redArg(v_t_61_, v_unchanged_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_unchanged_elim(lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_unchanged_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lp_effect4_Effect4_Program_Edit_Delta_ctorElim___redArg(v_t_65_, v_unchanged_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_spliced_elim___redArg(lean_object* v_t_69_, lean_object* v_spliced_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_effect4_Effect4_Program_Edit_Delta_ctorElim___redArg(v_t_69_, v_spliced_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_spliced_elim(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_spliced_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lp_effect4_Effect4_Program_Edit_Delta_ctorElim___redArg(v_t_73_, v_spliced_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_rechecked_elim___redArg(lean_object* v_t_77_, lean_object* v_rechecked_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lp_effect4_Effect4_Program_Edit_Delta_ctorElim___redArg(v_t_77_, v_rechecked_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_Delta_rechecked_elim(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_rechecked_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lp_effect4_Effect4_Program_Edit_Delta_ctorElim___redArg(v_t_81_, v_rechecked_83_);
return v___x_84_;
}
}
LEAN_EXPORT uint8_t lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq___lam__0(lean_object* v_a_85_, lean_object* v_b_86_){
_start:
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_88_ = l_instDecidableEqList___redArg(v___x_87_, v_a_85_, v_b_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq___lam__0___boxed(lean_object* v_a_89_, lean_object* v_b_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq___lam__0(v_a_89_, v_b_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT uint8_t lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq(lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
switch(lean_obj_tag(v_x_94_))
{
case 0:
{
if (lean_obj_tag(v_x_95_) == 0)
{
uint8_t v___x_96_; 
v___x_96_ = 1;
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
lean_dec(v_x_95_);
v___x_97_ = 0;
return v___x_97_;
}
}
case 1:
{
lean_object* v_shown_98_; uint8_t v___x_99_; 
v_shown_98_ = lean_ctor_get(v_x_94_, 0);
lean_inc(v_shown_98_);
lean_dec_ref_known(v_x_94_, 1);
v___x_99_ = 0;
if (lean_obj_tag(v_x_95_) == 1)
{
lean_object* v_shown_100_; lean_object* v___f_101_; uint8_t v___x_102_; 
v_shown_100_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_shown_100_);
lean_dec_ref_known(v_x_95_, 1);
v___f_101_ = ((lean_object*)(lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq___closed__0));
v___x_102_ = l_instDecidableEqList___redArg(v___f_101_, v_shown_98_, v_shown_100_);
if (v___x_102_ == 0)
{
return v___x_99_;
}
else
{
return v___x_102_;
}
}
else
{
lean_dec(v_shown_98_);
lean_dec(v_x_95_);
return v___x_99_;
}
}
default: 
{
if (lean_obj_tag(v_x_95_) == 2)
{
uint8_t v___x_103_; 
v___x_103_ = 1;
return v___x_103_;
}
else
{
uint8_t v___x_104_; 
lean_dec(v_x_95_);
v___x_104_ = 0;
return v___x_104_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq___boxed(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq(v_x_105_, v_x_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT uint8_t lp_effect4_Effect4_Program_Edit_instDecidableEqDelta(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = lp_effect4_Effect4_Program_Edit_instDecidableEqDelta_decEq(v_x_109_, v_x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_instDecidableEqDelta___boxed(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = lp_effect4_Effect4_Program_Edit_instDecidableEqDelta(v_x_112_, v_x_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* lp_effect4_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_116_, lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
if (lean_obj_tag(v_x_118_) == 0)
{
lean_dec(v_x_116_);
return v_x_117_;
}
else
{
lean_object* v_head_119_; lean_object* v_tail_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_130_; 
v_head_119_ = lean_ctor_get(v_x_118_, 0);
v_tail_120_ = lean_ctor_get(v_x_118_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_x_118_);
if (v_isSharedCheck_130_ == 0)
{
v___x_122_ = v_x_118_;
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_tail_120_);
lean_inc(v_head_119_);
lean_dec(v_x_118_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
lean_inc(v_x_116_);
if (v_isShared_123_ == 0)
{
lean_ctor_set_tag(v___x_122_, 5);
lean_ctor_set(v___x_122_, 1, v_x_116_);
lean_ctor_set(v___x_122_, 0, v_x_117_);
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_x_117_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_x_116_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lp_effect4_List_repr_x27___at___00Effect4_Machine_instReprCapture_repr_spec__0___redArg(v_head_119_);
v___x_127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v_x_117_ = v___x_127_;
v_x_118_ = v_tail_120_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_effect4_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0_spec__0_spec__1(lean_object* v_x_131_, lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_dec(v_x_131_);
return v_x_132_;
}
else
{
lean_object* v_head_134_; lean_object* v_tail_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_145_; 
v_head_134_ = lean_ctor_get(v_x_133_, 0);
v_tail_135_ = lean_ctor_get(v_x_133_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_145_ == 0)
{
v___x_137_ = v_x_133_;
v_isShared_138_ = v_isSharedCheck_145_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_tail_135_);
lean_inc(v_head_134_);
lean_dec(v_x_133_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_145_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
lean_inc(v_x_131_);
if (v_isShared_138_ == 0)
{
lean_ctor_set_tag(v___x_137_, 5);
lean_ctor_set(v___x_137_, 1, v_x_131_);
lean_ctor_set(v___x_137_, 0, v_x_132_);
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_x_132_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_x_131_);
v___x_140_ = v_reuseFailAlloc_144_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = lp_effect4_List_repr_x27___at___00Effect4_Machine_instReprCapture_repr_spec__0___redArg(v_head_134_);
v___x_142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lp_effect4_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0_spec__0_spec__1_spec__2(v_x_131_, v___x_142_, v_tail_135_);
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_effect4_Std_Format_joinSep___at___00List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0_spec__0(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v___x_148_; 
lean_dec(v_x_147_);
v___x_148_ = lean_box(0);
return v___x_148_;
}
else
{
lean_object* v_tail_149_; 
v_tail_149_ = lean_ctor_get(v_x_146_, 1);
if (lean_obj_tag(v_tail_149_) == 0)
{
lean_object* v_head_150_; lean_object* v___x_151_; 
lean_dec(v_x_147_);
v_head_150_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_head_150_);
lean_dec_ref_known(v_x_146_, 2);
v___x_151_ = lp_effect4_List_repr_x27___at___00Effect4_Machine_instReprCapture_repr_spec__0___redArg(v_head_150_);
return v___x_151_;
}
else
{
lean_object* v_head_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
lean_inc(v_tail_149_);
v_head_152_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_head_152_);
lean_dec_ref_known(v_x_146_, 2);
v___x_153_ = lp_effect4_List_repr_x27___at___00Effect4_Machine_instReprCapture_repr_spec__0___redArg(v_head_152_);
v___x_154_ = lp_effect4_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0_spec__0_spec__1(v_x_147_, v___x_153_, v_tail_149_);
return v___x_154_;
}
}
}
}
static lean_object* _init_lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__2));
v___x_167_ = lean_string_length(v___x_166_);
return v___x_167_;
}
}
static lean_object* _init_lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_obj_once(&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__7, &lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__7_once, _init_lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__7);
v___x_169_ = lean_nat_to_int(v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg(lean_object* v_a_174_){
_start:
{
if (lean_obj_tag(v_a_174_) == 0)
{
lean_object* v___x_175_; 
v___x_175_ = ((lean_object*)(lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__1));
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; 
v___x_176_ = ((lean_object*)(lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__5));
v___x_177_ = lp_effect4_Std_Format_joinSep___at___00List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0_spec__0(v_a_174_, v___x_176_);
v___x_178_ = lean_obj_once(&lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__8, &lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__8_once, _init_lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__8);
v___x_179_ = ((lean_object*)(lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__9));
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_177_);
v___x_181_ = ((lean_object*)(lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg___closed__10));
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_178_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = 0;
v___x_185_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set_uint8(v___x_185_, sizeof(void*)*1, v___x_184_);
return v___x_185_;
}
}
}
static lean_object* _init_lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__4(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(2u);
v___x_193_ = lean_nat_to_int(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__5(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_nat_to_int(v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr(lean_object* v_x_202_, lean_object* v_prec_203_){
_start:
{
lean_object* v___y_205_; lean_object* v___y_212_; 
switch(lean_obj_tag(v_x_202_))
{
case 0:
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(1024u);
v___x_219_ = lean_nat_dec_le(v___x_218_, v_prec_203_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_obj_once(&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__4, &lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__4_once, _init_lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__4);
v___y_205_ = v___x_220_;
goto v___jp_204_;
}
else
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__5, &lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__5_once, _init_lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__5);
v___y_205_ = v___x_221_;
goto v___jp_204_;
}
}
case 1:
{
lean_object* v_shown_222_; lean_object* v___y_224_; lean_object* v___x_232_; uint8_t v___x_233_; 
v_shown_222_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_shown_222_);
lean_dec_ref_known(v_x_202_, 1);
v___x_232_ = lean_unsigned_to_nat(1024u);
v___x_233_ = lean_nat_dec_le(v___x_232_, v_prec_203_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__4, &lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__4_once, _init_lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__4);
v___y_224_ = v___x_234_;
goto v___jp_223_;
}
else
{
lean_object* v___x_235_; 
v___x_235_ = lean_obj_once(&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__5, &lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__5_once, _init_lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__5);
v___y_224_ = v___x_235_;
goto v___jp_223_;
}
v___jp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_225_ = ((lean_object*)(lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__8));
v___x_226_ = lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg(v_shown_222_);
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
lean_inc(v___y_224_);
v___x_228_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_228_, 0, v___y_224_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = 0;
v___x_230_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*1, v___x_229_);
v___x_231_ = l_Repr_addAppParen(v___x_230_, v_prec_203_);
return v___x_231_;
}
}
default: 
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(1024u);
v___x_237_ = lean_nat_dec_le(v___x_236_, v_prec_203_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__4, &lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__4_once, _init_lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__4);
v___y_212_ = v___x_238_;
goto v___jp_211_;
}
else
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__5, &lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__5_once, _init_lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__5);
v___y_212_ = v___x_239_;
goto v___jp_211_;
}
}
}
v___jp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_206_ = ((lean_object*)(lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__1));
lean_inc(v___y_205_);
v___x_207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_207_, 0, v___y_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = 0;
v___x_209_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*1, v___x_208_);
v___x_210_ = l_Repr_addAppParen(v___x_209_, v_prec_203_);
return v___x_210_;
}
v___jp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_213_ = ((lean_object*)(lp_effect4_Effect4_Program_Edit_instReprDelta_repr___closed__3));
lean_inc(v___y_212_);
v___x_214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_214_, 0, v___y_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = 0;
v___x_216_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*1, v___x_215_);
v___x_217_ = l_Repr_addAppParen(v___x_216_, v_prec_203_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_instReprDelta_repr___boxed(lean_object* v_x_240_, lean_object* v_prec_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = lp_effect4_Effect4_Program_Edit_instReprDelta_repr(v_x_240_, v_prec_241_);
lean_dec(v_prec_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0(lean_object* v_a_243_, lean_object* v_n_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___redArg(v_a_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0___boxed(lean_object* v_a_246_, lean_object* v_n_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = lp_effect4_List_repr___at___00Effect4_Program_Edit_instReprDelta_repr_spec__0(v_a_246_, v_n_247_);
lean_dec(v_n_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* lp_effect4_List_find_x3f___at___00Effect4_Program_Table_typedAt_spec__0(lean_object* v_a_251_, lean_object* v_x_252_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_object* v___x_253_; 
lean_dec(v_a_251_);
v___x_253_ = lean_box(0);
return v___x_253_;
}
else
{
lean_object* v_head_254_; lean_object* v_tail_255_; lean_object* v_path_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_head_254_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_head_254_);
v_tail_255_ = lean_ctor_get(v_x_252_, 1);
lean_inc(v_tail_255_);
lean_dec_ref_known(v_x_252_, 2);
v_path_256_ = lean_ctor_get(v_head_254_, 0);
v___x_257_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc(v_a_251_);
lean_inc(v_path_256_);
v___x_258_ = l_instDecidableEqList___redArg(v___x_257_, v_path_256_, v_a_251_);
if (v___x_258_ == 0)
{
lean_dec(v_head_254_);
v_x_252_ = v_tail_255_;
goto _start;
}
else
{
lean_object* v___x_260_; 
lean_dec(v_tail_255_);
lean_dec(v_a_251_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v_head_254_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Table_typedAt(lean_object* v_t_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lp_effect4_List_find_x3f___at___00Effect4_Program_Table_typedAt_spec__0(v_a_262_, v_t_261_);
if (lean_obj_tag(v___x_263_) == 1)
{
lean_object* v_val_264_; lean_object* v_env_265_; 
v_val_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_val_264_);
lean_dec_ref_known(v___x_263_, 1);
v_env_265_ = lean_ctor_get(v_val_264_, 1);
if (lean_obj_tag(v_env_265_) == 1)
{
lean_object* v_val_266_; 
v_val_266_ = lean_ctor_get(v_env_265_, 0);
lean_inc(v_val_266_);
if (lean_obj_tag(v_val_266_) == 0)
{
lean_object* v_result_267_; 
v_result_267_ = lean_ctor_get(v_val_264_, 2);
lean_inc(v_result_267_);
lean_dec(v_val_264_);
if (lean_obj_tag(v_result_267_) == 1)
{
lean_object* v_val_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_279_; 
v_val_268_ = lean_ctor_get(v_result_267_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v_result_267_);
if (v_isSharedCheck_279_ == 0)
{
v___x_270_ = v_result_267_;
v_isShared_271_ = v_isSharedCheck_279_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_val_268_);
lean_dec(v_result_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_279_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
if (lean_obj_tag(v_val_268_) == 1)
{
lean_object* v_env_272_; lean_object* v_a_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v_env_272_ = lean_ctor_get(v_val_266_, 0);
lean_inc(v_env_272_);
lean_dec_ref_known(v_val_266_, 1);
v_a_273_ = lean_ctor_get(v_val_268_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v_val_268_, 1);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_env_272_);
lean_ctor_set(v___x_274_, 1, v_a_273_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_274_);
v___x_276_ = v___x_270_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
else
{
lean_object* v___x_278_; 
lean_del_object(v___x_270_);
lean_dec(v_val_268_);
lean_dec_ref_known(v_val_266_, 1);
v___x_278_ = lean_box(0);
return v___x_278_;
}
}
}
else
{
lean_object* v___x_280_; 
lean_dec(v_result_267_);
lean_dec_ref_known(v_val_266_, 1);
v___x_280_ = lean_box(0);
return v___x_280_;
}
}
else
{
lean_object* v___x_281_; 
lean_dec(v_val_266_);
lean_dec(v_val_264_);
v___x_281_ = lean_box(0);
return v___x_281_;
}
}
else
{
lean_object* v___x_282_; 
lean_dec(v_val_264_);
v___x_282_ = lean_box(0);
return v___x_282_;
}
}
else
{
lean_object* v___x_283_; 
lean_dec(v___x_263_);
v___x_283_ = lean_box(0);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_EditSession_open(lean_object* v_app_284_, lean_object* v_s_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_inc_ref(v_app_284_);
lean_inc_ref(v_s_285_);
v___x_286_ = lp_effect4_Effect4_Program_Sketch_annotate(v_s_285_, v_app_284_);
v___x_287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_287_, 0, v_app_284_);
lean_ctor_set(v___x_287_, 1, v_s_285_);
lean_ctor_set(v___x_287_, 2, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* lp_effect4_List_mapTR_loop___at___00Effect4_Program_EditSession_feed_spec__0(lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
if (lean_obj_tag(v_a_288_) == 0)
{
lean_object* v___x_290_; 
v___x_290_ = l_List_reverse___redArg(v_a_289_);
return v___x_290_;
}
else
{
lean_object* v_head_291_; lean_object* v_tail_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_301_; 
v_head_291_ = lean_ctor_get(v_a_288_, 0);
v_tail_292_ = lean_ctor_get(v_a_288_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v_a_288_);
if (v_isSharedCheck_301_ == 0)
{
v___x_294_ = v_a_288_;
v_isShared_295_ = v_isSharedCheck_301_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_tail_292_);
lean_inc(v_head_291_);
lean_dec(v_a_288_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_301_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v_path_296_; lean_object* v___x_298_; 
v_path_296_ = lean_ctor_get(v_head_291_, 0);
lean_inc(v_path_296_);
lean_dec(v_head_291_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v_a_289_);
lean_ctor_set(v___x_294_, 0, v_path_296_);
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_path_296_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_a_289_);
v___x_298_ = v_reuseFailAlloc_300_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
v_a_288_ = v_tail_292_;
v_a_289_ = v___x_298_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_EditSession_feed(lean_object* v_l_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_object* v_path_304_; lean_object* v_program_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_364_; 
v_path_304_ = lean_ctor_get(v_x_303_, 0);
v_program_305_ = lean_ctor_get(v_x_303_, 1);
v_isSharedCheck_364_ = !lean_is_exclusive(v_x_303_);
if (v_isSharedCheck_364_ == 0)
{
v___x_307_ = v_x_303_;
v_isShared_308_ = v_isSharedCheck_364_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_program_305_);
lean_inc(v_path_304_);
lean_dec(v_x_303_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_364_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_app_309_; lean_object* v_sketch_310_; lean_object* v_table_311_; lean_object* v___x_312_; 
v_app_309_ = lean_ctor_get(v_l_302_, 0);
v_sketch_310_ = lean_ctor_get(v_l_302_, 1);
v_table_311_ = lean_ctor_get(v_l_302_, 2);
lean_inc_ref(v_program_305_);
lean_inc_ref(v_sketch_310_);
v___x_312_ = lp_effect4_Effect4_Program_Sketch_fillAt(v_sketch_310_, v_path_304_, v_program_305_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v___x_313_; lean_object* v___x_315_; 
lean_dec_ref(v_program_305_);
lean_dec(v_path_304_);
v___x_313_ = lean_box(0);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_313_);
lean_ctor_set(v___x_307_, 0, v_l_302_);
v___x_315_ = v___x_307_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_l_302_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_360_; 
lean_inc(v_table_311_);
lean_inc_ref(v_sketch_310_);
lean_inc_ref(v_app_309_);
v_isSharedCheck_360_ = !lean_is_exclusive(v_l_302_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; lean_object* v_unused_362_; lean_object* v_unused_363_; 
v_unused_361_ = lean_ctor_get(v_l_302_, 2);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_l_302_, 1);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_l_302_, 0);
lean_dec(v_unused_363_);
v___x_318_ = v_l_302_;
v_isShared_319_ = v_isSharedCheck_360_;
goto v_resetjp_317_;
}
else
{
lean_dec(v_l_302_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_360_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v_val_320_; 
v_val_320_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v___x_312_, 1);
if (lean_obj_tag(v_path_304_) == 1)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_box(0);
lean_inc(v_table_311_);
v___x_331_ = lp_effect4_Effect4_Program_Table_typedAt(v_table_311_, v___x_330_);
if (lean_obj_tag(v___x_331_) == 1)
{
lean_object* v___x_332_; 
lean_dec_ref_known(v___x_331_, 1);
lean_inc_ref(v_path_304_);
lean_inc(v_table_311_);
v___x_332_ = lp_effect4_Effect4_Program_Table_typedAt(v_table_311_, v_path_304_);
if (lean_obj_tag(v___x_332_) == 1)
{
lean_object* v_val_333_; lean_object* v_fst_334_; lean_object* v_snd_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v_snd_338_; 
v_val_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_val_333_);
lean_dec_ref_known(v___x_332_, 1);
v_fst_334_ = lean_ctor_get(v_val_333_, 0);
lean_inc(v_fst_334_);
v_snd_335_ = lean_ctor_get(v_val_333_, 1);
lean_inc(v_snd_335_);
lean_dec(v_val_333_);
lean_inc_ref_n(v_path_304_, 2);
lean_inc_ref(v_app_309_);
v___x_336_ = lp_effect4_Effect4_Program_Sketch_sigAt(v_sketch_310_, v_app_309_, v_path_304_);
v___x_337_ = lp_effect4_Effect4_Program_Annotate_check___redArg(v___x_336_, v_fst_334_, v_path_304_, v_program_305_);
v_snd_338_ = lean_ctor_get(v___x_337_, 1);
lean_inc(v_snd_338_);
if (lean_obj_tag(v_snd_338_) == 0)
{
lean_dec_ref_known(v_snd_338_, 1);
lean_dec_ref(v___x_337_);
lean_dec(v_snd_335_);
lean_dec_ref_known(v_path_304_, 2);
lean_dec(v_table_311_);
goto v___jp_321_;
}
else
{
lean_object* v_fst_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_358_; 
v_fst_339_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v___x_337_, 1);
lean_dec(v_unused_359_);
v___x_341_ = v___x_337_;
v_isShared_342_ = v_isSharedCheck_358_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_fst_339_);
lean_dec(v___x_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_358_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_357_; 
v_a_343_ = lean_ctor_get(v_snd_338_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v_snd_338_);
if (v_isSharedCheck_357_ == 0)
{
v___x_345_ = v_snd_338_;
v_isShared_346_ = v_isSharedCheck_357_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v_snd_338_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_357_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
uint8_t v___x_347_; 
v___x_347_ = lp_effect4_Effect4_Program_instDecidableEqEffTy_decEq(v_a_343_, v_snd_335_);
if (v___x_347_ == 0)
{
lean_del_object(v___x_345_);
lean_del_object(v___x_341_);
lean_dec(v_fst_339_);
lean_dec_ref_known(v_path_304_, 2);
lean_dec(v_table_311_);
goto v___jp_321_;
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
lean_del_object(v___x_318_);
lean_del_object(v___x_307_);
lean_inc(v_fst_339_);
v___x_348_ = lp_effect4_Effect4_Program_Table_splice(v_table_311_, v_path_304_, v_fst_339_);
lean_dec_ref_known(v_path_304_, 2);
v___x_349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_349_, 0, v_app_309_);
lean_ctor_set(v___x_349_, 1, v_val_320_);
lean_ctor_set(v___x_349_, 2, v___x_348_);
v___x_350_ = lp_effect4_List_mapTR_loop___at___00Effect4_Program_EditSession_feed_spec__0(v_fst_339_, v___x_330_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_350_);
v___x_352_ = v___x_345_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_354_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v___x_352_);
lean_ctor_set(v___x_341_, 0, v___x_349_);
v___x_354_ = v___x_341_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_332_);
lean_dec_ref_known(v_path_304_, 2);
lean_dec(v_table_311_);
lean_dec_ref(v_sketch_310_);
lean_dec_ref(v_program_305_);
goto v___jp_321_;
}
}
else
{
lean_dec(v___x_331_);
lean_dec_ref_known(v_path_304_, 2);
lean_dec(v_table_311_);
lean_dec_ref(v_sketch_310_);
lean_dec_ref(v_program_305_);
goto v___jp_321_;
}
}
else
{
lean_dec(v_table_311_);
lean_dec_ref(v_sketch_310_);
lean_dec_ref(v_program_305_);
lean_dec(v_path_304_);
goto v___jp_321_;
}
v___jp_321_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
lean_inc_ref(v_app_309_);
lean_inc(v_val_320_);
v___x_322_ = lp_effect4_Effect4_Program_Sketch_annotate(v_val_320_, v_app_309_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 2, v___x_322_);
lean_ctor_set(v___x_318_, 1, v_val_320_);
v___x_324_ = v___x_318_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_app_309_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_val_320_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v___x_322_);
v___x_324_ = v_reuseFailAlloc_329_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_box(2);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_325_);
lean_ctor_set(v___x_307_, 0, v___x_324_);
v___x_327_ = v___x_307_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
}
else
{
lean_object* v_path_365_; lean_object* v_row_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_452_; 
v_path_365_ = lean_ctor_get(v_x_303_, 0);
v_row_366_ = lean_ctor_get(v_x_303_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v_x_303_);
if (v_isSharedCheck_452_ == 0)
{
v___x_368_ = v_x_303_;
v_isShared_369_ = v_isSharedCheck_452_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_row_366_);
lean_inc(v_path_365_);
lean_dec(v_x_303_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_452_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v_app_370_; lean_object* v_sketch_371_; lean_object* v_table_372_; lean_object* v___x_373_; 
v_app_370_ = lean_ctor_get(v_l_302_, 0);
v_sketch_371_ = lean_ctor_get(v_l_302_, 1);
v_table_372_ = lean_ctor_get(v_l_302_, 2);
lean_inc_ref(v_row_366_);
lean_inc_ref(v_app_370_);
lean_inc_ref(v_sketch_371_);
v___x_373_ = lp_effect4_Effect4_Program_Sketch_omitAt(v_sketch_371_, v_app_370_, v_path_365_, v_row_366_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v___x_374_; lean_object* v___x_376_; 
lean_dec_ref(v_row_366_);
lean_dec(v_path_365_);
v___x_374_ = lean_box(0);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 0);
lean_ctor_set(v___x_368_, 1, v___x_374_);
lean_ctor_set(v___x_368_, 0, v_l_302_);
v___x_376_ = v___x_368_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_l_302_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_448_; 
lean_inc(v_table_372_);
lean_inc_ref(v_app_370_);
v_isSharedCheck_448_ = !lean_is_exclusive(v_l_302_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; lean_object* v_unused_450_; lean_object* v_unused_451_; 
v_unused_449_ = lean_ctor_get(v_l_302_, 2);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_l_302_, 1);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_l_302_, 0);
lean_dec(v_unused_451_);
v___x_379_ = v_l_302_;
v_isShared_380_ = v_isSharedCheck_448_;
goto v_resetjp_378_;
}
else
{
lean_dec(v_l_302_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_448_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_val_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_447_; 
v_val_381_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_447_ == 0)
{
v___x_383_ = v___x_373_;
v_isShared_384_ = v_isSharedCheck_447_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_val_381_);
lean_dec(v___x_373_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_447_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
if (lean_obj_tag(v_path_365_) == 1)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_box(0);
lean_inc(v_table_372_);
v___x_395_ = lp_effect4_Effect4_Program_Table_typedAt(v_table_372_, v___x_394_);
if (lean_obj_tag(v___x_395_) == 1)
{
lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_445_; 
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_395_, 0);
lean_dec(v_unused_446_);
v___x_397_ = v___x_395_;
v_isShared_398_ = v_isSharedCheck_445_;
goto v_resetjp_396_;
}
else
{
lean_dec(v___x_395_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_445_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; 
lean_inc_ref(v_path_365_);
lean_inc(v_table_372_);
v___x_399_ = lp_effect4_Effect4_Program_Table_typedAt(v_table_372_, v_path_365_);
if (lean_obj_tag(v___x_399_) == 1)
{
lean_object* v_val_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_444_; 
v_val_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_444_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_444_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_val_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_444_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_snd_404_; lean_object* v_fst_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_443_; 
v_snd_404_ = lean_ctor_get(v_val_400_, 1);
v_fst_405_ = lean_ctor_get(v_val_400_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v_val_400_);
if (v_isSharedCheck_443_ == 0)
{
v___x_407_ = v_val_400_;
v_isShared_408_ = v_isSharedCheck_443_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_snd_404_);
lean_inc(v_fst_405_);
lean_dec(v_val_400_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_443_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_name_409_; lean_object* v_answer_410_; lean_object* v_error_411_; lean_object* v_requires_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v_name_409_ = lean_ctor_get(v_row_366_, 0);
v_answer_410_ = lean_ctor_get(v_snd_404_, 0);
v_error_411_ = lean_ctor_get(v_snd_404_, 1);
v_requires_412_ = lean_ctor_get(v_snd_404_, 2);
lean_inc(v_requires_412_);
lean_inc(v_error_411_);
lean_inc(v_answer_410_);
lean_inc_ref(v_name_409_);
v___x_413_ = lp_effect4_Effect4_Program_Row_hole(v_name_409_, v_answer_410_, v_error_411_, v_requires_412_);
lean_inc_ref(v_row_366_);
v___x_414_ = lp_effect4_Effect4_Program_instDecidableEqRow_decEq(v_row_366_, v___x_413_);
if (v___x_414_ == 0)
{
lean_del_object(v___x_407_);
lean_dec(v_fst_405_);
lean_dec(v_snd_404_);
lean_del_object(v___x_402_);
lean_del_object(v___x_397_);
lean_dec_ref_known(v_path_365_, 2);
lean_del_object(v___x_383_);
lean_dec(v_table_372_);
lean_dec_ref(v_row_366_);
goto v___jp_385_;
}
else
{
uint8_t v___x_415_; 
v___x_415_ = lp_effect4_Effect4_Program_Ty_closed(v_answer_410_);
if (v___x_415_ == 0)
{
lean_del_object(v___x_407_);
lean_dec(v_fst_405_);
lean_dec(v_snd_404_);
lean_del_object(v___x_402_);
lean_del_object(v___x_397_);
lean_dec_ref_known(v_path_365_, 2);
lean_del_object(v___x_383_);
lean_dec(v_table_372_);
lean_dec_ref(v_row_366_);
goto v___jp_385_;
}
else
{
uint8_t v___x_416_; 
v___x_416_ = lp_effect4_Effect4_Program_Ty_closed(v_error_411_);
if (v___x_416_ == 0)
{
lean_del_object(v___x_407_);
lean_dec(v_fst_405_);
lean_dec(v_snd_404_);
lean_del_object(v___x_402_);
lean_del_object(v___x_397_);
lean_dec_ref_known(v_path_365_, 2);
lean_del_object(v___x_383_);
lean_dec(v_table_372_);
lean_dec_ref(v_row_366_);
goto v___jp_385_;
}
else
{
lean_object* v___x_417_; uint8_t v___x_418_; 
lean_inc(v_answer_410_);
v___x_417_ = lp_effect4_Effect4_Program_Ty_normalize(v_answer_410_);
v___x_418_ = lp_effect4_Effect4_Program_Ty_beq(v___x_417_, v_answer_410_);
lean_dec(v___x_417_);
if (v___x_418_ == 0)
{
lean_del_object(v___x_407_);
lean_dec(v_fst_405_);
lean_dec(v_snd_404_);
lean_del_object(v___x_402_);
lean_del_object(v___x_397_);
lean_dec_ref_known(v_path_365_, 2);
lean_del_object(v___x_383_);
lean_dec(v_table_372_);
lean_dec_ref(v_row_366_);
goto v___jp_385_;
}
else
{
lean_object* v___x_419_; uint8_t v___x_420_; 
lean_inc(v_error_411_);
v___x_419_ = lp_effect4_Effect4_Program_Ty_normalize(v_error_411_);
v___x_420_ = lp_effect4_Effect4_Program_Ty_beq(v___x_419_, v_error_411_);
lean_dec(v___x_419_);
if (v___x_420_ == 0)
{
lean_del_object(v___x_407_);
lean_dec(v_fst_405_);
lean_dec(v_snd_404_);
lean_del_object(v___x_402_);
lean_del_object(v___x_397_);
lean_dec_ref_known(v_path_365_, 2);
lean_del_object(v___x_383_);
lean_dec(v_table_372_);
lean_dec_ref(v_row_366_);
goto v___jp_385_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = lp_effect4_Effect4_Program_Row_normalizeTypes(v_row_366_);
v___x_422_ = lp_effect4_Effect4_Program_Formation_instantiatedSites(v___x_421_, v___x_394_);
v___x_423_ = lp_effect4_Effect4_Program_Formation_check(v___x_422_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v___x_425_; 
lean_del_object(v___x_379_);
lean_del_object(v___x_368_);
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 0);
lean_ctor_set(v___x_383_, 0, v_fst_405_);
v___x_425_ = v___x_383_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_fst_405_);
v___x_425_ = v_reuseFailAlloc_442_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_427_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_425_);
v___x_427_ = v___x_402_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_441_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_428_, 0, v_snd_404_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_428_);
v___x_430_ = v___x_397_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_440_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v_entry_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
lean_inc_ref(v_path_365_);
v_entry_431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_431_, 0, v_path_365_);
lean_ctor_set(v_entry_431_, 1, v___x_427_);
lean_ctor_set(v_entry_431_, 2, v___x_430_);
v___x_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_432_, 0, v_entry_431_);
lean_ctor_set(v___x_432_, 1, v___x_394_);
v___x_433_ = lp_effect4_Effect4_Program_Table_splice(v_table_372_, v_path_365_, v___x_432_);
v___x_434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_434_, 0, v_app_370_);
lean_ctor_set(v___x_434_, 1, v_val_381_);
lean_ctor_set(v___x_434_, 2, v___x_433_);
v___x_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_435_, 0, v_path_365_);
lean_ctor_set(v___x_435_, 1, v___x_394_);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 1, v___x_436_);
lean_ctor_set(v___x_407_, 0, v___x_434_);
v___x_438_ = v___x_407_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_423_, 1);
lean_del_object(v___x_407_);
lean_dec(v_fst_405_);
lean_dec(v_snd_404_);
lean_del_object(v___x_402_);
lean_del_object(v___x_397_);
lean_dec_ref_known(v_path_365_, 2);
lean_del_object(v___x_383_);
lean_dec(v_table_372_);
goto v___jp_385_;
}
}
}
}
}
}
}
}
}
else
{
lean_dec(v___x_399_);
lean_del_object(v___x_397_);
lean_dec_ref_known(v_path_365_, 2);
lean_del_object(v___x_383_);
lean_dec(v_table_372_);
lean_dec_ref(v_row_366_);
goto v___jp_385_;
}
}
}
else
{
lean_dec(v___x_395_);
lean_dec_ref_known(v_path_365_, 2);
lean_del_object(v___x_383_);
lean_dec(v_table_372_);
lean_dec_ref(v_row_366_);
goto v___jp_385_;
}
}
else
{
lean_del_object(v___x_383_);
lean_dec(v_table_372_);
lean_dec_ref(v_row_366_);
lean_dec(v_path_365_);
goto v___jp_385_;
}
v___jp_385_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
lean_inc_ref(v_app_370_);
lean_inc(v_val_381_);
v___x_386_ = lp_effect4_Effect4_Program_Sketch_annotate(v_val_381_, v_app_370_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 2, v___x_386_);
lean_ctor_set(v___x_379_, 1, v_val_381_);
v___x_388_ = v___x_379_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_app_370_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_val_381_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v___x_386_);
v___x_388_ = v_reuseFailAlloc_393_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = lean_box(2);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 0);
lean_ctor_set(v___x_368_, 1, v___x_389_);
lean_ctor_set(v___x_368_, 0, v___x_388_);
v___x_391_ = v___x_368_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___x_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_path(lean_object* v_x_453_){
_start:
{
lean_object* v_path_454_; 
v_path_454_ = lean_ctor_get(v_x_453_, 0);
lean_inc(v_path_454_);
return v_path_454_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_Edit_path___boxed(lean_object* v_x_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = lp_effect4_Effect4_Program_Edit_path(v_x_455_);
lean_dec_ref(v_x_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_EditSession_feedStep(lean_object* v_l_457_, lean_object* v_e_458_){
_start:
{
lean_object* v___y_460_; lean_object* v_sketch_472_; lean_object* v_program_473_; lean_object* v___x_474_; lean_object* v___y_476_; lean_object* v_path_489_; 
v_sketch_472_ = lean_ctor_get(v_l_457_, 1);
v_program_473_ = lean_ctor_get(v_sketch_472_, 0);
lean_inc_ref(v_program_473_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v_program_473_);
v_path_489_ = lean_ctor_get(v_e_458_, 0);
lean_inc(v_path_489_);
v___y_476_ = v_path_489_;
goto v___jp_475_;
v___jp_459_:
{
lean_object* v___x_461_; lean_object* v_fst_462_; lean_object* v_snd_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_471_; 
lean_inc_ref(v_e_458_);
v___x_461_ = lp_effect4_Effect4_Program_EditSession_feed(v_l_457_, v_e_458_);
v_fst_462_ = lean_ctor_get(v___x_461_, 0);
v_snd_463_ = lean_ctor_get(v___x_461_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_471_ == 0)
{
v___x_465_ = v___x_461_;
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_snd_463_);
lean_inc(v_fst_462_);
lean_dec(v___x_461_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_471_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_467_, 0, v_e_458_);
lean_ctor_set(v___x_467_, 1, v___y_460_);
lean_ctor_set(v___x_467_, 2, v_snd_463_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_fst_462_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
v___jp_475_:
{
lean_object* v___x_477_; 
v___x_477_ = lp_effect4_Effect4_Program_Node_at___00__redArg(v___x_474_, v___y_476_);
lean_dec(v___y_476_);
if (lean_obj_tag(v___x_477_) == 1)
{
lean_object* v_val_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_487_; 
v_val_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_487_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_val_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
if (lean_obj_tag(v_val_478_) == 0)
{
lean_object* v_e_482_; lean_object* v___x_484_; 
v_e_482_ = lean_ctor_get(v_val_478_, 0);
lean_inc_ref(v_e_482_);
lean_dec_ref_known(v_val_478_, 1);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v_e_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_e_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
v___y_460_ = v___x_484_;
goto v___jp_459_;
}
}
else
{
lean_object* v___x_486_; 
lean_del_object(v___x_480_);
lean_dec(v_val_478_);
v___x_486_ = lean_box(0);
v___y_460_ = v___x_486_;
goto v___jp_459_;
}
}
}
else
{
lean_object* v___x_488_; 
lean_dec(v___x_477_);
v___x_488_ = lean_box(0);
v___y_460_ = v___x_488_;
goto v___jp_459_;
}
}
}
}
LEAN_EXPORT lean_object* lp_effect4_List_foldl___at___00Effect4_Program_EditSession_run_spec__0(lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_491_) == 0)
{
return v_x_490_;
}
else
{
lean_object* v_head_492_; lean_object* v_tail_493_; lean_object* v___x_494_; lean_object* v_fst_495_; 
v_head_492_ = lean_ctor_get(v_x_491_, 0);
lean_inc(v_head_492_);
v_tail_493_ = lean_ctor_get(v_x_491_, 1);
lean_inc(v_tail_493_);
lean_dec_ref_known(v_x_491_, 2);
v___x_494_ = lp_effect4_Effect4_Program_EditSession_feed(v_x_490_, v_head_492_);
v_fst_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_fst_495_);
lean_dec_ref(v___x_494_);
v_x_490_ = v_fst_495_;
v_x_491_ = v_tail_493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_EditSession_run(lean_object* v_l_497_, lean_object* v_edits_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lp_effect4_List_foldl___at___00Effect4_Program_EditSession_run_spec__0(v_l_497_, v_edits_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* lp_effect4_Effect4_Program_EditSession_view(lean_object* v_l_502_){
_start:
{
lean_object* v_table_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_528_; 
v_table_503_ = lean_ctor_get(v_l_502_, 2);
v_isSharedCheck_528_ = !lean_is_exclusive(v_l_502_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; lean_object* v_unused_530_; 
v_unused_529_ = lean_ctor_get(v_l_502_, 1);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_l_502_, 0);
lean_dec(v_unused_530_);
v___x_505_ = v_l_502_;
v_isShared_506_ = v_isSharedCheck_528_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_table_503_);
lean_dec(v_l_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_528_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_507_ = ((lean_object*)(lp_effect4_Effect4_Program_EditSession_view___closed__0));
lean_inc_n(v_table_503_, 2);
v___x_508_ = lp_effect4_List_filterMapTR_go___at___00Effect4_Program_refusals_spec__0(v_table_503_, v___x_507_);
v___x_509_ = lp_effect4_List_eraseDups___at___00Effect4_Program_refusals_spec__1(v___x_508_);
v___x_510_ = lean_box(0);
v___x_511_ = lp_effect4_Effect4_Program_Table_typedAt(v_table_503_, v___x_510_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = lean_box(0);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 2, v___x_512_);
lean_ctor_set(v___x_505_, 1, v___x_509_);
lean_ctor_set(v___x_505_, 0, v_table_503_);
v___x_514_ = v___x_505_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_table_503_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
else
{
lean_object* v_val_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_527_; 
v_val_516_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_527_ == 0)
{
v___x_518_ = v___x_511_;
v_isShared_519_ = v_isSharedCheck_527_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_val_516_);
lean_dec(v___x_511_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_527_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v_snd_520_; lean_object* v___x_522_; 
v_snd_520_ = lean_ctor_get(v_val_516_, 1);
lean_inc(v_snd_520_);
lean_dec(v_val_516_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v_snd_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_snd_520_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 2, v___x_522_);
lean_ctor_set(v___x_505_, 1, v___x_509_);
lean_ctor_set(v___x_505_, 0, v_table_503_);
v___x_524_ = v___x_505_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_table_503_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_effect4_Effect4_Program_Typing_Splice(uint8_t builtin);
lean_object* initialize_effect4_Effect4_Program_Typing_PartsTable(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_effect4_Effect4_Program_Edit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_effect4_Effect4_Program_Typing_Splice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_effect4_Effect4_Program_Typing_PartsTable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
