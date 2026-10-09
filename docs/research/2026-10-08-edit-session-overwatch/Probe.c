// Lean compiler output
// Module: docs.research.«2026-10-08-edit-session-overwatch».Probe
// Imports: public import Init public meta import Init public import Effect4.Author public import Effect4.Library public import Effect4.Program.Edit public import Test.Program.EditControls
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
lean_object* lp_effect4_Effect4_Program_Node_replaceAt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_annotate___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_Table_typedAt(lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_Annotate_check___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_effect4_Effect4_Program_instDecidableEqEffTy_decEq(lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_Table_splice(lean_object*, lean_object*, lean_object*);
lean_object* lp_effect4_List_mapTR_loop___at___00Effect4_Program_EditSession_feed_spec__0(lean_object*, lean_object*);
extern lean_object* lp_effect4_Test_Program_EditControls_keep;
extern lean_object* lp_effect4_Test_Program_EditControls_opened;
lean_object* lp_effect4_Effect4_Program_EditSession_feed___redArg(lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_Authoring_nat___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Semaphore_takeIfAvailable(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Semaphore_make(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_Authoring_bindWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Api_Author_program(lean_object*);
lean_object* lp_effect4_Effect4_Program_nativeSignature(lean_object*);
lean_object* lp_effect4_Effect4_Program_EditSession_open___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_EditSession_view___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lp_effect4_Test_Program_SketchControls_sketchAt(lean_object*);
lean_object* lp_effect4_Effect4_Program_SigApp_withHoles(lean_object*, lean_object*);
lean_object* lp_effect4_Effect4_Program_SigApp_signature(lean_object*);
LEAN_EXPORT lean_object* l_EditOverwatch_feedDeferred___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EditOverwatch_feedDeferred(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_EditOverwatch_expanded___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_EditOverwatch_expanded___closed__0 = (const lean_object*)&l_EditOverwatch_expanded___closed__0_value;
static const lean_ctor_object l_EditOverwatch_expanded___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_EditOverwatch_expanded___closed__1 = (const lean_object*)&l_EditOverwatch_expanded___closed__1_value;
static const lean_ctor_object l_EditOverwatch_expanded___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_EditOverwatch_expanded___closed__1_value)}};
static const lean_object* l_EditOverwatch_expanded___closed__2 = (const lean_object*)&l_EditOverwatch_expanded___closed__2_value;
static const lean_ctor_object l_EditOverwatch_expanded___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_EditOverwatch_expanded___closed__2_value)}};
static const lean_object* l_EditOverwatch_expanded___closed__3 = (const lean_object*)&l_EditOverwatch_expanded___closed__3_value;
static const lean_ctor_object l_EditOverwatch_expanded___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 4}, .m_objs = {((lean_object*)&l_EditOverwatch_expanded___closed__3_value)}};
static const lean_object* l_EditOverwatch_expanded___closed__4 = (const lean_object*)&l_EditOverwatch_expanded___closed__4_value;
static const lean_ctor_object l_EditOverwatch_expanded___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_EditOverwatch_expanded___closed__0_value),((lean_object*)&l_EditOverwatch_expanded___closed__4_value)}};
static const lean_object* l_EditOverwatch_expanded___closed__5 = (const lean_object*)&l_EditOverwatch_expanded___closed__5_value;
static lean_once_cell_t l_EditOverwatch_expanded___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_EditOverwatch_expanded___closed__6;
LEAN_EXPORT lean_object* l_EditOverwatch_expanded;
static lean_once_cell_t l_EditOverwatch_shrunk___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_EditOverwatch_shrunk___closed__0;
LEAN_EXPORT lean_object* l_EditOverwatch_shrunk;
static const lean_closure_object l_EditOverwatch_semaphoreClient___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_effect4_Effect4_Program_Authoring_nat___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_EditOverwatch_semaphoreClient___lam__0___closed__0 = (const lean_object*)&l_EditOverwatch_semaphoreClient___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_EditOverwatch_semaphoreClient___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_EditOverwatch_semaphoreClient___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EditOverwatch_semaphoreClient___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_EditOverwatch_semaphoreClient___closed__0 = (const lean_object*)&l_EditOverwatch_semaphoreClient___closed__0_value;
static const lean_closure_object l_EditOverwatch_semaphoreClient___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_effect4_Effect4_Semaphore_make, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_EditOverwatch_semaphoreClient___closed__1 = (const lean_object*)&l_EditOverwatch_semaphoreClient___closed__1_value;
LEAN_EXPORT lean_object* l_EditOverwatch_semaphoreClient(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00EditOverwatch_moduleSplices_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00EditOverwatch_moduleSplices_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_EditOverwatch_moduleSplices___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_EditOverwatch_moduleSplices___closed__0;
LEAN_EXPORT uint8_t l_EditOverwatch_moduleSplices;
static lean_once_cell_t l_EditOverwatch_holeSession___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_EditOverwatch_holeSession___closed__0;
static const lean_ctor_object l_EditOverwatch_holeSession___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_EditOverwatch_holeSession___closed__1 = (const lean_object*)&l_EditOverwatch_holeSession___closed__1_value;
LEAN_EXPORT lean_object* l_EditOverwatch_holeSession;
LEAN_EXPORT lean_object* l_EditOverwatch_feedDeferred___redArg(lean_object* v_l_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_path_6_; lean_object* v_program_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_66_; 
v_path_6_ = lean_ctor_get(v_x_2_, 0);
v_program_7_ = lean_ctor_get(v_x_2_, 1);
v_isSharedCheck_66_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_66_ == 0)
{
v___x_9_ = v_x_2_;
v_isShared_10_ = v_isSharedCheck_66_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_program_7_);
lean_inc(v_path_6_);
lean_dec(v_x_2_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_66_;
goto v_resetjp_8_;
}
v___jp_3_:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_box(0);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v_l_1_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
return v___x_5_;
}
v_resetjp_8_:
{
lean_object* v_sig_11_; lean_object* v_env_12_; lean_object* v_program_13_; lean_object* v_table_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_sig_11_ = lean_ctor_get(v_l_1_, 0);
v_env_12_ = lean_ctor_get(v_l_1_, 1);
v_program_13_ = lean_ctor_get(v_l_1_, 2);
v_table_14_ = lean_ctor_get(v_l_1_, 3);
lean_inc_ref(v_program_13_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v_program_13_);
lean_inc_ref(v_program_7_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v_program_7_);
v___x_17_ = lp_effect4_Effect4_Program_Node_replaceAt___redArg(v___x_15_, v_path_6_, v___x_16_);
if (lean_obj_tag(v___x_17_) == 1)
{
lean_object* v_val_18_; 
v_val_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_val_18_);
lean_dec_ref_known(v___x_17_, 1);
if (lean_obj_tag(v_val_18_) == 0)
{
lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_61_; 
lean_inc(v_table_14_);
lean_inc(v_env_12_);
lean_inc_ref(v_sig_11_);
v_isSharedCheck_61_ = !lean_is_exclusive(v_l_1_);
if (v_isSharedCheck_61_ == 0)
{
lean_object* v_unused_62_; lean_object* v_unused_63_; lean_object* v_unused_64_; lean_object* v_unused_65_; 
v_unused_62_ = lean_ctor_get(v_l_1_, 3);
lean_dec(v_unused_62_);
v_unused_63_ = lean_ctor_get(v_l_1_, 2);
lean_dec(v_unused_63_);
v_unused_64_ = lean_ctor_get(v_l_1_, 1);
lean_dec(v_unused_64_);
v_unused_65_ = lean_ctor_get(v_l_1_, 0);
lean_dec(v_unused_65_);
v___x_20_ = v_l_1_;
v_isShared_21_ = v_isSharedCheck_61_;
goto v_resetjp_19_;
}
else
{
lean_dec(v_l_1_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_61_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v_e_22_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_e_22_ = lean_ctor_get(v_val_18_, 0);
lean_inc_ref(v_e_22_);
lean_dec_ref_known(v_val_18_, 1);
v___x_32_ = lean_box(0);
lean_inc(v_table_14_);
v___x_33_ = lp_effect4_Effect4_Program_Table_typedAt(v_table_14_, v___x_32_);
if (lean_obj_tag(v___x_33_) == 1)
{
lean_object* v___x_34_; 
lean_dec_ref_known(v___x_33_, 1);
lean_inc(v_path_6_);
lean_inc(v_table_14_);
v___x_34_ = lp_effect4_Effect4_Program_Table_typedAt(v_table_14_, v_path_6_);
if (lean_obj_tag(v___x_34_) == 1)
{
lean_object* v_val_35_; lean_object* v_fst_36_; lean_object* v_snd_37_; lean_object* v___x_38_; lean_object* v_snd_39_; 
v_val_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_val_35_);
lean_dec_ref_known(v___x_34_, 1);
v_fst_36_ = lean_ctor_get(v_val_35_, 0);
lean_inc(v_fst_36_);
v_snd_37_ = lean_ctor_get(v_val_35_, 1);
lean_inc(v_snd_37_);
lean_dec(v_val_35_);
lean_inc(v_path_6_);
lean_inc_ref(v_sig_11_);
v___x_38_ = lp_effect4_Effect4_Program_Annotate_check___redArg(v_sig_11_, v_fst_36_, v_path_6_, v_program_7_);
v_snd_39_ = lean_ctor_get(v___x_38_, 1);
lean_inc(v_snd_39_);
if (lean_obj_tag(v_snd_39_) == 0)
{
lean_dec_ref_known(v_snd_39_, 1);
lean_dec_ref(v___x_38_);
lean_dec(v_snd_37_);
lean_dec(v_table_14_);
lean_dec(v_path_6_);
goto v___jp_23_;
}
else
{
lean_object* v_fst_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_59_; 
v_fst_40_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_59_ == 0)
{
lean_object* v_unused_60_; 
v_unused_60_ = lean_ctor_get(v___x_38_, 1);
lean_dec(v_unused_60_);
v___x_42_ = v___x_38_;
v_isShared_43_ = v_isSharedCheck_59_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_fst_40_);
lean_dec(v___x_38_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_59_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_58_; 
v_a_44_ = lean_ctor_get(v_snd_39_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v_snd_39_);
if (v_isSharedCheck_58_ == 0)
{
v___x_46_ = v_snd_39_;
v_isShared_47_ = v_isSharedCheck_58_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v_snd_39_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_58_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
uint8_t v___x_48_; 
v___x_48_ = lp_effect4_Effect4_Program_instDecidableEqEffTy_decEq(v_a_44_, v_snd_37_);
if (v___x_48_ == 0)
{
lean_del_object(v___x_46_);
lean_del_object(v___x_42_);
lean_dec(v_fst_40_);
lean_dec(v_table_14_);
lean_dec(v_path_6_);
goto v___jp_23_;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_53_; 
lean_del_object(v___x_20_);
lean_del_object(v___x_9_);
lean_inc(v_fst_40_);
v___x_49_ = lp_effect4_Effect4_Program_Table_splice(v_table_14_, v_path_6_, v_fst_40_);
lean_dec(v_path_6_);
v___x_50_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_50_, 0, v_sig_11_);
lean_ctor_set(v___x_50_, 1, v_env_12_);
lean_ctor_set(v___x_50_, 2, v_e_22_);
lean_ctor_set(v___x_50_, 3, v___x_49_);
v___x_51_ = lp_effect4_List_mapTR_loop___at___00Effect4_Program_EditSession_feed_spec__0(v_fst_40_, v___x_32_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 0, v___x_51_);
v___x_53_ = v___x_46_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_51_);
v___x_53_ = v_reuseFailAlloc_57_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
lean_object* v___x_55_; 
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___x_53_);
lean_ctor_set(v___x_42_, 0, v___x_50_);
v___x_55_ = v___x_42_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_53_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_34_);
lean_dec(v_table_14_);
lean_dec_ref(v_program_7_);
lean_dec(v_path_6_);
goto v___jp_23_;
}
}
else
{
lean_dec(v___x_33_);
lean_dec(v_table_14_);
lean_dec_ref(v_program_7_);
lean_dec(v_path_6_);
goto v___jp_23_;
}
v___jp_23_:
{
lean_object* v___x_24_; lean_object* v___x_26_; 
lean_inc_ref(v_e_22_);
lean_inc(v_env_12_);
lean_inc_ref(v_sig_11_);
v___x_24_ = lp_effect4_Effect4_Program_annotate___redArg(v_sig_11_, v_env_12_, v_e_22_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 3, v___x_24_);
lean_ctor_set(v___x_20_, 2, v_e_22_);
v___x_26_ = v___x_20_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_sig_11_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_env_12_);
lean_ctor_set(v_reuseFailAlloc_31_, 2, v_e_22_);
lean_ctor_set(v_reuseFailAlloc_31_, 3, v___x_24_);
v___x_26_ = v_reuseFailAlloc_31_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_27_ = lean_box(2);
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 1, v___x_27_);
lean_ctor_set(v___x_9_, 0, v___x_26_);
v___x_29_ = v___x_9_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_26_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v___x_27_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
}
else
{
lean_dec(v_val_18_);
lean_del_object(v___x_9_);
lean_dec_ref(v_program_7_);
lean_dec(v_path_6_);
goto v___jp_3_;
}
}
else
{
lean_dec(v___x_17_);
lean_del_object(v___x_9_);
lean_dec_ref(v_program_7_);
lean_dec(v_path_6_);
goto v___jp_3_;
}
}
}
}
LEAN_EXPORT lean_object* l_EditOverwatch_feedDeferred(lean_object* v_Op_67_, lean_object* v_l_68_, lean_object* v_x_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_EditOverwatch_feedDeferred___redArg(v_l_68_, v_x_69_);
return v___x_70_;
}
}
static lean_object* _init_l_EditOverwatch_expanded___closed__6(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = ((lean_object*)(l_EditOverwatch_expanded___closed__5));
v___x_86_ = lp_effect4_Test_Program_EditControls_opened;
v___x_87_ = lp_effect4_Effect4_Program_EditSession_feed___redArg(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l_EditOverwatch_expanded(void){
_start:
{
lean_object* v___x_88_; lean_object* v_fst_89_; 
v___x_88_ = lean_obj_once(&l_EditOverwatch_expanded___closed__6, &l_EditOverwatch_expanded___closed__6_once, _init_l_EditOverwatch_expanded___closed__6);
v_fst_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_fst_89_);
return v_fst_89_;
}
}
static lean_object* _init_l_EditOverwatch_shrunk___closed__0(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lp_effect4_Test_Program_EditControls_keep;
v___x_91_ = l_EditOverwatch_expanded;
v___x_92_ = lp_effect4_Effect4_Program_EditSession_feed___redArg(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_EditOverwatch_shrunk(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_obj_once(&l_EditOverwatch_shrunk___closed__0, &l_EditOverwatch_shrunk___closed__0_once, _init_l_EditOverwatch_shrunk___closed__0);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_EditOverwatch_semaphoreClient___lam__0(lean_object* v_q_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = ((lean_object*)(l_EditOverwatch_semaphoreClient___lam__0___closed__0));
v___x_100_ = lp_effect4_Effect4_Semaphore_takeIfAvailable(v_q_96_, v___x_99_, v___y_97_, v___y_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_EditOverwatch_semaphoreClient(lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___f_106_ = ((lean_object*)(l_EditOverwatch_semaphoreClient___closed__0));
v___x_107_ = ((lean_object*)(l_EditOverwatch_semaphoreClient___closed__1));
v___x_108_ = lp_effect4_Effect4_Program_Authoring_bindWith___redArg(v___x_107_, v___f_106_, v_a_104_, v_a_105_);
return v___x_108_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00EditOverwatch_moduleSplices_spec__0(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
if (lean_obj_tag(v_x_110_) == 0)
{
uint8_t v___x_111_; 
v___x_111_ = 1;
return v___x_111_;
}
else
{
uint8_t v___x_112_; 
lean_dec_ref_known(v_x_110_, 1);
v___x_112_ = 0;
return v___x_112_;
}
}
else
{
if (lean_obj_tag(v_x_110_) == 0)
{
uint8_t v___x_113_; 
lean_dec_ref_known(v_x_109_, 1);
v___x_113_ = 0;
return v___x_113_;
}
else
{
lean_object* v_val_114_; lean_object* v_val_115_; uint8_t v___x_116_; 
v_val_114_ = lean_ctor_get(v_x_109_, 0);
lean_inc(v_val_114_);
lean_dec_ref_known(v_x_109_, 1);
v_val_115_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_val_115_);
lean_dec_ref_known(v_x_110_, 1);
v___x_116_ = lp_effect4_Effect4_Program_instDecidableEqEffTy_decEq(v_val_114_, v_val_115_);
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00EditOverwatch_moduleSplices_spec__0___boxed(lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Option_instBEq_beq___at___00EditOverwatch_moduleSplices_spec__0(v_x_117_, v_x_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
static lean_object* _init_l_EditOverwatch_moduleSplices___closed__0(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_alloc_closure((void*)(l_EditOverwatch_semaphoreClient), 2, 0);
v___x_122_ = lp_effect4_Effect4_Api_Author_program(v___x_121_);
return v___x_122_;
}
}
static uint8_t _init_l_EditOverwatch_moduleSplices(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_EditOverwatch_moduleSplices___closed__0, &l_EditOverwatch_moduleSplices___closed__0_once, _init_l_EditOverwatch_moduleSplices___closed__0);
if (lean_obj_tag(v___x_123_) == 0)
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
else
{
lean_object* v_a_125_; lean_object* v_table_126_; lean_object* v_program_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v_opened_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v_snd_134_; 
v_a_125_ = lean_ctor_get(v___x_123_, 0);
v_table_126_ = lean_ctor_get(v_a_125_, 0);
v_program_127_ = lean_ctor_get(v_a_125_, 1);
lean_inc(v_table_126_);
v___x_128_ = lp_effect4_Effect4_Program_nativeSignature(v_table_126_);
v___x_129_ = lean_box(0);
lean_inc_ref_n(v_program_127_, 2);
v_opened_130_ = lp_effect4_Effect4_Program_EditSession_open___redArg(v___x_128_, v___x_129_, v_program_127_);
v___x_131_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_131_, 0, v_program_127_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_129_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
lean_inc_ref(v_opened_130_);
v___x_133_ = l_EditOverwatch_feedDeferred___redArg(v_opened_130_, v___x_132_);
v_snd_134_ = lean_ctor_get(v___x_133_, 1);
lean_inc(v_snd_134_);
if (lean_obj_tag(v_snd_134_) == 1)
{
lean_object* v_fst_135_; lean_object* v___x_136_; lean_object* v_refusals_137_; lean_object* v_type_138_; lean_object* v___x_139_; lean_object* v_type_140_; uint8_t v___x_141_; 
lean_dec_ref_known(v_snd_134_, 1);
v_fst_135_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_fst_135_);
lean_dec_ref(v___x_133_);
v___x_136_ = lp_effect4_Effect4_Program_EditSession_view___redArg(v_fst_135_);
v_refusals_137_ = lean_ctor_get(v___x_136_, 1);
lean_inc(v_refusals_137_);
v_type_138_ = lean_ctor_get(v___x_136_, 2);
lean_inc(v_type_138_);
lean_dec_ref(v___x_136_);
v___x_139_ = lp_effect4_Effect4_Program_EditSession_view___redArg(v_opened_130_);
v_type_140_ = lean_ctor_get(v___x_139_, 2);
lean_inc(v_type_140_);
lean_dec_ref(v___x_139_);
v___x_141_ = l_Option_instBEq_beq___at___00EditOverwatch_moduleSplices_spec__0(v_type_138_, v_type_140_);
if (v___x_141_ == 0)
{
lean_dec(v_refusals_137_);
return v___x_141_;
}
else
{
uint8_t v___x_142_; 
v___x_142_ = l_List_isEmpty___redArg(v_refusals_137_);
lean_dec(v_refusals_137_);
return v___x_142_;
}
}
else
{
uint8_t v___x_143_; 
lean_dec(v_snd_134_);
lean_dec_ref(v___x_133_);
lean_dec_ref(v_opened_130_);
v___x_143_ = 0;
return v___x_143_;
}
}
}
}
static lean_object* _init_l_EditOverwatch_holeSession___closed__0(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_box(2);
v___x_145_ = lp_effect4_Test_Program_SketchControls_sketchAt(v___x_144_);
return v___x_145_;
}
}
static lean_object* _init_l_EditOverwatch_holeSession(void){
_start:
{
lean_object* v___x_148_; lean_object* v_program_149_; lean_object* v_holes_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_148_ = lean_obj_once(&l_EditOverwatch_holeSession___closed__0, &l_EditOverwatch_holeSession___closed__0_once, _init_l_EditOverwatch_holeSession___closed__0);
v_program_149_ = lean_ctor_get(v___x_148_, 0);
v_holes_150_ = lean_ctor_get(v___x_148_, 1);
v___x_151_ = lean_box(0);
v___x_152_ = ((lean_object*)(l_EditOverwatch_holeSession___closed__1));
lean_inc(v_holes_150_);
v___x_153_ = lp_effect4_Effect4_Program_SigApp_withHoles(v___x_152_, v_holes_150_);
v___x_154_ = lp_effect4_Effect4_Program_SigApp_signature(v___x_153_);
lean_inc_ref(v_program_149_);
v___x_155_ = lp_effect4_Effect4_Program_EditSession_open___redArg(v___x_154_, v___x_151_, v_program_149_);
return v___x_155_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_effect4_Effect4_Author(uint8_t builtin);
lean_object* initialize_effect4_Effect4_Library(uint8_t builtin);
lean_object* initialize_effect4_Effect4_Program_Edit(uint8_t builtin);
lean_object* initialize_effect4_Test_Program_EditControls(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_docs_research_002026_x2d10_x2d08_x2dedit_x2dsession_x2doverwatch_Probe(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_effect4_Effect4_Author(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_effect4_Effect4_Library(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_effect4_Effect4_Program_Edit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_effect4_Test_Program_EditControls(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_EditOverwatch_expanded = _init_l_EditOverwatch_expanded();
lean_mark_persistent(l_EditOverwatch_expanded);
l_EditOverwatch_shrunk = _init_l_EditOverwatch_shrunk();
lean_mark_persistent(l_EditOverwatch_shrunk);
l_EditOverwatch_moduleSplices = _init_l_EditOverwatch_moduleSplices();
l_EditOverwatch_holeSession = _init_l_EditOverwatch_holeSession();
lean_mark_persistent(l_EditOverwatch_holeSession);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
