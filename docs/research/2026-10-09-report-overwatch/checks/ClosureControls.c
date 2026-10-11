// Lean compiler output
// Module: ClosureControls
// Imports: public import Init public meta import Init public import ProofGraph.ClosureAudit
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
lean_object* l_List_range(lean_object*);
uint8_t l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ReviewClosure_rebuilt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReviewClosure_rebuilt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ReviewClosure_instSizeOfRebuilt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReviewClosure_instSizeOfRebuilt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_ClosureControls_0__ReviewClosure_privateRebuilt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_ClosureControls_0__ReviewClosure_privateRebuilt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReviewClosure_proofOnly___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ReviewClosure_proofOnly___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ReviewClosure_proofOnly(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReviewClosure_proofOnly___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ReviewClosure_asData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReviewClosure_asData___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ReviewClosure_rebuilt(lean_object* v_n_1_, lean_object* v_k_2_){
_start:
{
lean_object* v_table_3_; uint8_t v___x_4_; 
v_table_3_ = l_List_range(v_n_1_);
v___x_4_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_k_2_, v_table_3_);
lean_dec(v_table_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_ReviewClosure_rebuilt___boxed(lean_object* v_n_5_, lean_object* v_k_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l_ReviewClosure_rebuilt(v_n_5_, v_k_6_);
lean_dec(v_k_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT uint8_t l_ReviewClosure_instSizeOfRebuilt(lean_object* v_n_9_, lean_object* v_k_10_){
_start:
{
lean_object* v_table_11_; uint8_t v___x_12_; 
v_table_11_ = l_List_range(v_n_9_);
v___x_12_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_k_10_, v_table_11_);
lean_dec(v_table_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_ReviewClosure_instSizeOfRebuilt___boxed(lean_object* v_n_13_, lean_object* v_k_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_ReviewClosure_instSizeOfRebuilt(v_n_13_, v_k_14_);
lean_dec(v_k_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l___private_ClosureControls_0__ReviewClosure_privateRebuilt(lean_object* v_n_17_, lean_object* v_k_18_){
_start:
{
lean_object* v_table_19_; uint8_t v___x_20_; 
v_table_19_ = l_List_range(v_n_17_);
v___x_20_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_k_18_, v_table_19_);
lean_dec(v_table_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_ClosureControls_0__ReviewClosure_privateRebuilt___boxed(lean_object* v_n_21_, lean_object* v_k_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l___private_ClosureControls_0__ReviewClosure_privateRebuilt(v_n_21_, v_k_22_);
lean_dec(v_k_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* l_ReviewClosure_proofOnly___redArg(lean_object* v_k_25_){
_start:
{
lean_inc(v_k_25_);
return v_k_25_;
}
}
LEAN_EXPORT lean_object* l_ReviewClosure_proofOnly___redArg___boxed(lean_object* v_k_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_ReviewClosure_proofOnly___redArg(v_k_26_);
lean_dec(v_k_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_ReviewClosure_proofOnly(lean_object* v_n_28_, lean_object* v_k_29_){
_start:
{
lean_inc(v_k_29_);
return v_k_29_;
}
}
LEAN_EXPORT lean_object* l_ReviewClosure_proofOnly___boxed(lean_object* v_n_30_, lean_object* v_k_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_ReviewClosure_proofOnly(v_n_30_, v_k_31_);
lean_dec(v_k_31_);
lean_dec(v_n_30_);
return v_res_32_;
}
}
LEAN_EXPORT uint8_t l_ReviewClosure_asData(lean_object* v_table_33_, lean_object* v_k_34_){
_start:
{
uint8_t v___x_35_; 
v___x_35_ = l_List_elem___at___00Lean_Meta_Grind_Arith_Cutsat_checkElimEqs_spec__0(v_k_34_, v_table_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_ReviewClosure_asData___boxed(lean_object* v_table_36_, lean_object* v_k_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_ReviewClosure_asData(v_table_36_, v_k_37_);
lean_dec(v_k_37_);
lean_dec(v_table_36_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ProofGraph_ClosureAudit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ClosureControls(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ProofGraph_ClosureAudit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
