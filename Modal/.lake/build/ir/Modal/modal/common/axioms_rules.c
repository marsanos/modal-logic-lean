// Lean compiler output
// Module: Modal.modal.common.axioms_rules
// Imports: Init Modal.modal.common.syntax Modal.common.inference_rule
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
LEAN_EXPORT lean_object* l_Modal_Axioms_n___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Modal_Axioms_k___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_CPL_Syntax_and___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_CPL_Syntax_iff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Axioms_m___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Axioms_n(lean_object*, lean_object*);
lean_object* l_CPL_Syntax_top___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Modal_Rules_nec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Axioms_k(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Rules_re(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Axioms_m(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Rules_re___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Rules_nec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Rules_re___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_5);
x_7 = l_CPL_Syntax_iff___redArg(x_5, x_2, x_3);
lean_inc(x_6);
x_8 = lean_apply_1(x_6, x_2);
x_9 = lean_apply_1(x_6, x_3);
x_10 = l_CPL_Syntax_iff___redArg(x_5, x_8, x_9);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_11);
x_13 = l_CPL_Syntax_iff___redArg(x_11, x_2, x_3);
lean_inc(x_12);
x_14 = lean_apply_1(x_12, x_2);
x_15 = lean_apply_1(x_12, x_3);
x_16 = l_CPL_Syntax_iff___redArg(x_11, x_14, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Modal_Rules_re(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Modal_Rules_re___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Modal_Rules_nec___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
lean_inc(x_2);
x_6 = lean_apply_1(x_4, x_2);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_2);
x_8 = lean_apply_1(x_7, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Modal_Rules_nec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Modal_Rules_nec___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Modal_Axioms_m___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_2);
x_7 = l_CPL_Syntax_and___redArg(x_4, x_2, x_3);
lean_inc(x_5);
x_8 = lean_apply_1(x_5, x_7);
x_9 = lean_apply_1(x_5, x_2);
x_10 = lean_apply_2(x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Modal_Axioms_m(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Modal_Axioms_m___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Modal_Axioms_k___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_apply_2(x_6, x_2, x_3);
lean_inc(x_5);
x_8 = lean_apply_1(x_5, x_7);
lean_inc(x_5);
x_9 = lean_apply_1(x_5, x_2);
x_10 = lean_apply_1(x_5, x_3);
lean_inc(x_6);
x_11 = lean_apply_2(x_6, x_9, x_10);
x_12 = lean_apply_2(x_6, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Modal_Axioms_k(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Modal_Axioms_k___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Modal_Axioms_n___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_CPL_Syntax_top___redArg(x_2);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Modal_Axioms_n(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Modal_Axioms_n___redArg(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_common_syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_common_inference__rule(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Modal_modal_common_axioms__rules(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_common_syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_common_inference__rule(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
