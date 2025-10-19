// Lean compiler output
// Module: Modal.modal.common.formula
// Imports: Init Modal.modal.common.syntax Modal.common.logic Modal.cpl.syntax Modal.cpl.formula
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
LEAN_EXPORT lean_object* l_Modal_Formula_atom_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_instDecidableEqFormula_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_instDecidableEqFormula___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Modal_instDecidableEqFormula_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_bot_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Modal_instDecidableEqFormula___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_atom_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_bot_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_instSyntaxFormula___lam__1(lean_object*);
LEAN_EXPORT uint8_t l_Modal_instDecidableEqFormula(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_impl_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_impl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_instDecidableEqFormula___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_instDecidableEqFormula_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_instSyntaxFormula___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_instSyntaxFormula(lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_box_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_to__cpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_box_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_to__cpl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Modal_instDecidableEqFormula_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Modal_Formula_ctorIdx___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Modal_Formula_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Modal_Formula_ctorIdx___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Modal_Formula_ctorIdx(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
return x_2;
}
case 2:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Modal_Formula_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Modal_Formula_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_atom_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Modal_Formula_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_atom_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Modal_Formula_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_bot_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Modal_Formula_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_bot_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Modal_Formula_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_impl_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Modal_Formula_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_impl_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Modal_Formula_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_box_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Modal_Formula_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Modal_Formula_box_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Modal_Formula_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Modal_instDecidableEqFormula_decEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = 0;
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_apply_2(x_1, x_4, x_6);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
uint8_t x_9; 
x_9 = lean_unbox(x_7);
return x_9;
}
}
case 1:
{
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
default: 
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
}
case 1:
{
lean_dec_ref(x_1);
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
x_11 = 0;
return x_11;
}
}
case 2:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = 0;
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_1);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_17 = l_Modal_instDecidableEqFormula_decEq___redArg(x_1, x_12, x_15);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_1);
return x_14;
}
else
{
uint8_t x_18; 
x_18 = l_Modal_instDecidableEqFormula_decEq___redArg(x_1, x_13, x_16);
if (x_18 == 0)
{
return x_14;
}
else
{
return x_18;
}
}
}
default: 
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_14;
}
}
}
default: 
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec_ref(x_2);
x_20 = 0;
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_dec(x_19);
lean_dec_ref(x_1);
return x_20;
}
case 3:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
lean_dec_ref(x_3);
x_22 = l_Modal_instDecidableEqFormula_decEq___redArg(x_1, x_19, x_21);
if (x_22 == 0)
{
return x_20;
}
else
{
return x_22;
}
}
default: 
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_20;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Modal_instDecidableEqFormula_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Modal_instDecidableEqFormula_decEq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Modal_instDecidableEqFormula_decEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Modal_instDecidableEqFormula_decEq___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Modal_instDecidableEqFormula_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Modal_instDecidableEqFormula_decEq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Modal_instDecidableEqFormula___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Modal_instDecidableEqFormula_decEq___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Modal_instDecidableEqFormula(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Modal_instDecidableEqFormula_decEq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Modal_instDecidableEqFormula___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Modal_instDecidableEqFormula___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Modal_instDecidableEqFormula___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Modal_instDecidableEqFormula(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Modal_instSyntaxFormula___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Modal_instSyntaxFormula___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Modal_instSyntaxFormula(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_closure((void*)(l_Modal_instSyntaxFormula___lam__0), 2, 0);
x_3 = lean_alloc_closure((void*)(l_Modal_instSyntaxFormula___lam__1), 1, 0);
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Modal_to__cpl___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; 
x_2 = lean_box(1);
return x_2;
}
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Modal_to__cpl___redArg(x_4);
x_7 = l_Modal_to__cpl___redArg(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Modal_to__cpl___redArg(x_8);
x_11 = l_Modal_to__cpl___redArg(x_9);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
default: 
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Modal_to__cpl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Modal_to__cpl___redArg(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_common_syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_common_logic(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_cpl_syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_cpl_formula(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Modal_modal_common_formula(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_common_syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_common_logic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_cpl_syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_cpl_formula(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
