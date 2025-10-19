// Lean compiler output
// Module: Modal
// Imports: Init Modal.common.inference_rule Modal.common.logic Modal.cpl.formula Modal.cpl.proof Modal.cpl.syntax Modal.modal.common.axioms_rules Modal.modal.common.formula Modal.modal.common.syntax Modal.modal.proof_systems.K_proof Modal.modal.proof_systems.E_proof Modal.modal.proof_systems.M_proof Modal.modal.models.dual Modal.modal.models.kripke Modal.modal.models.nbhd Modal.modal.sound_complete.E_nbhd Modal.modal.sound_complete.K_kripke Modal.modal.sound_complete.M_upnbhd
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_common_inference__rule(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_common_logic(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_cpl_formula(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_cpl_proof(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_cpl_syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_common_axioms__rules(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_common_formula(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_common_syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_proof__systems_K__proof(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_proof__systems_E__proof(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_proof__systems_M__proof(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_models_dual(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_models_kripke(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_models_nbhd(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_sound__complete_E__nbhd(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_sound__complete_K__kripke(uint8_t builtin, lean_object*);
lean_object* initialize_Modal_modal_sound__complete_M__upnbhd(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Modal(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_common_inference__rule(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_common_logic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_cpl_formula(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_cpl_proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_cpl_syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_common_axioms__rules(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_common_formula(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_common_syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_proof__systems_K__proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_proof__systems_E__proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_proof__systems_M__proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_models_dual(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_models_kripke(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_models_nbhd(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_sound__complete_E__nbhd(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_sound__complete_K__kripke(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Modal_modal_sound__complete_M__upnbhd(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
