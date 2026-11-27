import Lean
import PortableLean_Strengthened_Lean4322


/-!
  PortableLean_VerifyAxioms_Lean4322.lean
  =======================================
  Declaration-by-declaration semantic axiom audit for all 16 theorems in
  `PortableLean_Strengthened_Lean4322.lean` (git blob SHA
  `130b363ba07c26dda43976486bd8d4da87136c68`).


  1. Prints `#print axioms` for every theorem (for CI log inspection).
  2. Runs a compile-time meta-check (`Lean.collectAxioms`) that FAILS
     elaboration if ANY declaration depends on `sorryAx` or any axiom
     outside the standard Lean 4 core set (`propext`, `Classical.choice`,
     `Quot.sound`), and reports exact per-declaration axiom usage.


  Drop-in usage inside `kolberz/Toolchain_factory`:
    Stage alongside `PortableLean_Strengthened_Lean4322.lean` and run
    `lake env lean PortableLean_VerifyAxioms_Lean4322.lean` inside the
    pinned Lean 4.32.2 portable builder.
-/


open Lean Elab Command


#print axioms PortableLean.poly_id
#print axioms PortableLean.modus_ponens
#print axioms PortableLean.church_2_plus_2
#print axioms PortableLean.catalytic_restores_u
#print axioms PortableLean.catalytic_restores_v
#print axioms PortableLean.catalytic_computes_product
#print axioms PortableLean.ternary_4trits_fit_7bits
#print axioms PortableLean.ternary_4trits_capacity_values
#print axioms PortableLean.ternary_4trits_capacity_slack
#print axioms PortableLean.syracuse_weight_at_one
#print axioms PortableLean.syracuse_sevenfold_weight_at_one
#print axioms PortableLean.hadwiger_1d_cover
#print axioms PortableLean.hadwiger_integer_cube_cover
#print axioms PortableLean.sample_regret_threshold_certificate
#print axioms PortableLean.oblique_chordal_linear_bound
#print axioms PortableLean.oblique_chordal_squared_bound


run_cmd do
  let targets : List Name := [
    `PortableLean.poly_id,
    `PortableLean.modus_ponens,
    `PortableLean.church_2_plus_2,
    `PortableLean.catalytic_restores_u,
    `PortableLean.catalytic_restores_v,
    `PortableLean.catalytic_computes_product,
    `PortableLean.ternary_4trits_fit_7bits,
    `PortableLean.ternary_4trits_capacity_values,
    `PortableLean.ternary_4trits_capacity_slack,
    `PortableLean.syracuse_weight_at_one,
    `PortableLean.syracuse_sevenfold_weight_at_one,
    `PortableLean.hadwiger_1d_cover,
    `PortableLean.hadwiger_integer_cube_cover,
    `PortableLean.sample_regret_threshold_certificate,
    `PortableLean.oblique_chordal_linear_bound,
    `PortableLean.oblique_chordal_squared_bound
  ]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for decl in targets do
    let axioms ← collectAxioms decl
    for ax in axioms do
      if ax == `sorryAx then
        throwError "AUDIT FAIL: {decl} depends on sorryAx"
      if !allowed.contains ax then
        throwError "AUDIT FAIL: {decl} depends on unpermitted axiom {ax}"
    logInfo m!"AUDIT OK: {decl} -> axioms = {axioms.toList}"