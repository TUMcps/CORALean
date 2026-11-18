module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec

@[expose] public section

/-!
# A translated input set: its constant part, integrated, plus the rest

Inputs in `v + U` are `v` plus inputs in `U`, so over `[0, t]` they contribute
`(∫₀ᵗ e^{As} ds) v` plus what `U` contributes: `inputReach (v + U) t` is `inputReach U t`
translated by `expIntegral t v`. The constant input of CORA's canonical form `u_trans` is this
`v`, and the generators of the input set the `U` about the origin.

## Inputs
* `sys` – linear system
* `U` – input set about the origin
* `t` – time
* `v` – constant part of the input

## Hypotheses
* `hbdd` – input set bounded
* `ht` – time nonnegative

## Conclusion
* the input reach of the translated set is the translated input reach
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSetLike Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.inputReach_image_add (sys : LinearSys 𝕋 n) {U : Set (Vec ℝ n)}
    (hbdd : Bornology.IsBounded U) {t : ℝ} (ht : 0 ≤ t) (v : Vec ℝ n) : -- --- CONCL ---
    sys.inputReach (S := ExactSet) ((fun x => v + x) '' U) t
      = (fun y => MatExp.expIntegral (toRealMat sys.A) t *ᵥ v + y) ''
        sys.inputReach (S := ExactSet) U t := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  have hv : Bornology.IsBounded (({v} : Set (Vec ℝ n))) := Bornology.isBounded_singleton
  have hvint : IntervalIntegrable (fun s => exp ((t - s) • A) *ᵥ v) volume 0 t :=
    intervalIntegrable_expSub_mulVec (S := ExactSet) (U := ({v} : Set (Vec ℝ n))) (A := A)
      (c := t) ht hv (fun _ _ => rfl) aestronglyMeasurable_const
  ext y
  constructor
  · -- an input in `v + U` is `v` plus an input in `U`
    rintro ⟨u, hmem, hmeas, rfl⟩
    have hmem' : ∀ s ∈ Set.Icc (0:ℝ) t, u s - v ∈ U := by
      intro s hs
      obtain ⟨x, hx, hxe⟩ := hmem s hs
      rw [← hxe, add_sub_cancel_left]
      exact hx
    have hint := intervalIntegrable_expSub_mulVec (S := ExactSet) (U := U) (A := A) (c := t) ht
      hbdd hmem' (hmeas.sub aestronglyMeasurable_const)
    refine ⟨∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ (u s - v),
      ⟨fun s => u s - v, hmem', hmeas.sub aestronglyMeasurable_const, rfl⟩, ?_⟩
    rw [← Real.MatExp.expIntegral_constInput A v ht]
    dsimp only
    rw [← intervalIntegral.integral_add hvint hint]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [Matrix.mulVec_sub]
    abel
  · -- and back
    rintro ⟨y₀, ⟨u, hmem, hmeas, rfl⟩, rfl⟩
    have hint := intervalIntegrable_expSub_mulVec (S := ExactSet) (U := U) (A := A) (c := t) ht
      hbdd hmem hmeas
    refine ⟨fun s => v + u s, fun s hs => ⟨u s, hmem s hs, rfl⟩,
      aestronglyMeasurable_const.add hmeas, ?_⟩
    rw [← Real.MatExp.expIntegral_constInput A v ht]
    dsimp only
    rw [← intervalIntegral.integral_add hvint hint]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [Matrix.mulVec_add, hA]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
