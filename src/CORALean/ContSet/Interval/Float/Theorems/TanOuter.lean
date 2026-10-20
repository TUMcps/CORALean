module

public import CORALean.ContSet.Interval.Float.Operations.Tan

@[expose] public section

/-!
# `Interval.tan` contains the image under `tan`

On the principal branch, as `Real.Interval.tan_exact`: both corners in `(-π/2, π/2)`, where the
tangent increases; and where the computed cosine at both corners is positive, which
`tanDown`/`tanUp` need and `cosDown` evaluates.

## Inputs
* `p` – halving count
* `I` – interval box

## Hypotheses
* `hI` – bounds strictly inside `(-π/2, π/2)`
* `hc` – the lower cosine bound is positive at both ends

## Conclusion
* the tangent image of `I` lies in the result box
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.tan_outer [SoundFloatArithmetic 𝕋] (p : ℕ) (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, -(Real.pi / 2) < toReal (I.inf i) ∧ toReal (I.sup i) < Real.pi / 2)
    (hc : ∀ i, 0 < toReal (cosDown p (I.inf i)) ∧ 0 < toReal (cosDown p (I.sup i)))
    : -- --- CONCL ---
    (fun x i => Real.tan (x i)) '' I.construct ⊆ (I.tan p).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  have hD : ∀ y, toReal (I.inf i) ≤ y → y ≤ toReal (I.sup i) →
      y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := fun y h1 h2 =>
    ⟨lt_of_lt_of_le (hI i).1 h1, lt_of_le_of_lt h2 (hI i).2⟩
  have hl := hD _ le_rfl (le_trans hx'.1 hx'.2)
  have hu := hD _ (le_trans hx'.1 hx'.2) le_rfl
  have hxD := hD _ hx'.1 hx'.2
  exact ⟨le_trans (tanDown_le p _ (hc i).1) (Real.strictMonoOn_tan.monotoneOn hl hxD hx'.1),
    le_trans (Real.strictMonoOn_tan.monotoneOn hxD hu hx'.2) (le_tanUp p _ (hc i).2)⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
