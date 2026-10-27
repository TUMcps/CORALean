module

public import CORALean.ContSet.ConZonotope.Real.Operations.Constrain
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The printed image of the factor bounds can miss the constrained zonotope

[1, Eq. 13] as printed, `Z|_{C≤d} ⊆ c ⊕ [G⁺ β̲ - G⁻ β̄, G⁺ β̄ - G⁻ β̲]`, with `G⁻ = ½(G - |G|)`,
the entries `≤ 0`, the reading under which [1, Prop. 3] holds. For `Z = ⟨0, [-1]⟩_Z = [-1, 1]`
without constraints and the exact factor bounds `[-1, 1]`, `G⁺ = 0` and `G⁻ = -1`, so the printed
interval runs from `0 + 1 = 1` down to `0 - 1 = -1`, empty, and misses `0 ∈ Z`. The minus signs
are right for `G⁻ = ½(|G| - G)` (`Zonotope.intervalOfFactorBounds` writes the corrected form).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed interval misses a point of the constrained zonotope

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations,
      2026.](../../../../../../references/2026/koller-iclr-latent-space.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Z = ⟨0, [-1]⟩_Z ⊂ ℝ`. -/
private abbrev aux_Z : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ _ => -1⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 13] as printed misses a point of the constrained zonotope. -/
theorem Zonotope.intervalOfFactorBoundsPrinted_counterexample : -- --- CONCL ---
    ∃ (Z : Zonotope (Vec ℝ 1)) (C : Mat ℝ 0 Z.h) (d : Vec ℝ 0) (B : Interval (Vec ℝ Z.h)),
      (∀ β : Vec ℝ Z.h, (∀ j, |β j| ≤ 1) → β ∈ (HPolytope.ineqs C d).construct →
        β ∈ B.construct) ∧
      ¬ (Z.constrain C d).construct ⊆ (⟨
        Z.c + (fun i j => (Z.G j i + |Z.G j i|) / 2 : Mat ℝ 1 Z.h) *ᵥ B.inf -
          (fun i j => (Z.G j i - |Z.G j i|) / 2 : Mat ℝ 1 Z.h) *ᵥ B.sup,
        Z.c + (fun i j => (Z.G j i + |Z.G j i|) / 2 : Mat ℝ 1 Z.h) *ᵥ B.sup -
          (fun i j => (Z.G j i - |Z.G j i|) / 2 : Mat ℝ 1 Z.h) *ᵥ B.inf⟩ :
        Interval (Vec ℝ 1)).construct := by -- --- PROOF ---
  refine ⟨aux_Z, fun i => i.elim0, fun i => i.elim0, ⟨fun _ => -1, fun _ => 1⟩,
    fun β hβ _ j => abs_le.1 (hβ j), fun hsub => ?_⟩
  -- `0 = 0 + 0 · (-1)` is in `Z`, and the printed interval is `[1, -1]`
  have h0 := hsub (a := 0) ⟨fun _ => 0, fun _ => by simp, (HPolytope.mem_ineqs_iff).2
    fun i => i.elim0, by funext; simp [Zonotope.constrain]⟩ 0
  change (0 : ℝ) + ∑ j : Fin 1, (-1 + |(-1 : ℝ)|) / 2 * (-1) -
      ∑ j : Fin 1, (-1 - |(-1 : ℝ)|) / 2 * 1 ≤ 0 ∧ _ at h0
  norm_num at h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
