module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Logic.Function.CompTypeclasses
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope

@[expose] public section

/-!
# A polynomial zonotope as a zonotope: `zonotope_not_mono`

## Inputs
* none

## Hypotheses
* none

## Conclusion
* enclosing zonotope is not monotone under set inclusion

## References

* [1] [N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control,
      2020.](../../../../../../references/2020/kochdumper-hscc-utilizing-dependencies.md)
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The square of one factor: it denotes `[0,1]`, its generator reaching `[-1,1]`. -/
private abbrev PolyZonotope.aux_sq : PolyZonotope (Vec ℝ 1) :=
  ⟨1, 1, 0, 0, fun _ _ => 1, fun _ _ => 2, Fin.elim0⟩

/-- A wider interval written affinely, whose generator is already tight. -/
private abbrev PolyZonotope.aux_aff : PolyZonotope (Vec ℝ 1) :=
  ⟨1, 1, 0, fun _ => 1, fun _ _ => 1, fun _ _ => 1, Fin.elim0⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1]'s property (6) fails for `zonotope`: `α²` and `1 + α` denote `[0,1]` and
`[0,2]`, whose enclosures are `[-1,1]` and `[0,2]`. -/
theorem PolyZonotope.zonotope_not_mono : -- --- CONCL ---
    ¬ ∀ pZ₁ pZ₂ : PolyZonotope (Vec ℝ 1), pZ₁.construct ⊆ pZ₂.construct →
      pZ₁.zonotope.construct ⊆ pZ₂.zonotope.construct := by -- --- PROOF ---
  intro hmono
  -- the square's value is the affine one's, read at the factor `α² - 1`
  have hsub : PolyZonotope.aux_sq.construct ⊆ PolyZonotope.aux_aff.construct := by
    rintro _ ⟨a, β, ha, _, rfl⟩
    have hsq : a 0 ^ 2 ≤ 1 := by nlinarith [abs_le.1 (ha 0)]
    refine ⟨fun _ => a 0 ^ 2 - 1, Fin.elim0, fun k => ?_, fun j => j.elim0, ?_⟩
    · rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (a 0)]
    · funext i
      simp [PolyZonotope.monomial]
  -- `-1` is in the square's enclosure, its generator being free there
  have hmem : (fun _ => -1 : Vec ℝ 1) ∈ PolyZonotope.aux_sq.zonotope.construct := by
    refine ⟨fun _ => -1, fun j => by norm_num, ?_⟩
    funext i
    simp [PolyZonotope.zonotope]
  -- and in none of the affine one's, whose coordinate never drops below zero
  obtain ⟨β, hβ, heq⟩ := hmono _ _ hsub hmem
  have h0 : (-1 : ℝ) = 1 + β ⟨0, by simp [PolyZonotope.zonotope]⟩ := by
    simpa [PolyZonotope.zonotope] using congrFun heq 0
  have hb := abs_le.1 (hβ ⟨0, by simp [PolyZonotope.zonotope]⟩)
  linarith [hb.1, hb.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
