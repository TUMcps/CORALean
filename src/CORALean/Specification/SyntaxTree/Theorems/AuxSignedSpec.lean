module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `aux_signed_` holds the point

When `intPrev` holds `s` and `|s|` is between the two roots, `aux_signed_` is an interval whose
bounds
enclose `s`: the sign of `s` is the one `intPrev` allows.

## Inputs
* `prev` – previous interval
* `t₁` – lower bound of the absolute value
* `t₂` – upper bound of the absolute value
* `s` – solution

## Hypotheses
* `hs` – the previous interval contains the solution
* `h₁` – the lower bound is at most the absolute value
* `h₂` – the absolute value is at most the upper bound

## Conclusion
* the signed roots form an interval containing the solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_signed_` is an interval `lo..hi` with `lo ≤ s ≤ hi`. -/
theorem SyntaxTree.signedRoots_spec {prev : Dom} {t₁ t₂ s : ℝ} (hs : Dom.contains prev s)
    (h₁ : t₁ ≤ |s|) (h₂ : |s| ≤ t₂) : -- --- CONCL ---
    ∃ lo hi, signedRoots prev t₁ t₂ = interval lo hi ∧ lo ≤ s ∧ s ≤ hi := by -- --- PROOF ---
  unfold signedRoots
  split_ifs with hc hp
  · -- `intPrev` contains `0`: both signs
    exact ⟨_, _, rfl, by linarith [neg_abs_le s, le_max_right t₁ t₂],
      by linarith [le_abs_self s, le_max_right t₁ t₂]⟩
  · -- `intPrev` is nonnegative
    have hs0 : 0 ≤ s := hs.1.trans' (not_lt.1 (fun h => hc ⟨hp, h⟩)) |>.trans_eq rfl
    rw [abs_of_nonneg hs0] at h₁ h₂
    exact ⟨_, _, rfl, (min_le_left _ _).trans h₁, h₂.trans (le_max_right _ _)⟩
  · -- `intPrev` is nonpositive
    have hs0 : s ≤ 0 := hs.2.trans (not_lt.1 hp)
    rw [abs_of_nonpos hs0] at h₁ h₂
    exact ⟨_, _, rfl, by linarith [le_max_right t₁ t₂], by linarith [min_le_left t₁ t₂]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
