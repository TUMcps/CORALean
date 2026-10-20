module

public import CORALean.ContSet.ContSet.Theorems.ProjectOuter
public import CORALean.Specification.AtomicProposition.Definitions.Holds
public import CORALean.Specification.AtomicProposition.Operations.CanBeFalse

@[expose] public section

/-!
# `canBeFalse` is sound

If a point of the set does not satisfy the proposition, `canBeFalse` says the proposition can be
false on the set. Contrapositively, `canBeFalse = false` says that every point of the set
satisfies it. The converse does not hold: the containment test is conservative.

## Inputs
* `ap` – atomic proposition
* `s` – set
* `loc` – location
* `x` – point of the set

## Hypotheses
* `hx` – the point lies in the set
* `h` – the point violates the proposition

## Conclusion
* `canBeFalse` returns true
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem AtomicProposition.canBeFalse_sound (ap : AtomicProposition S n) (s : S n) (loc : ℕ)
    {x : Vec ℝ n} (hx : x ∈ construct s) (h : ¬ ap.Holds x loc) : -- --- CONCL ---
    ap.canBeFalse (𝕋 := 𝕋) s loc = true := by -- --- PROOF ---
  unfold AtomicProposition.canBeFalse
  by_cases hl : ap.containsLoc loc = true
  · -- the location is allowed, so the point must be outside the set, which then is not contained
    have hout : ap.readPoint x ∉ construct ap.set := fun hm => h ⟨hl, hm⟩
    have hc : Contains.contains ap.set (ContSet.project (𝕋 := 𝕋) s ap.dims) = false := by
      by_contra hc
      exact hout (Contains.contains_sound _ _ (by simpa using hc)
        (ContSet.project_outer (𝕋 := 𝕋) s ap.dims ⟨x, hx, rfl⟩))
    simp [hc]
  · have : ap.containsLoc loc = false := by simpa using hl
    simp [this]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
