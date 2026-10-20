module

public import CORALean.ContSet.ContSet.Theorems.ProjectOuter
public import CORALean.Specification.AtomicProposition.Definitions.Holds
public import CORALean.Specification.AtomicProposition.Operations.CanBeTrue

@[expose] public section

/-!
# `canBeTrue` is sound

If a point of the set satisfies the proposition, `canBeTrue` says the proposition can be true on
the set. Contrapositively, `canBeTrue = false` says that no point of the set satisfies it. The
converse does not hold: the intersection test is conservative, and `true` says only that no
disjointness was shown.

## Inputs
* `ap` – atomic proposition
* `s` – set
* `loc` – location
* `x` – point of the set

## Hypotheses
* `hx` – the point lies in the set
* `h` – the point satisfies the proposition

## Conclusion
* `canBeTrue` returns true
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, IsDisjoint (S k) (S k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem AtomicProposition.canBeTrue_sound (ap : AtomicProposition S n) (s : S n) (loc : ℕ)
    {x : Vec ℝ n} (hx : x ∈ construct s) (h : ap.Holds x loc) :
    ap.canBeTrue (𝕋 := 𝕋) s loc = true := by -- --- PROOF ---
  unfold AtomicProposition.canBeTrue
  rw [if_neg (by simp [h.1])]
  -- if the two sets were disjoint, the point read at `dims` would be in neither
  simp only [Bool.not_eq_true']
  by_contra hd
  have hdis := IsDisjoint.isDisjoint_sound _ _ (by simpa using hd)
  exact Set.disjoint_left.mp hdis (ContSet.project_outer (𝕋 := 𝕋) s ap.dims ⟨x, hx, rfl⟩) h.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
