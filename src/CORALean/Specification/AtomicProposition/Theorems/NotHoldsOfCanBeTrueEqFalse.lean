module

public import CORALean.Specification.AtomicProposition.Theorems.CanBeTrueSound

@[expose] public section

/-!
# `canBeTrue = false` excludes every point

If `canBeTrue` is false, no point of the set satisfies the proposition: the contrapositive of
`canBeTrue_sound`.
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

theorem AtomicProposition.not_holds_of_canBeTrue_eq_false (ap : AtomicProposition S n)
    (s : S n) (loc : ℕ) (h : ap.canBeTrue (𝕋 := 𝕋) s loc = false) {x : Vec ℝ n}
    (hx : x ∈ construct s) : ¬ ap.Holds x loc :=
  fun hh => by simp [AtomicProposition.canBeTrue_sound (𝕋 := 𝕋) ap s loc hx hh] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
