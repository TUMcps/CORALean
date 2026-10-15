module

public import CORALean.Specification.AtomicProposition.Theorems.CanBeFalseSound

@[expose] public section

/-!
# `canBeFalse = false` bounds every point

If `canBeFalse` is false, every point of the set satisfies the proposition: the contrapositive of
`canBeFalse_sound`.
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

theorem AtomicProposition.holds_of_canBeFalse_eq_false (ap : AtomicProposition S n) (s : S n)
    (loc : ℕ) (h : ap.canBeFalse (𝕋 := 𝕋) s loc = false) {x : Vec ℝ n} (hx : x ∈ construct s) :
    ap.Holds x loc :=
  not_not.mp fun hh => by simp [AtomicProposition.canBeFalse_sound (𝕋 := 𝕋) ap s loc hx hh] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
