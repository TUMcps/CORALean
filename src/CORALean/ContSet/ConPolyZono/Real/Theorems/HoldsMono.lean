module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.holds_mono`

Widening `b` only admits more factor vectors, never fewer — what makes a
rounded bound sound, so the float layer can pay its error into `b` through it.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Widening a bound only admits more factor vectors, which is what makes a
rounded constraint sound. -/
theorem ConPolyZono.holds_mono {p m q : ℕ} {A : Mat ℝ m q} {b b' : Interval (Vec ℝ m)}
    {R : Fin p → Fin q → ℕ} {a : Fin p → ℝ} (hinf : ∀ i, b'.inf i ≤ b.inf i)
    (hsup : ∀ i, b.sup i ≤ b'.sup i) (h : ConPolyZono.holds A b R a) :
    ConPolyZono.holds A b' R a :=
  fun i => ⟨le_trans (hinf i) (h i).1, le_trans (h i).2 (hsup i)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
