import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.holds_mono`

Widening `b` only admits more factor vectors, never fewer — what makes a
rounded bound sound, so the float layer can pay its error into `b` through it.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- Widening a bound only admits more factor vectors, which is what makes a
rounded constraint sound. -/
theorem ConPolyZono.holds_mono {p m s : ℕ} {A : Mat ℝ m s} {b b' : Interval (Vec ℝ m)}
    {EC : Fin p → Fin s → ℕ} {a : Fin p → ℝ} (hinf : ∀ i, b'.inf i ≤ b.inf i)
    (hsup : ∀ i, b.sup i ≤ b'.sup i) (h : ConPolyZono.holds A b EC a) :
    ConPolyZono.holds A b' EC a :=
  fun i => ⟨le_trans (hinf i) (h i).1, le_trans (h i).2 (hsup i)⟩

end CORALean.Real
