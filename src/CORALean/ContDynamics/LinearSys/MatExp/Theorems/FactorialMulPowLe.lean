import CORALean.ContDynamics.LinearSys.MatExp.Enclosures

/-!
# A factorial outgrows a power by at least one factor per step

Shared by `scalar_term_le` and `norm_exp_sub_expTaylor_le`, both of which turn
a factorial-vs-power tail into a geometric one: `(a+k)!` outgrows `a!` by at
least `(a+1)` every step past it, which is the one fact both bounds invert
into their geometric ratio.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- `(a+k)!` outgrows `a` factorial by at least `(a+1)` each step, which is what
makes the tail geometric. -/
theorem factorial_mul_pow_le (a k : ℕ) :
    Nat.factorial a * (a + 1) ^ k ≤ Nat.factorial (a + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : Nat.factorial (a + (k + 1)) = (a + k + 1) * Nat.factorial (a + k) := by
      rw [← Nat.add_assoc]; exact Nat.factorial_succ _
    calc Nat.factorial a * (a + 1) ^ (k + 1)
        = (Nat.factorial a * (a + 1) ^ k) * (a + 1) := by ring
      _ ≤ Nat.factorial (a + k) * (a + 1)           := Nat.mul_le_mul_right _ ih
      _ ≤ Nat.factorial (a + k) * (a + k + 1)       := Nat.mul_le_mul_left _ (by omega)
      _ = Nat.factorial (a + (k + 1))               := by rw [hstep]; ring

end CORALean.Real
