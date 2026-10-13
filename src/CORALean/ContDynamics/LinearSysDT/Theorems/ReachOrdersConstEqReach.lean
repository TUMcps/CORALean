import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate

/-!
# `reachOrders` at a constant sequence is `reach`

The two recursions are the same term at every step, `(fun _ => o) (k + 1)`
reducing to `o` by `rfl`: nothing distinguishes them but which argument the
order comes from. This is what keeps the two definitions from drifting apart
— a proof about `reach` alone is a proof about `reachOrders` at the sequence
that never changes.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.reachOrders_const_eq_reach (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : S n) (k : ℕ) :
    sys.reachOrders ⟨R₀, U, 0, k⟩ ⟨fun _ => o, fun _ => ho⟩
      = sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ := by -- --- PROOF ---
  induction k with
  | zero => rfl
  | succ k ih =>
    show reduce (plus (mtimes sys.A (sys.reachOrders ⟨R₀, U, 0, k⟩ ⟨fun _ => o, fun _ => ho⟩)) U) o
      = reduce (plus (mtimes sys.A (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)) U) o
    rw [ih]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
