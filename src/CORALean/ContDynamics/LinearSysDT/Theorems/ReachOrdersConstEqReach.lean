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

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.reachOrders_const_eq_reach (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : S n) (k : ℕ) :
    sys.reachOrders (fun _ => o) (fun _ => ho) R₀ U k
      = sys.reach o ho R₀ U k := by -- --- PROOF ---
  induction k with
  | zero => rfl
  | succ k ih =>
    show reduce (plus (mtimes sys.A (sys.reachOrders (fun _ => o) (fun _ => ho) R₀ U k)) U) o
      = reduce (plus (mtimes sys.A (sys.reach o ho R₀ U k)) U) o
    rw [ih]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
