import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderOrderSpec
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepEps
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter

/-!
# An enclosure asked for by error rather than by order

`timeIntervalStep_outer_at` carried over to the chosen order, and the point of
choosing one: its side condition `‖rA‖/(η+2) < 1` is gone, discharged by
`expRemainderOrder_spec`, and `0 < ε` is the only thing a caller supplies
beyond the step. So "enclose this with a remainder under `ε`" is a request the
library answers soundly, which is what a tuning rule has to mean here.

`2 ≤ η` is what lets the chosen order be written in the `m + 2` form
`timeIntervalStep_outer_at` takes; the selector's predicate carries it for exactly
that reason.

A smaller `ε` gives a tighter correction matrix, and
`timeIntervalStep_subset_reach_add_error` is what turns that into a statement
about the enclosure's own error. It also says `ε` reaches the smaller term
only: over a whole step the convex hull costs a first-order excess that the
correction matrix, second order, does not pay for.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow, at every time of the step,
with the order asked for by an admissible error instead of named. -/
theorem LinearSys.timeIntervalStepEps_outer (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r)
    {ε : ℝ} (hε : 0 < ε) (X₀ : S n) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀) '' construct X₀
      ⊆ construct (sys.timeIntervalStepEps r ε X₀) := by -- --- PROOF ---
  obtain ⟨h2, -, hs⟩ := MatExp.expRemainderOrder_spec (r • toRealMat sys.A) hε
  -- the outer theorem takes its order as `m + 2`, which `2 ≤ η` supplies
  obtain ⟨m, hm⟩ : ∃ m : ℕ, MatExp.expRemainderOrder (r • toRealMat sys.A) ε = m + 2 :=
    ⟨MatExp.expRemainderOrder (r • toRealMat sys.A) ε - 2, by omega⟩
  simp only [LinearSys.timeIntervalStepEps]
  rw [hm] at hs ⊢
  exact sys.timeIntervalStep_outer_at hr hs X₀ ht0 htr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
