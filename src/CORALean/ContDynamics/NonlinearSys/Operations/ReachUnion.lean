import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.ReachOrder
import CORALean.ContDynamics.NonlinearSys.Definitions.ReachParams
import CORALean.ContDynamics.NonlinearSys.Definitions.WithSteps
import CORALean.ContDynamics.NonlinearSys.Operations.RelinTimeInterval
import CORALean.ContSet.SetUnion.SetUnion

/-!
# The re-linearization loop as one union, or a run-time failure

`relinTimeInterval` at steps `0` through `N - 1`, one member of the `SetUnion`
per step — the `Reach.reach` field of the instance, [1, Alg. 1]'s `R([0, t_f])`.
Step `i`'s certificate is conservative only while the run stays in
`(steps i).R`, so, as CORA does, each step is tested before it is trusted, and
one failed test makes the answer `none`; `List.all` stops at the first `false`.

The test is the one `confined_of_ball` proves sound: the set step `i` starts
from, inflated by the box `‖·‖∞ ≤ 2MΔt`, inside `region i`. CORA tests the
time-interval set instead, which closes no induction here: its enclosure is
proved only for runs already confined over the whole step.

## References
* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Steps `0` through `p.N - 1` of `relinTimeInterval`, or `none` once the set
some step starts from, inflated by `2MΔt`, is not shown inside its region. -/
noncomputable def NonlinearSys.WithSteps.reachUnion (sys : NonlinearSys.WithSteps S Rg m n)
    (p : NonlinearSys.ReachParams) (X₀ : S n) : Option (SetUnion (S n)) :=
  let q := max p.q ((Finset.range p.N).sup fun i =>              -- order q + 2, admissible
    (NonlinearSys.linearize (sys.steps i).A).reachOrder p.Δt)     --   at every step's matrix
  let Ud := fun i => (NonlinearSys.linearize (sys.steps i).A).inputSolution p.Δt (q + 2)
    (sys.steps i).linInput                                        -- step i's input solution
  let R := fun i => sys.sys.relinReach ⟨X₀, 0, i⟩ ⟨p.Δt, p.o, p.ho⟩ sys.steps Ud  -- R(iΔt)
  let ρ := 2 * sys.M * p.Δt                                       -- beyond what one step moves
  let B : S n := OfInterval.ofInterval ⟨fun _ => -ρ, fun _ => ρ⟩  -- the box ‖·‖∞ ≤ ρ
  let confined := (List.range p.N).all fun i =>                   -- R(iΔt) ⊕ B ⊆ region i
    Contains.contains (sys.region i) (R i ⊞ B)
  if confined then                                                -- ⋃_{i < N} R(τ_i), or fail
    some ⟨(List.range p.N).map (sys.sys.relinTimeInterval p.o p.ho p.Δt (q + 2) sys.steps Ud X₀)⟩
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
