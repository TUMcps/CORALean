module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrder
public import CORALean.ContDynamics.NonlinearSys.Definitions.WithSteps
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinTimeInterval
public import CORALean.ContDynamics.Reach.Definitions.Params
public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# The re-linearization loop as one union, or a run-time failure

`relinTimeInterval` at steps `0` through `N - 1`, one member of the `SetUnion`
per step — the `Reach.reach` field of the instance, [1, Alg. 1]'s `R([0, t_f])`.
`N = (tFinal - tStart) / Δt`, `none` unless it is a positive natural number,
CORA's integer-steps check, decided in ℝ since `Δt` is the real `discretize`
takes; `none` too at `ρ = 0`, CORA's `geone`. `η` is a floor,
raised to what every step's matrix admits. Step `i`'s certificate is conservative
only while the run stays in `(steps i).R`, so, as CORA does, each step is tested
before it is trusted, and one failed test makes the answer `none`.

The test is the one `confined_of_ball` proves sound: the set step `i` starts
from, inflated by the box `‖·‖∞ ≤ 2MΔt`, inside `region i`. CORA tests the
time-interval set instead, which closes no induction here: its enclosure is
proved only for runs already confined over the whole step.

## References
* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Steps `0` through `N - 1` of `relinTimeInterval`, `N = (tFinal - tStart) / Δt`,
or `none` if `N` is no positive natural, the order is `0`, or a step's start, inflated
by `2MΔt`, is not shown inside its region. -/
noncomputable def NonlinearSys.WithSteps.reachUnion (sys : NonlinearSys.WithSteps S Rg m n)
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachOptions ℝ) :
    Option (SetUnion (S n)) :=
  let X₀ := params.X₀                                             -- the paper's symbols
  let Δt := options.Δt
  let o := options.ρ
  let N := ⌈(params.tFinal - params.tStart) / Δt⌉₊               -- steps
  if h : 0 < Δt ∧ 0 < N ∧ (N : ℝ) * Δt = params.tFinal - params.tStart ∧ 0 < o then
    let q := max options.η ((Finset.range N).sup fun i => -- order q + 2, admissible
      (NonlinearSys.linearize (sys.steps i).A).reachOrder Δt)     --   at every step's matrix
    let Ud := fun i => (NonlinearSys.linearize (sys.steps i).A).inputSolution Δt (q + 2)
      (sys.steps i).linInput                                      -- step i's input solution
    let R := fun i => sys.sys.relinReach ⟨X₀, 0, i⟩ ⟨Δt, o, h.2.2.2⟩ sys.steps Ud  -- R(iΔt)
    let ρ := 2 * sys.M * Δt                                       -- beyond what one step moves
    let B : S n := OfInterval.ofInterval ⟨fun _ => -ρ, fun _ => ρ⟩  -- the box ‖·‖∞ ≤ ρ
    let confined := (List.range N).all fun i =>                   -- R(iΔt) ⊕ B ⊆ region i
      Contains.contains (sys.region i) (R i ⊞ B)
    if confined then                                              -- ⋃_{i < N} R(τ_i), or fail
      some ⟨(List.range N).map (sys.sys.relinTimeInterval o h.2.2.2 Δt (q + 2) sys.steps Ud X₀)⟩
    else none
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
