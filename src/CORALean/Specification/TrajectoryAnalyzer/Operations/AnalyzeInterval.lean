module

public import CORALean.Specification.AtomicProposition.Operations.EvaluatePoint
public import CORALean.Specification.TrajectoryAnalyzer.Operations.MarkKey

@[expose] public section

/-!
# One interval of the simulation

The body of the loop of `analyze` for the time point with index `l`: the point `x(:,l,s)` of the
realization stands for the whole time interval `[t(l),t(l+1)]`, "an approximation; however, since
simulation results have no claim of correctness this inaccuracy is acceptable here" (CORA). The
location is `loc(:,l)`, or `1` if the simulation has none. Every proposition that holds at the point
is marked true in its signal on the interval.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} {n : ℕ} [∀ k, ContSet (S k) (Vec ℝ k)]
  [OfScalarPoint 𝕋 S] [∀ k, Contains (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The loop body of `analyze(obj,s)` for `l`. -/
noncomputable def TrajectoryAnalyzer.analyzeInterval (obj : TrajectoryAnalyzer 𝕋 S n) (s : ℕ)
    (dur : ℝ) (sigs : List (String × FiniteSignal ℝ Bool)) (l : ℕ) :
    Option (List (String × FiniteSignal ℝ Bool)) :=
  -- obtain value of simulation
  let point := obj.traj.x l s
  -- set location property
  let loc := if obj.traj.loc ≠ [] then obj.traj.loc.getD (l - 1) 0 else 1
  -- calculate time interval
  let lo := obj.traj.t.getD (l - 1) 0
  let hi := obj.traj.t.getD l 0
  -- check all atomic propositions
  obj.aps.foldlM (fun sigs p =>
    if p.2.evaluatePoint point loc = true then TrajectoryAnalyzer.markKey dur lo hi sigs p.1
    else some sigs) sigs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
