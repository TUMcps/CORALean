module

public import CORALean.Specification.AtomicProposition.Operations.EvaluatePoint
public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.Covers
public import CORALean.Specification.TrajectoryAnalyzer.TrajectoryAnalyzer

@[expose] public section

/-!
# Where the analyzer marks a proposition true

Proposition `k` is marked true at the time `τ` of a signal of duration `dur` by the time point with
index `l` of the realization `s` when it holds at the point `x(:,l,s)`, at the location `loc(:,l)`
(`1` without locations), and the interval `[t(l),t(l+1))` covers `τ` (`Covers`).

## Inputs
* `obj` – analyzer
* `s` – realization index
* `dur` – signal duration
* `k` – proposition key
* `l` – time point index
* `τ` – time

## Output
* the time point marks the proposition true at the time
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

/-- The time point `l` of realization `s` marks proposition `k` true at `τ`. -/
def TrajectoryAnalyzer.TrueAt (obj : TrajectoryAnalyzer ℝ 𝕋 S n) (s : ℕ) (dur : ℝ) (k : String)
    (l : ℕ) (τ : ℝ) : Prop :=
  ∃ ap, (k, ap) ∈ obj.aps ∧ ap.evaluatePoint (obj.traj.x l s)
      (if obj.traj.loc ≠ [] then obj.traj.loc.getD (l - 1) 0 else 1) = true ∧
    FiniteKleeneSignalBuilder.Covers dur τ (obj.traj.t.getD (l - 1) 0) (obj.traj.t.getD l 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
