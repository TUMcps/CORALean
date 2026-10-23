module

public import CORALean.Specification.FiniteSignal.Operations.Mk
public import CORALean.Specification.TrajectoryAnalyzer.Operations.AnalyzeInterval

@[expose] public section

/-!
# The analysis of a simulation

`sigs = analyze(obj,s)`: for the realization `s` of the simulation, one Boolean signal per
proposition, of the duration `dur = t(:,end)` of the simulation, true on the time intervals whose
first point satisfies the proposition. CORA's `analyze(obj,s,j)` also picks the `j`-th of an array
of analyzers; that is plumbing. It throws for an empty simulation, a negative duration or a
degenerate interval; here `none`.

## Inputs
* `obj` – analyzer
* `s` – realization index

## Output
* the signal of each proposition, or none where CORA throws
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T 𝕋 : Type} [TimeOrder T] [Zero T] [Scalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)]
  [OfScalarPoint 𝕋 S] [∀ k, Contains (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sigs = analyze(obj,s)`. -/
def TrajectoryAnalyzer.analyze (obj : TrajectoryAnalyzer T 𝕋 S n) (s : ℕ) :
    Option (List (String × FiniteSignal T Bool)) :=
  -- dur = obj.traj.t(:,end)
  obj.traj.t.getLast?.bind fun dur =>
    -- prepare signals for all atomic propositions
    (obj.aps.mapM fun p => (FiniteSignal.mk? [dur] [false]).map fun sig => (p.1, sig)).bind
      fun sigs =>
        -- for l = 1:size(obj.traj.t,2)-1
        (List.range' 1 (obj.traj.t.length - 1)).foldlM
          (fun sigs l => obj.analyzeInterval s dur sigs l) sigs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
