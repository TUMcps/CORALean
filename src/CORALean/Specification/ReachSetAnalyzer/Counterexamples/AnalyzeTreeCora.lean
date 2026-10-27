module

public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeTree
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `analyzeTreeCora`: CORA's `analyze` as printed

CORA's `specification/reachSetAnalyzer.m`, `analyze` (l. 76-82), runs `copy(obj).analyze(R,c(j))`
for `j=1:length(c)-1` and then, under the comment "use the current copy for last child",
`obj.analyze(R,c(1))`. The comment means `c(end)`; the code analyzes `c(1)` again, so for
`length(c) ≥ 2` the last child and everything below it is never analyzed and the branch of `c(1)`
appears twice. This is `ReachSetAnalyzer.analyzeTree` with that one index changed.

# The second branch of a fork is lost

A reach set `R(1)` (parent `0`) with successors `R(2)` and `R(3)` has the branches `[1,2]` and
`[1,3]`. CORA's recursion returns `[[1,2],[1,2]]`, the one here `[[1,2],[1,3]]`: entry `3` is never
analyzed, so `priv_modelCheckingSignals` and `verifySTL_seidl` check one branch only and may report
`true` for a reach set one of whose branches violates the formula. Read from the source and
transcribed to Python, not run in MATLAB.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's analysis skips the last child and repeats the first
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's recursion as printed, kept only to be refuted.
/-- `out = analyze(obj,R,i)` as printed: `c(1)` is analyzed again where `c(end)` is meant. -/
def ReachSetAnalyzer.analyzeTreeCora {σ α : Type} (children : ℕ → List ℕ)
    (analyzeSingle : σ → ℕ → Option σ) (signals : σ → Option α) :
    ℕ → ℕ → σ → Option (List α)
  | 0, _, _ => none
  | fuel + 1, i, obj =>
    (if i ≠ 0 then analyzeSingle obj i else some obj).bind fun obj =>
      let c := children i
      if c = [] then (signals obj).map fun s => [s]
      else
        -- for j=1:length(c)-1, out = [out copy(obj).analyze(R,c(j))]
        (c.dropLast.mapM fun j =>
          ReachSetAnalyzer.analyzeTreeCora children analyzeSingle signals fuel j obj).bind
            fun outs =>
          -- out = [out obj.analyze(R,c(1))]
          (ReachSetAnalyzer.analyzeTreeCora children analyzeSingle signals fuel (c.headD 0)
            obj).map fun last => outs.flatten ++ last


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The fork of the reach sets with parents `0`, `1`, `1`: the root has the child `1`, and `1` has
the children `2` and `3`. -/
@[step_of ReachSetAnalyzer.analyzeTreeCora_counterexample]
def ReachSetAnalyzer.step_forkChildren : ℕ → List ℕ
  | 0 => [1]
  | 1 => [2, 3]
  | _ => []

/-- The state is the list of entries analyzed so far. -/
@[step_of ReachSetAnalyzer.analyzeTreeCora_counterexample]
def ReachSetAnalyzer.step_visit (o : List ℕ) (j : ℕ) : Option (List ℕ) := some (o ++ [j])


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.analyzeTreeCora_counterexample : -- --- CONCL ---
    ReachSetAnalyzer.analyzeTreeCora ReachSetAnalyzer.step_forkChildren
        ReachSetAnalyzer.step_visit some 4 0 [] = some [[1, 2], [1, 2]] ∧
      ReachSetAnalyzer.analyzeTree ReachSetAnalyzer.step_forkChildren
        ReachSetAnalyzer.step_visit some 4 0 [] = some [[1, 2], [1, 3]] := by -- --- PROOF ---
  constructor <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
