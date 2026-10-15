module

public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeTree

@[expose] public section

/-!
# `analyzeTreeCora`: CORA's `analyze` as printed

CORA's `specification/reachSetAnalyzer.m`, `analyze` (l. 76-82), analyzes the branches below a node
with

```
for j=1:length(c)-1
    out = [out copy(obj).analyze(R,c(j))];
end
% use the current copy for last child
out = [out obj.analyze(R,c(1))];
```

The comment says the last child `c(end)` is analyzed on `obj` itself, after the first
`length(c)-1` on copies; the code analyzes `c(1)` instead. The loop covers `c(1),…,c(end-1)`, and
`c(1)` follows once more, so with `length(c) ≥ 2` the child `c(end)` and everything below it is
never analyzed, and the branch of `c(1)` is in the result twice. This is the recursion of
`ReachSetAnalyzer.analyzeTree` with that one index changed.

# The second branch of a fork is lost

A reach set `R(1)` (parent `0`) with two successors `R(2)` and `R(3)` (parent `1`) has the branches
`[1,2]` and `[1,3]`. With the state "the entries analyzed so far", CORA's recursion returns
`[[1,2],[1,2]]` and the one here `[[1,2],[1,3]]`: entry `3` is never analyzed. As `reachSet`
arrays with forks come from `reach` of hybrid automata with several outgoing transitions or from
splitting, `priv_modelCheckingSignals` and `verifySTL_seidl` then check the formula on one
branch only, and may report `true` for a reach set one of whose branches violates it. Read from
the source and transcribed literally to Python, which gives `[[1, 2], [1, 2]]`, not run in MATLAB.
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The fork of the reach sets with parents `0`, `1`, `1`: the root has the child `1`, and `1` has
the children `2` and `3`. -/
def ReachSetAnalyzer.aux_forkChildren : ℕ → List ℕ
  | 0 => [1]
  | 1 => [2, 3]
  | _ => []

/-- The state is the list of entries analyzed so far. -/
def ReachSetAnalyzer.aux_visit (o : List ℕ) (j : ℕ) : Option (List ℕ) := some (o ++ [j])


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.analyzeTreeCora_counterexample :
    ReachSetAnalyzer.analyzeTreeCora ReachSetAnalyzer.aux_forkChildren
        ReachSetAnalyzer.aux_visit some 4 0 [] = some [[1, 2], [1, 2]] ∧
      ReachSetAnalyzer.analyzeTree ReachSetAnalyzer.aux_forkChildren
        ReachSetAnalyzer.aux_visit some 4 0 [] = some [[1, 2], [1, 3]] := by
  constructor <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
