module

public import CORALean.Specification.ReachSetAnalyzer.ReachSetAnalyzer

@[expose] public section

/-!
# The recursion of `analyze` over the branches

`out = analyze(obj,R,i)`: analyze the entry `R(i)` (the root `i = 0` has none), find the children
`c` of the node, and if there is none the result is the signals; otherwise every child branch is
analyzed on a copy of `obj`, and the results are concatenated. The state `σ` is what the entries are
analyzed into (the analyzer), `α` what a leaf yields (its signals). CORA recurses without bound;
a parent relation without cycles (every parent index below its child's) is finished after
`length(R)+1` levels, so `fuel` of that size loses nothing, and exhausting it is `none`, as is
a failing `analyzeSingle` or `signals` (CORA throws).

## Inputs
* `σ` – analyzer state type
* `α` – result type
* `children` – children of each entry
* `analyzeSingle` – analysis of one entry
* `signals` – result extracted from a state

## Output
* the results of every branch below the entry, or none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `out = analyze(obj,R,i)`, with `children R`, `analyzeSingle obj j = obj.analyzeSingle(R(j))`
and `signals`. -/
def ReachSetAnalyzer.analyzeTree {σ α : Type} (children : ℕ → List ℕ)
    (analyzeSingle : σ → ℕ → Option σ) (signals : σ → Option α) :
    ℕ → ℕ → σ → Option (List α)
  | 0, _, _ => none
  | fuel + 1, i, obj =>
    -- if nargin > 2, obj.analyzeSingle(R(i))
    (if i ≠ 0 then analyzeSingle obj i else some obj).bind fun obj =>
      -- find all children of the current node
      let c := children i
      if c = [] then (signals obj).map fun s => [s]
      else
        -- analyze the child branches, each on its own copy of obj
        (c.mapM fun j => ReachSetAnalyzer.analyzeTree children analyzeSingle signals fuel j obj).map
          List.flatten

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
