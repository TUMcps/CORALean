module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.FormulaKind
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode

@[expose] public section

/-!
# The node of a subformula in the syntax DAG

`n` is the node of `φ` when every node `c` is labelled with the formula `ψ c`: its kind, the
interval of an until and the proposition of an atom are those of `φ`, and its children are the
nodes of the operands of `φ`, in order. This is the syntax tree of [1, Alg. 1], shared where a
subformula repeats.

## Inputs
* `ψ` – formula of each node index

## Output
* `n` is the node of `φ` in the DAG labelled by `ψ`

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def OnlineReachSetAnalyzer.IsNodeOf (ψ : ℕ → OnlineReachSetAnalyzer.Formula ℝ A) :
    OnlineReachSetAnalyzer.Formula ℝ A → OnlineAnalyzerNode ℝ A → Prop
  | .tt, n => n.kind = .true ∧ n.children = []
  | .ff, n => n.kind = .false ∧ n.children = []
  | .ap _ a, n => n.kind = .ap ∧ n.children = [] ∧ n.ap = some a
  | .not φ, n => n.kind = .not ∧ ∃ c, n.children = [c] ∧ ψ c = φ
  | .and φ φ', n => n.kind = .and ∧ ∃ c c', n.children = [c, c'] ∧ ψ c = φ ∧ ψ c' = φ'
  | .or φ φ', n => n.kind = .or ∧ ∃ c c', n.children = [c, c'] ∧ ψ c = φ ∧ ψ c' = φ'
  | .until I φ φ', n => n.kind = .until ∧ n.interval = some I ∧
      ∃ c c', n.children = [c, c'] ∧ ψ c = φ ∧ ψ c' = φ'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
