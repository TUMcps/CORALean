module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.PropagateFloat
public import CORALean.Specification.OnlineReachSetAnalyzer.OnlineReachSetAnalyzer

@[expose] public section

/-!
# Propagating the observations, over a float scalar

`propagate(obj,makeValid)` with time stamps in `𝕋`: reset `obj.propagated` and propagate from the
root, node `1`, by the recursion of `propagateRec` with each node propagated by
`OnlineAnalyzerNode.propagateFloat` (`propagateFloat_toRealNode` says what a step does). `fuel`
bounds the recursion; running out of it is `none`, as is every throw.

## Inputs
* `eps` – machine epsilon
* `obj` – analyzer
* `makeValid` – interval to make final

## Output
* the analyzer after propagating from the root, or none
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {S : ℕ → Type} {d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `propagateRec(makeValid,idx)` on the nodes and the `propagated` flags. -/
def OnlineReachSetAnalyzer.aux_propagateRecFloat (eps : 𝕋) (makeValid : STLInterval 𝕋) :
    ℕ → ℕ → List (OnlineAnalyzerNode 𝕋 (AtomicProposition S d)) × List Bool →
      Option (List (OnlineAnalyzerNode 𝕋 (AtomicProposition S d)) × List Bool)
  | 0, _, _ => none
  | fuel + 1, idx, (nodes, propagated) =>
    (nodes[idx - 1]?).bind fun node =>
      -- setdiff(node.children',find(obj.propagated))
      let todo := (node.children.filter fun c => ¬ (propagated[c - 1]? = some true)).eraseDups
        |>.mergeSort (fun a b => decide (a ≤ b))
      -- first propagate the children (if they were not yet propagated) ...
      (todo.foldlM
        (fun st c => OnlineReachSetAnalyzer.aux_propagateRecFloat eps makeValid fuel c st)
        (nodes, propagated)).bind fun st =>
        -- ... and now the node at idx: node.propagate(obj.nodes(node.children),makeValid)
        (st.1[idx - 1]?).bind fun node =>
          (node.children.mapM fun c => st.1[c - 1]?).bind fun childNodes =>
            (node.propagateFloat eps childNodes makeValid).map fun r =>
              -- the node and its children, and obj.propagated(idx) = true
              ((node.children.zip r.2).foldl (fun ns p => ns.set (p.1 - 1) p.2)
                (st.1.set (idx - 1) r.1), st.2.set (idx - 1) true)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `propagate(obj,makeValid)`. -/
def OnlineReachSetAnalyzer.propagateFloat (eps : 𝕋) (obj : OnlineReachSetAnalyzer 𝕋 S d)
    (makeValid : STLInterval 𝕋) : Option (OnlineReachSetAnalyzer 𝕋 S d) :=
  -- obj.propagated = false(1,length(obj.nodes)); obj.propagateRec(makeValid,1)
  (OnlineReachSetAnalyzer.aux_propagateRecFloat eps makeValid (obj.nodes.length + 1) 1
    (obj.nodes, List.replicate obj.nodes.length false)).map fun st =>
      { obj with nodes := st.1, propagated := st.2 }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
