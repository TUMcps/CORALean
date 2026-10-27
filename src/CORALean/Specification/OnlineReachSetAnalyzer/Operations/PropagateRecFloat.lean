module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.PropagateFloat
public import CORALean.Specification.OnlineReachSetAnalyzer.OnlineReachSetAnalyzer

@[expose] public section

/-!
# The recursion of the propagation, over a float scalar

`propagateRec(makeValid,idx)` with time stamps in `𝕋`: the recursion of `propagateRec`, each node
propagated by `OnlineAnalyzerNode.propagateFloat`. `fuel` bounds the recursion; running out of it
is `none`, as is every throw.

## Inputs
* `eps` – machine epsilon
* `makeValid` – interval to make final

## Output
* the nodes and propagated flags after the recursion, or none
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {S : ℕ → Type} {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `propagateRec(makeValid,idx)` on the nodes and the `propagated` flags. -/
def OnlineReachSetAnalyzer.propagateRecFloat (eps : 𝕋) (makeValid : STLInterval 𝕋) :
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
        (fun st c => OnlineReachSetAnalyzer.propagateRecFloat eps makeValid fuel c st)
        (nodes, propagated)).bind fun st =>
        -- ... and now the node at idx: node.propagate(obj.nodes(node.children),makeValid)
        (st.1[idx - 1]?).bind fun node =>
          (node.children.mapM fun c => st.1[c - 1]?).bind fun childNodes =>
            (node.propagateFloat eps childNodes makeValid).map fun r =>
              -- the node and its children, and obj.propagated(idx) = true
              ((node.children.zip r.2).foldl (fun ns p => ns.set (p.1 - 1) p.2)
                (st.1.set (idx - 1) r.1), st.2.set (idx - 1) true)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
