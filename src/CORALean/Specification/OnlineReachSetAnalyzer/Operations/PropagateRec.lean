module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.Propagate
public import CORALean.Specification.OnlineReachSetAnalyzer.OnlineReachSetAnalyzer

@[expose] public section

/-!
# The recursion of the propagation

`propagateRec(makeValid,idx)`: node `idx` is propagated after its not yet propagated children
(`setdiff(node.children,find(obj.propagated))`, ascending, without repeats); a child an earlier
sibling's recursion already propagated is propagated again. Then `node.propagate` updates the node
and its children (handles in CORA, written back here) and `obj.propagated(idx)` is set. The syntax
graph is acyclic, so `fuel` of the node count loses nothing; running out of it is `none`, as is
every throw. `eps` is MATLAB's `eps`.
Real-only, a specification: it reads real time stamps exactly; its rounded refinement is
the recursion of `OnlineReachSetAnalyzer.propagateFloat`.

## Inputs
* `eps` – machine epsilon
* `makeValid` – interval to make final

## Output
* the nodes and propagated flags after the recursion, or none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `propagateRec(makeValid,idx)` on the nodes and the `propagated` flags. -/
noncomputable def OnlineReachSetAnalyzer.propagateRec (eps : ℝ) (makeValid : STLInterval ℝ) :
    ℕ → ℕ → List (OnlineAnalyzerNode ℝ (AtomicProposition S d)) × List Bool →
      Option (List (OnlineAnalyzerNode ℝ (AtomicProposition S d)) × List Bool)
  | 0, _, _ => none
  | fuel + 1, idx, (nodes, propagated) =>
    (nodes[idx - 1]?).bind fun node =>
      -- setdiff(node.children',find(obj.propagated))
      let todo := (node.children.filter fun c => ¬ (propagated[c - 1]? = some true)).eraseDups
        |>.mergeSort (fun a b => decide (a ≤ b))
      -- first propagate the children (if they were not yet propagated) ...
      (todo.foldlM (fun st c => OnlineReachSetAnalyzer.propagateRec eps makeValid fuel c st)
        (nodes, propagated)).bind fun st =>
        -- ... and now the node at idx: node.propagate(obj.nodes(node.children),makeValid)
        (st.1[idx - 1]?).bind fun node =>
          (node.children.mapM fun c => st.1[c - 1]?).bind fun childNodes =>
            (node.propagate eps childNodes makeValid).map fun r =>
              -- the node and its children, and obj.propagated(idx) = true
              ((node.children.zip r.2).foldl (fun ns p => ns.set (p.1 - 1) p.2)
                (st.1.set (idx - 1) r.1), st.2.set (idx - 1) true)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
