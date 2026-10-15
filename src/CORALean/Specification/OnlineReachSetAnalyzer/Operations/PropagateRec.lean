module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.Propagate
public import CORALean.Specification.OnlineReachSetAnalyzer.OnlineReachSetAnalyzer

@[expose] public section

/-!
# The recursion of the propagation

`propagateRec(makeValid,idx)`: the node `idx` is propagated after its children that are not yet
propagated, found when the node is entered: `setdiff(node.children,find(obj.propagated))`, the
indices in ascending order without repeats. A child that an earlier sibling's recursion already
propagated is propagated again. Then `node.propagate(obj.nodes(node.children),makeValid)` updates
the node and its children (handle objects in CORA; written back here, a child listed twice
by the last copy), and `obj.propagated(idx)` is set. The syntax graph has no cycles, so the
recursion depth is at most the number of nodes; `fuel` of that size loses nothing and running out
of it is `none`, as is every throw. `eps` is MATLAB's `eps`.
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
noncomputable def OnlineReachSetAnalyzer.propagateRec (eps : ℝ) (makeValid : STLInterval) :
    ℕ → ℕ → List (OnlineAnalyzerNode (AtomicProposition S d)) × List Bool →
      Option (List (OnlineAnalyzerNode (AtomicProposition S d)) × List Bool)
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
