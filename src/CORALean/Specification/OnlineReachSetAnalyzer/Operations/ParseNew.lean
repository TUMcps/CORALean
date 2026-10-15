module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.Basic
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Mk
public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Basic
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Basic
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.FormulaKey
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.FormulaKind

@[expose] public section

/-!
# A new subformula

The part of `parse(phi,parent)` for a subformula without node: the next index `myPos` is its,
it becomes a child of its `parent` (unless it is the root, whose `parent` is `0`), its node is
made and entered into the cache. CORA throws if an index is out of range or the node cannot be
made; here `none`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No node for phi --> create one and store in cache. -/
noncomputable def OnlineReachSetAnalyzer.parseNew (dropPropagated : Bool)
    (φ : OnlineReachSetAnalyzer.Formula (AtomicProposition S d)) (parent : ℕ)
    (st : OnlineReachSetAnalyzer.ParseState S d) :
    Option (OnlineReachSetAnalyzer.ParseState S d) :=
  let myPos := st.nodes.length + 1
  -- need this check for the first iteration where we pass in 0 as parent
  (if parent ≠ 0 then
    OnlineReachSetAnalyzer.updateNode st.nodes parent (fun n => some (n.addChild myPos))
    else some st.nodes).bind fun nodes =>
  -- obj.nodes(myPos) = onlineAnalyzerNode(phi.type,myPos,parent,dropPropagated,...)
  (OnlineAnalyzerNode.mk? φ.kind myPos [parent] dropPropagated φ.interval? φ.ap?).map fun node =>
    { nodes := nodes ++ [node], cache := (φ.key, myPos) :: st.cache }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
