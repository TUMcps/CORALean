module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.Basic
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Mk
public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Basic
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Basic
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ParseNew
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.FormulaKey
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.FormulaKind

@[expose] public section

/-!
# Parsing a formula into the syntax DAG

`parse(phi,parent)`, the helper of the constructor: a subformula already seen (its key is in
`cache`) becomes one more child of its `parent` and its node one more parent of the node of
`phi`; a new subformula gets a node at the next index (the child of its `parent`, unless it is
the root, whose `parent` is `0`), is entered into the cache, and its operands are parsed with
this node as their parent. CORA throws if an index is out of range or a node cannot be made;
here `none`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] [Float.ExactLe 𝕋]
  [TimeOrder 𝕋]
    {S : ℕ → Type} {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- `parse(phi,parent)`. Noncomputable: the cache lookup compares formulas classically, as the
time scalar `𝕋` has no decidable equality. -/
noncomputable def OnlineReachSetAnalyzer.parse (dropPropagated : Bool) :
    OnlineReachSetAnalyzer.Formula 𝕋 (AtomicProposition S d) → ℕ →
      OnlineReachSetAnalyzer.ParseState 𝕋 S d → Option (OnlineReachSetAnalyzer.ParseState 𝕋 S d)
  | φ, parent, st =>
    -- check cache
    match st.cache.find? (fun p => decide (p.1 = φ.key)) with
    | some (_, c) =>
      -- obj.nodes(cache(k)).addParent(parent); obj.nodes(parent).addChild(cache(k))
      (OnlineReachSetAnalyzer.updateNode st.nodes c (fun n => some (n.addParent parent))).bind
        fun nodes =>
          (OnlineReachSetAnalyzer.updateNode nodes parent (fun n => some (n.addChild c))).map
            fun nodes => { st with nodes := nodes }
    | none =>
      -- no node for phi --> create one and store in cache
      (OnlineReachSetAnalyzer.parseNew dropPropagated φ parent st).bind fun st' =>
        let myPos := st.nodes.length + 1
        -- parse the operands, with the new node as their parent
        match φ with
        | .not a => OnlineReachSetAnalyzer.parse dropPropagated a myPos st'
        | .and a b =>
          (OnlineReachSetAnalyzer.parse dropPropagated a myPos st').bind
            (OnlineReachSetAnalyzer.parse dropPropagated b myPos)
        | .or a b =>
          (OnlineReachSetAnalyzer.parse dropPropagated a myPos st').bind
            (OnlineReachSetAnalyzer.parse dropPropagated b myPos)
        | .until _ a b =>
          (OnlineReachSetAnalyzer.parse dropPropagated a myPos st').bind
            (OnlineReachSetAnalyzer.parse dropPropagated b myPos)
        | _ => some st'
end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
