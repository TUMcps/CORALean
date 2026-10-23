module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode

@[expose] public section

/-!
# `OnlineAnalyzerNode/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {A : Type}


-- ==============================  `OnlineAnalyzerNode.addChild`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `addChild(obj,child)`: registers a new child in the graph structure. -/
def OnlineAnalyzerNode.addChild (n : OnlineAnalyzerNode 𝕋 A) (child : ℕ) : OnlineAnalyzerNode 𝕋 A :=
  { n with children := n.children ++ [child] }


-- ==============================  `OnlineAnalyzerNode.addParent`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `addParent(obj,parent)`: registers a new parent, with nothing propagated to it yet. -/
def OnlineAnalyzerNode.addParent (n : OnlineAnalyzerNode 𝕋 A) (parent : ℕ) :
    OnlineAnalyzerNode 𝕋 A :=
  { n with parents := n.parents ++ [parent], prop := n.prop ++ [STLInterval.empty] }


-- ===========================  `OnlineAnalyzerNode.Kind.initValue`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aux_initSignal(type)`: the value a node's signal starts with. -/
def OnlineAnalyzerNode.Kind.initValue : OnlineAnalyzerNode.Kind → FourValued
  | .true => .tt
  | .false => .ff
  | _ => .ii


-- =============================  `OnlineAnalyzerNode.initSignal`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `aux_initSignal(type)`: the constant signal a node starts with. -/
def OnlineAnalyzerNode.initSignal [TimeOrder 𝕋] (k : OnlineAnalyzerNode.Kind) :
    FourValuedSignal 𝕋 :=
  FourValuedSignal.uniformSignal k.initValue


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
