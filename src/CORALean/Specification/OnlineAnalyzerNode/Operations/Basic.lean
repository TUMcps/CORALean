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
noncomputable def OnlineAnalyzerNode.initSignal (k : OnlineAnalyzerNode.Kind) :
    FourValuedSignal ℝ :=
  FourValuedSignal.uniformSignal k.initValue


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
