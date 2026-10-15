module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Theorems.Basic
public import CORALean.Specification.FourValued.Theorems.Basic

@[expose] public section

/-!
# Negation negates the value at every time

`(~obj).at(t)` is `~obj.at(t)` for every valid four-valued signal and every time.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.at_not {T : Type} [LinearOrder T] [Zero T] (s : FourValuedSignal T)
    (hs : s.IsValid) (t : T) : s.not.at t = (s.at t).not := by
  simp only [FourValuedSignal.at, FourValuedSignal.not, KleeneSignal.at_not _ hs.1]
  split_ifs
  · rfl
  · exact FourValued.fromKleene_not _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
