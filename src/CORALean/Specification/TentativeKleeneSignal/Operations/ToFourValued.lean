module

public import CORALean.Specification.FourValuedSignal.FourValuedSignal
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Combine
public import CORALean.Specification.TentativeKleeneSignal.TentativeKleeneSignal
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# A tentative signal as a four-valued one

`toFourValued(obj)` of `tentativeKleeneSignal.m` (a private method): the conjunction of the two
parts is the unknown part, the negation of their disjunction the inconclusive part, the Kleene
signal is `canBeTrue` with the unknown part.

## Inputs
* `T` – time type
* `s` – tentative signal

## Output
* the four-valued signal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = toFourValued(obj)`. -/
def TentativeKleeneSignal.toFourValued {T : Type} [LinearOrder T] [Zero T]
    (s : TentativeKleeneSignal T) : FourValuedSignal T :=
  -- 1. unk = obj.canBeTrue & obj.canBeFalse
  let unk := PointSegmentSignal.combine (fun (a : Fin 2 → Bool) (_ : Unit) =>
    (a 0 && a 1)) ![s.canBeTrue, s.canBeFalse] ()
  -- 2. kleeneSig = kleeneSignal(obj.canBeTrue,unk)
  let kleeneSig : KleeneSignal T := ⟨s.canBeTrue, unk⟩
  -- 3. inc = ~(obj.canBeTrue | obj.canBeFalse)
  let inc := (PointSegmentSignal.combine (fun (a : Fin 2 → Bool) (_ : Unit) =>
    (a 0 || a 1)) ![s.canBeTrue, s.canBeFalse] ()).not
  -- 4. sig = fourValuedSignal(kleeneSig,inc)
  ⟨kleeneSig, inc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
