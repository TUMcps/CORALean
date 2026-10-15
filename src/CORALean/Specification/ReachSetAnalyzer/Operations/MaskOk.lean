module

public import CORALean.Specification.FiniteSignal.Operations.Max
public import CORALean.Specification.ReachSetAnalyzer.ReachSetAnalyzer
public import Mathlib.Algebra.Ring.BooleanRing

@[expose] public section

/-!
# Does the mask let a proposition through

`~isKey(obj.masks,k) || max(obj.masks(k),int)` of `analyzeTimeInterval`: a proposition without a
mask matters always, one with a mask only where the mask is true somewhere in `int =
interval(lo,hi)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `~isKey(obj.masks,k) || max(obj.masks(k),int)`. -/
noncomputable def ReachSetAnalyzer.maskOk (obj : ReachSetAnalyzer S n) (k : String)
    (lo hi : ℝ) : Bool :=
  match obj.masks.lookup k with
  | none => true
  | some mask => FiniteSignal.max mask lo hi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
