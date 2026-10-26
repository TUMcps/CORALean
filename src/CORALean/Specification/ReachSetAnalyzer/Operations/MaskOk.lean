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

Generic over the time type: at a float scalar it compares its time stamps exactly
(`TimeOrder`), so the result read as reals is that of the analyzer read as reals
(`ReachSetAnalyzer.maskOk_mapTime`).

## Inputs
* `obj` – analyzer
* `k` – proposition key
* `lo` – interval lower bound
* `hi` – interval upper bound

## Output
* whether the mask lets the proposition through
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [TimeOrder T] [Zero T] {S : ℕ → Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `~isKey(obj.masks,k) || max(obj.masks(k),int)`. -/
def ReachSetAnalyzer.maskOk (obj : ReachSetAnalyzer T S n) (k : String)
    (lo hi : T) : Bool :=
  match obj.masks.lookup k with
  | none => true
  | some mask => FiniteSignal.max mask lo hi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
