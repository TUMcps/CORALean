module

public import CORALean.ContSet.Conversion.Float.Theorems.CapsuleIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalHPolytopeExact
public import CORALean.ContSet.Conversion.Float.Operations.Capsule_to_HPolytope
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.SubsetOfBounds

@[expose] public section

/-!
# A capsule lies in its halfspace polytope, over a floating-point scalar

At `n ≤ 1` the box, which encloses the capsule (`Capsule.interval_contains`) and which its rows
describe exactly; otherwise every row is bounded by `Capsule.boundDotUp`, for whatever basis the
floats produced.

## Inputs
* `p` – Newton steps per row length
* `C` – capsule

## Hypotheses
* none

## Conclusion
* capsule is contained in its halfspace polytope
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.hPolytope_contains (p : ℕ) (C : Capsule 𝕋 n) : -- --- CONCL ---
    C.construct ⊆ (C.hPolytope p).construct := by -- --- PROOF ---
  -- the box, at `n ≤ 1`
  have hbox : C.construct ⊆ C.interval.hPolytope.construct :=
    subset_trans C.interval_contains (Interval.hPolytope_exact _).symm.subset
  cases n with
  | zero => exact hbox
  | succ m =>
    show C.construct ⊆ (if m = 0 then _ else _ : HPolytope 𝕋 (Vec 𝕋 (m + 1))).construct
    split_ifs
    · exact hbox
    · exact HPolytope.subset_ofBounds _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
