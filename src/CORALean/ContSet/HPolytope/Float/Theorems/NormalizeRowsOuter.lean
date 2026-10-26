module

public import CORALean.ContSet.HPolytope.Float.Operations.NormalizeRows
public import CORALean.ContSet.HPolytope.Float.Theorems.AbsorbRoundingOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.ErrFreeOfIsErrFree
public import CORALean.ContSet.HPolytope.Float.Theorems.ScaleRowsOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.RowScalePos

@[expose] public section

/-!
# The float `normalizeRows` keeps every point of the polytope in the domain

The inequality divisors are positive (`rowScale_pos`), so `scaleRows_outer` applies to the
polytope itself when its box is certified empty (`errFree_of_isErrFree`), and otherwise to the
polytope with its error box folded into its rows (`absorbRounding_outer`): every point of the
polytope that lies in the domain meets the normalized rows. Outer over the domain,
as `reduceOverDomain_outer` is; the exact layer's `normalizeRows_exact` says the real operation
is the same set.

## Inputs
* `p` – natural number
* `P` – H-polytope
* `dom` – domain interval

## Hypotheses
* none

## Conclusion
* the float `normalizeRows` keeps every point of the polytope in the domain
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.normalizeRows_outer (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n))
    (dom : Interval (Vec 𝕋 n)) :
    P.construct ∩ dom.construct ⊆ (P.normalizeRows p dom).construct ∩ dom.construct :=
  fun _ hx => HPolytope.scaleRows_outer (if P.isErrFree then P else P.absorbRounding)
    (by split <;> rename_i h
        exacts [HPolytope.errFree_of_isErrFree h, HPolytope.isErrFree_of_origin rfl rfl rfl]) _ _
    (HPolytope.rowScale_pos p _) dom
    ⟨by split
        exacts [hx.1, HPolytope.absorbRounding_outer P hx.1], hx.2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
