module

public import CORALean.ContSet.HPolytope.Float.Operations.NormalizeConstraints
public import CORALean.ContSet.HPolytope.Float.Theorems.AbsorbRoundingOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.ErrFreeOfIsErrFree
public import CORALean.ContSet.HPolytope.Float.Theorems.ScaleRowsOuter

@[expose] public section

/-!
# The float `normalizeConstraints` keeps every point of the polytope in the domain

The inequality divisors are positive (`recipUp_pos`), so `scaleRows_outer` applies, to the
polytope itself when its box is certified empty (`errFree_of_isErrFree`), and otherwise to the
polytope with its error box folded into its rows (`absorbRounding_outer`): every point of the
polytope that lies in the domain meets the normalized rows. Outer over the domain, as
`reduceOverDomain_outer` is; the exact layer's `normalizeConstraints_exact` says the real operation
is the same set.

## Inputs
* `a` – scalar

## Hypotheses
* none

## Conclusion
* `recipUp` is positive: `1 / a` rounded up for a certified positive `a`, and `1` otherwise
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

/-- `recipUp` is positive: `1 / a` rounded up for a certified positive `a`, and `1` otherwise. -/
private theorem HPolytope.recipUp_pos (a : 𝕋) : -- --- CONCL ---
    0 < toReal (HPolytope.recipUp a) := by -- --- PROOF ---
  by_cases h : ltStrict zero a = true
  · simp only [HPolytope.recipUp, h, if_true]
    have hpos := toReal_lt_of_ltStrict h
    rw [toReal_zero] at hpos
    refine lt_of_lt_of_le ?_ (div_le_divUp _ _ hpos)
    rw [toReal_one]
    exact one_div_pos.mpr hpos
  · simp only [HPolytope.recipUp, h, if_false, Bool.false_eq_true]
    rw [toReal_one]
    exact one_pos


theorem HPolytope.normalizeConstraints_outer (P : HPolytope 𝕋 (Vec 𝕋 n))
    (dom : Interval (Vec 𝕋 n)) :
    P.construct ∩ dom.construct ⊆ (P.normalizeConstraints dom).construct ∩ dom.construct :=
  fun _ hx => HPolytope.scaleRows_outer (if P.isErrFree then P else P.absorbRounding)
    (by split <;> rename_i h
        exacts [HPolytope.errFree_of_isErrFree h, HPolytope.errFree_of_origin rfl rfl rfl]) _ _
    (fun _ => HPolytope.recipUp_pos _) dom
    ⟨by split
        exacts [hx.1, HPolytope.absorbRounding_outer P hx.1], hx.2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
