module

public import CORALean.ContSet.ZonoBundle.Float.Operations.IntervalSupportFunc
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# CORA's box of a float bundle contains the support-function box

By construction: each end of the support-function box is the tighter of CORA's end and the
certified support bound, `maximum` and `minimum` being exact, so it is never larger than CORA's
box of the members' boxes, whatever the linear program returned.

## Inputs
* `zB` – float zonotope bundle

## Hypotheses
* `hk` – the bundle has a member

## Conclusion
* the support-function box is contained in the plain box
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The intersection of the members' boxes contains the support-function box. -/
theorem ZonoBundle.intervalAll_contains_intervalSupportFunc (zB : ZonoBundle (Vec 𝕋 n))
    (hk : 0 < zB.k) :
    (zB.intervalSupportFunc hk).construct ⊆ (zB.intervalAll hk).construct := by -- --- PROOF ---
  intro x hx
  refine Interval.mem_vec_iff.mpr fun i => ?_
  have h := Interval.mem_vec_iff.mp hx i
  simp only [ZonoBundle.intervalSupportFunc, toReal_maximum, toReal_minimum] at h
  exact ⟨(le_max_left _ _).trans h.1, h.2.trans (min_le_left _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
