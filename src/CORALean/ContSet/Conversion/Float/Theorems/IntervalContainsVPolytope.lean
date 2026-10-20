module

public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalContainsVPolytope
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeContainsVPolytope

@[expose] public section

/-!
# A box as its corners, over a floating-point scalar

## Inputs
* `I` – interval

## Hypotheses
* `hI` – lower end below upper end per coordinate

## Conclusion
* corner polytope is contained in the interval
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The corner list's convex hull is no larger than the box, for a nonempty one: the error box is
the point `0`, and the nominal corners are the exact layer's, whose hull
`Real.Interval.vPolytope_exact` shows to be the box. -/
theorem Interval.contains_vPolytope (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, toReal (I.inf i) ≤ toReal (I.sup i)) : -- --- CONCL ---
    (Interval.vPolytope I).construct ⊆ I.construct := by -- --- PROOF ---
  rintro y ⟨x, hx, e, he, rfl⟩
  have hV : (fun (l : Fin (2 ^ n)) (i : Fin n) =>
        toReal (if signEquiv n l i then I.sup i else I.inf i))
      = fun (l : Fin (2 ^ n)) => Real.Interval.corner I.nominal (signEquiv n l) := by
    funext l i
    exact apply_ite toReal _ _ _
  have hx' : x ∈ Real.VPolytope.construct
      ⟨2 ^ n, fun l i => toReal (if signEquiv n l i then I.sup i else I.inf i)⟩ := hx
  rw [hV] at hx'
  have hxI : x ∈ I.construct := Real.Interval.contains_vPolytope I.nominal hI hx'
  have he0 : e = 0 := by
    funext i
    have h : toReal (zero : 𝕋) ≤ e i ∧ e i ≤ toReal (zero : 𝕋) := he i
    rw [toReal_zero] at h
    exact le_antisymm h.2 h.1
  subst he0
  simpa using hxI

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
