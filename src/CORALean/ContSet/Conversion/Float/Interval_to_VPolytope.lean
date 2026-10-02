import CORALean.ContSet.VPolytope.Float.VPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope

/-!
# A box as its corners, over a floating-point scalar

The one place a float layer does nothing at all: a corner is a stored bound
copied, so the error box stays at zero and the nominal vertex list is exactly the
exact layer's corners of the nominal box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def Interval.vPolytope (I : Interval (Vec 𝕋 n)) : VPolytope 𝕋 n where
  k := 2 ^ n
  V := fun i l => if signEquiv n l i then I.sup i else I.inf i
  E := ⟨fun _ => zero, fun _ => zero⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.vPolytope_contains (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ (Interval.vPolytope I).construct := by -- --- PROOF ---
  intro x hx
  have hnom : x ∈ InflatedContSet.nominalSet (Interval.vPolytope I) := by
    -- reading a stored bound commutes with choosing which one to read
    have hV : (fun (l : Fin (2 ^ n)) (i : Fin n) =>
          toReal (if signEquiv n l i then I.sup i else I.inf i))
        = fun (l : Fin (2 ^ n)) => Real.Interval.corner I.nominal (signEquiv n l) := by
      funext l i
      exact apply_ite toReal _ _ _
    show x ∈ Real.VPolytope.construct
      ⟨2 ^ n, fun l i => toReal (if signEquiv n l i then I.sup i else I.inf i)⟩
    rw [hV]
    exact Real.Interval.vPolytope_contains I.nominal hx
  refine ⟨x, hnom, 0, fun i => ?_, ?_⟩
  · show toReal (zero : 𝕋) ≤ (0 : Vec ℝ n) i ∧ (0 : Vec ℝ n) i ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_refl 0, le_refl 0⟩
  · show x + 0 = x
    rw [add_zero]

/-- The corner list's convex hull is no larger than the box, for a nonempty one: the error box is
the point `0`, and the nominal corners are the exact layer's, whose hull
`Real.Interval.vPolytope_exact` shows to be the box. -/
theorem Interval.contains_vPolytope (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, toReal (I.inf i) ≤ toReal (I.sup i)) :
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

/-- Exact for a nonempty box: `vPolytope_contains` and `contains_vPolytope`. -/
theorem Interval.vPolytope_exact (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, toReal (I.inf i) ≤ toReal (I.sup i)) :
    (Interval.vPolytope I).construct = I.construct :=
  Set.Subset.antisymm (Interval.contains_vPolytope I hI) (Interval.vPolytope_contains I)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
