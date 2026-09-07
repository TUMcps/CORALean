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

def Interval.vPolytope (I : Interval 𝕋 n) : VPolytope 𝕋 n where
  k := 2 ^ n
  V := fun i l => if signEquiv n l i then I.sup i else I.inf i
  E := ⟨fun _ => zero, fun _ => zero⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.vPolytope_contains (I : Interval 𝕋 n) :
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
