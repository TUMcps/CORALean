import CORALean.ContSet.Interval.Float.Theorems.PowerOuter
import CORALean.ContSet.Interval.Float.Theorems.Prod1Outer
import CORALean.ContSet.PolyZonotope.Float.Operations.MonoBox
import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `monoBox` encloses every monomial

At every factor vector of the box, each monomial lies in its interval: the power of each factor
lies in the power's interval (`Interval.power_outer`) and the product of those in the product's
(`Interval.prod₁_outer`).
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.monoBox_outer {p h : ℕ} (E : Fin p → Fin h → ℕ) (X : Interval (Vec 𝕋 p))
    {a : Vec ℝ p} (ha : a ∈ X.construct) :
    (fun l => Real.PolyZonotope.monomial E a l) ∈
      (PolyZonotope.monoBox E X).construct := by -- --- PROOF ---
  rw [PolyZonotope.monoBox, Interval.materialise_eq]
  refine Interval.prod₁_outer _ ⟨fun k l => a k ^ E k l, fun q => ?_, rfl⟩
  -- each entry is the power of one factor, inside that power's interval
  have h := Interval.power_outer (⟨fun _ => X.inf q.1, fun _ => X.sup q.1⟩ : Interval (Vec 𝕋 1))
    (E q.1 q.2) ⟨fun _ => a q.1, fun _ => ⟨(ha q.1).1, (ha q.1).2⟩, rfl⟩ 0
  exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
