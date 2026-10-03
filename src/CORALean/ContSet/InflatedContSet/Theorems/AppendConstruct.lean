import CORALean.ContSet.InflatedContSet.InflatedContSet
import CORALean.ContSet.Interval.Float.Theorems.AppendConstruct
import CORALean.Global.AppendProdAdd

/-!
# A product of inflated sets

If the nominal part of a stored set is the pair of two others' nominal parts read through
`Fin.append`, and its error box is the two boxes side by side (`Interval.append`), then the set
itself is the pair of their sets read through `Fin.append`. Set addition is coordinatewise, so a
product of sums is a sum of products. Every Cartesian product of float representations discharges
its exactness through this.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.InflatedContSet

open Pointwise

variable {𝕋 S₁ S₂ T N₁ N₂ N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}
variable [ContSet N₁ (Vec ℝ n₁)] [ContSet N₂ (Vec ℝ n₂)] [ContSet N (Vec ℝ (n₁ + n₂))]
variable [InflatedContSet S₁ N₁ 𝕋 n₁] [InflatedContSet S₂ N₂ 𝕋 n₂]
  [InflatedContSet T N 𝕋 (n₁ + n₂)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem append_construct {s₁ : S₁} {s₂ : S₂} {t : T}
    (hnominal : nominalSet t = (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
      (nominalSet s₁ ×ˢ nominalSet s₂))
    (herror : error t = Interval.append (error s₁) (error s₂)) :
    construct t = (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
      (construct s₁ ×ˢ construct s₂) := by
  show nominalSet t + (error t).construct = _ '' ((nominalSet s₁ + (error s₁).construct) ×ˢ
    (nominalSet s₂ + (error s₂).construct))
  rw [hnominal, herror, Interval.append_construct, append_image_prod_add]

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
