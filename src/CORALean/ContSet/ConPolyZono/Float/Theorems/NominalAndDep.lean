import CORALean.ContSet.ConPolyZono.Float.Operations.And
import CORALean.ContSet.ConPolyZono.Float.Operations.AndA
import CORALean.ContSet.ConPolyZono.Float.Operations.AndB
import CORALean.ContSet.ConPolyZono.Float.Operations.AndDep
import CORALean.ContSet.ConPolyZono.Real.Operations.AndDep
import CORALean.ContSet.ConPolyZono.Float.Theorems.AndD
import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalAndB
import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatAndA
import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE

/-!
# `andDep`'s nominal part is the exact layer's, at the tolerance `andD`

The whole record, field by field, on the two blocks `toRealMat_andA` and
`nominal_andB` already pin.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.nominal_andDep (C₁ C₂ : ConPolyZono 𝕋 n) :
    nominal (C₁.andDep C₂)
      = Real.ConPolyZono.andDep (nominal C₁) (nominal C₂) (ConPolyZono.andD C₁ C₂) := by
  have hG : (fun (l : Fin (C₁.h + C₂.h)) (i : Fin n) =>
        toReal (Fin.append (C₁.G i) (fun _ => zero) l))
      = Fin.append (fun (l : Fin C₁.h) (i : Fin n) => toReal (C₁.G i l))
        (0 : Fin C₂.h → Vec ℝ n) := by
    refine funext (Fin.addCases (fun l => ?_) fun j => ?_) <;> funext i <;>
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, toReal_zero]
  have hGI : (fun (j : Fin 0) (_ : Fin n) => toReal ((Fin.elim0 : Fin 0 → 𝕋) j))
      = (Fin.elim0 : Fin 0 → Vec ℝ n) := funext fun j => j.elim0
  -- the exact layer's record spelled out, so the field rewrites above have a term to match
  have hreal : Real.ConPolyZono.andDep (nominal C₁) (nominal C₂)
        (ConPolyZono.andD C₁ C₂)
      = (⟨C₁.p + C₂.p, C₁.h + C₂.h, 0, C₁.m + C₂.m + n, C₁.s + C₂.s + (C₁.h + C₂.h),
        toRealVec C₁.c,
        Fin.append (fun (l : Fin C₁.h) (i : Fin n) => toReal (C₁.G i l))
          (0 : Fin C₂.h → Vec ℝ n),
        Real.PolyZonotope.plusE C₁.E C₂.E, (Fin.elim0 : Fin 0 → Vec ℝ n),
        Real.ConPolyZono.andA (nominal C₁) (nominal C₂),
        Real.ConPolyZono.andB (nominal C₁) (nominal C₂) (ConPolyZono.andD C₁ C₂),
        Real.ConPolyZono.appendE (Real.PolyZonotope.plusE C₁.EC C₂.EC)
          (Real.PolyZonotope.plusE C₁.E C₂.E)⟩ : Real.ConPolyZono (Vec ℝ n)) := rfl
  rw [hreal]
  -- and the float side in the same shape, so the two records differ only field by field
  show (⟨C₁.p + C₂.p, C₁.h + C₂.h, 0, C₁.m + C₂.m + n, C₁.s + C₂.s + (C₁.h + C₂.h),
      toRealVec C₁.c,
      fun l i => toReal (Fin.append (C₁.G i) (fun _ => zero) l),
      Real.PolyZonotope.plusE C₁.E C₂.E,
      fun j _ => toReal ((Fin.elim0 : Fin 0 → 𝕋) j),
      toRealMat (ConPolyZono.andA C₁ C₂), (ConPolyZono.andB C₁ C₂).nominal,
      Real.ConPolyZono.appendE (Real.PolyZonotope.plusE C₁.EC C₂.EC)
        (Real.PolyZonotope.plusE C₁.E C₂.E)⟩ : Real.ConPolyZono (Vec ℝ n)) = _
  rw [hG, hGI, ConPolyZono.toRealMat_andA, ConPolyZono.nominal_andB]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
