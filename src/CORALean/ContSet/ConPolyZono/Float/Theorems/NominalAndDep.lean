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

theorem ConPolyZono.nominal_andDep (cPZ₁ cPZ₂ : ConPolyZono 𝕋 n) :
    nominal (cPZ₁.andDep cPZ₂)
      = Real.ConPolyZono.andDep (nominal cPZ₁) (nominal cPZ₂)
        (ConPolyZono.andD cPZ₁ cPZ₂) := by -- --- PROOF ---
  have hG : (fun (l : Fin (cPZ₁.h + cPZ₂.h)) (i : Fin n) =>
        toReal (Fin.append (cPZ₁.G i) (fun _ => zero) l))
      = Fin.append (fun (l : Fin cPZ₁.h) (i : Fin n) => toReal (cPZ₁.G i l))
        (0 : Fin cPZ₂.h → Vec ℝ n) := by
    refine funext (Fin.addCases (fun l => ?_) fun j => ?_) <;> funext i <;>
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, toReal_zero]
  have hGI : (fun (j : Fin 0) (_ : Fin n) => toReal ((Fin.elim0 : Fin 0 → 𝕋) j))
      = (Fin.elim0 : Fin 0 → Vec ℝ n) := funext fun j => j.elim0
  -- the exact layer's record spelled out, so the field rewrites above have a term to match
  have hreal : Real.ConPolyZono.andDep (nominal cPZ₁) (nominal cPZ₂)
        (ConPolyZono.andD cPZ₁ cPZ₂)
      = (⟨cPZ₁.p + cPZ₂.p, cPZ₁.h + cPZ₂.h, 0, cPZ₁.m + cPZ₂.m + n,
        cPZ₁.s + cPZ₂.s + (cPZ₁.h + cPZ₂.h),
        toRealVec cPZ₁.c,
        Fin.append (fun (l : Fin cPZ₁.h) (i : Fin n) => toReal (cPZ₁.G i l))
          (0 : Fin cPZ₂.h → Vec ℝ n),
        Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E, (Fin.elim0 : Fin 0 → Vec ℝ n),
        Real.ConPolyZono.andA (nominal cPZ₁) (nominal cPZ₂),
        Real.ConPolyZono.andB (nominal cPZ₁) (nominal cPZ₂) (ConPolyZono.andD cPZ₁ cPZ₂),
        Real.ConPolyZono.appendE (Real.PolyZonotope.plusE cPZ₁.EC cPZ₂.EC)
          (Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E)⟩ : Real.ConPolyZono (Vec ℝ n)) := rfl
  rw [hreal]
  -- and the float side in the same shape, so the two records differ only field by field
  show (⟨cPZ₁.p + cPZ₂.p, cPZ₁.h + cPZ₂.h, 0, cPZ₁.m + cPZ₂.m + n,
      cPZ₁.s + cPZ₂.s + (cPZ₁.h + cPZ₂.h),
      toRealVec cPZ₁.c,
      fun l i => toReal (Fin.append (cPZ₁.G i) (fun _ => zero) l),
      Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E,
      fun j _ => toReal ((Fin.elim0 : Fin 0 → 𝕋) j),
      toRealMat (ConPolyZono.andA cPZ₁ cPZ₂), (ConPolyZono.andB cPZ₁ cPZ₂).nominal,
      Real.ConPolyZono.appendE (Real.PolyZonotope.plusE cPZ₁.EC cPZ₂.EC)
        (Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E)⟩ : Real.ConPolyZono (Vec ℝ n)) = _
  rw [hG, hGI, ConPolyZono.toRealMat_andA, ConPolyZono.nominal_andB]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
