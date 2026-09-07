import CORALean.ContSet.ConPolyZono.Float.Operations.Intersection
import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionA
import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionB
import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionDep
import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionDep
import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionD
import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalIntersectionB
import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatIntersectionA
import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE

/-!
# `intersectionDep`'s nominal part is the exact layer's, at the tolerance `intersectionD`

The whole record, field by field, on the two blocks `toRealMat_intersectionA` and
`nominal_intersectionB` already pin.
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

theorem ConPolyZono.nominal_intersectionDep (cPZ₁ cPZ₂ : ConPolyZono 𝕋 n) :
    nominal (cPZ₁.intersectionDep cPZ₂)
      = Real.ConPolyZono.intersectionDep (nominal cPZ₁) (nominal cPZ₂)
        (ConPolyZono.intersectionD cPZ₁ cPZ₂) := by -- --- PROOF ---
  have hG : (fun (l : Fin (cPZ₁.h + cPZ₂.h)) (i : Fin n) =>
        toReal (Fin.append (cPZ₁.G i) (fun _ => zero) l))
      = Fin.append (fun (l : Fin cPZ₁.h) (i : Fin n) => toReal (cPZ₁.G i l))
        (0 : Fin cPZ₂.h → Vec ℝ n) := by
    refine funext (Fin.addCases (fun l => ?_) fun j => ?_) <;> funext i <;>
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, toReal_zero]
  have hGI : (fun (j : Fin 0) (_ : Fin n) => toReal ((Fin.elim0 : Fin 0 → 𝕋) j))
      = (Fin.elim0 : Fin 0 → Vec ℝ n) := funext fun j => j.elim0
  -- the exact layer's record spelled out, so the field rewrites above have a term to match
  have hreal : Real.ConPolyZono.intersectionDep (nominal cPZ₁) (nominal cPZ₂)
        (ConPolyZono.intersectionD cPZ₁ cPZ₂)
      = (⟨cPZ₁.p + cPZ₂.p, cPZ₁.h + cPZ₂.h, 0, cPZ₁.m + cPZ₂.m + n,
        cPZ₁.s + cPZ₂.s + (cPZ₁.h + cPZ₂.h),
        toRealVec cPZ₁.c,
        Fin.append (fun (l : Fin cPZ₁.h) (i : Fin n) => toReal (cPZ₁.G i l))
          (0 : Fin cPZ₂.h → Vec ℝ n),
        Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E, (Fin.elim0 : Fin 0 → Vec ℝ n),
        Real.ConPolyZono.intersectionA (nominal cPZ₁) (nominal cPZ₂),
        Real.ConPolyZono.intersectionB (nominal cPZ₁) (nominal cPZ₂)
          (ConPolyZono.intersectionD cPZ₁ cPZ₂),
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
      toRealMat (ConPolyZono.intersectionA cPZ₁ cPZ₂),
      (ConPolyZono.intersectionB cPZ₁ cPZ₂).nominal,
      Real.ConPolyZono.appendE (Real.PolyZonotope.plusE cPZ₁.EC cPZ₂.EC)
        (Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E)⟩ : Real.ConPolyZono (Vec ℝ n)) = _
  rw [hG, hGI, ConPolyZono.toRealMat_intersectionA, ConPolyZono.nominal_intersectionB]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
