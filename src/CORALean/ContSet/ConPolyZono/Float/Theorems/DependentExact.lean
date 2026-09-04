import CORALean.ContSet.ConPolyZono.Float.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE

/-!
# Making the independent generators dependent loses nothing here either

The float operation rounds nothing, so its whole content is that the stored
floats read back to the exact layer's `dependent` of the read-back floats —
`nominal_dependent` — after which the exact layer's `dependent_exact` says the
rest and the error box is the same box.

Only two fields need an argument, and both are the transpose: generators are
stored as a matrix here and as a family of vectors there, so concatenating the
two blocks and then reading them back is `Fin.append` of the two read-back
blocks, coordinate by coordinate rather than by definition.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem ConPolyZono.nominal_dependent (C : ConPolyZono 𝕋 n) :
    nominal C.dependent = (nominal C).dependent := by
  have hG : (fun (l : Fin (C.h + C.q)) (i : Fin n) =>
        toReal (Fin.append (C.G i) (C.GI i) l))
      = Fin.append (fun (l : Fin C.h) (i : Fin n) => toReal (C.G i l))
        (fun (j : Fin C.q) (i : Fin n) => toReal (C.GI i j)) := by
    refine funext (Fin.addCases (fun l => ?_) fun j => ?_) <;> funext i <;>
      simp only [Fin.append_left, Fin.append_right]
  have hGI : (fun (j : Fin 0) (_ : Fin n) => toReal ((Fin.elim0 : Fin 0 → 𝕋) j))
      = (Fin.elim0 : Fin 0 → Vec ℝ n) := funext fun j => j.elim0
  -- the two records side by side, so only the two rewritten generator blocks differ
  show (⟨C.p + C.q, C.h + C.q, 0, C.m, C.s, toRealVec C.c,
      fun l i => toReal (Fin.append (C.G i) (C.GI i) l),
      Real.PolyZonotope.plusE C.E (Real.PolyZonotope.identE C.q),
      fun j _ => toReal ((Fin.elim0 : Fin 0 → 𝕋) j),
      toRealMat C.A, C.b.nominal, Real.ConPolyZono.padE C.EC C.q⟩ :
    Real.ConPolyZono (Vec ℝ n)) = _
  rw [hG, hGI]
  rfl

theorem ConPolyZono.nominalSet_dependent (C : ConPolyZono 𝕋 n) :
    nominalSet C.dependent = nominalSet C := by
  show Real.ConPolyZono.construct (nominal C.dependent)
    = Real.ConPolyZono.construct (nominal C)
  rw [ConPolyZono.nominal_dependent, ← Real.ConPolyZono.dependent_exact]

theorem ConPolyZono.dependent_exact (C : ConPolyZono 𝕋 n) :
    C.construct = C.dependent.construct := by
  show nominalSet C + (error C).construct
    = nominalSet C.dependent + (error C.dependent).construct
  rw [ConPolyZono.nominalSet_dependent]
  rfl

end CORALean.Float
