import CORALean.ContSet.ConPolyZono.Float.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE

/-!
# `dependent`'s record reads back to the exact layer's `dependent`

Only two fields need an argument, and both are the transpose: generators are
stored as a matrix here and as a family of vectors there, so concatenating the
two blocks and then reading them back is `Fin.append` of the two read-back
blocks, coordinate by coordinate rather than by definition.
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

theorem ConPolyZono.nominal_dependent (C : ConPolyZono 𝕋 n) :
    nominal C.dependent = (nominal C).dependent := by -- --- PROOF ---
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
