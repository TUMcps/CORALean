import CORALean.ContSet.Zonotope.Float.Operations.CubMap
import CORALean.ContSet.Zonotope.Float.Theorems.CubMapDepCoeff
import CORALean.ContSet.Zonotope.Float.Theorems.DependentOuter

/-!
# `Zonotope.cubMap` over-approximates the cubic map, over a floating-point scalar

Every point of the operand, box included, is a point of the nominal set of `dependent`
(`dependent_outer`), whose cubic image is held by `cubMapDep` (`cubMapDep_coeff`). Outer only: the
monomials `β_k β_j β_c` of the factors are tied to each other, and a zonotope frees them.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cubMap_outer (T : Fin m → Fin n → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) :
    Real.PolyZonotope.cubEval (fun i k => toRealMat (T i k)) '' Z.construct
      ⊆ (Z.cubMap T).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨p, hp, hxp⟩ := Zonotope.mem_nominalSet_iff.mp (Zonotope.dependent_outer Z hx)
  obtain ⟨γ, hγ, -, e, he, heq⟩ := Zonotope.cubMapDep_coeff T Z.dependent p hp
  refine ⟨_, Zonotope.mem_nominalSet_iff.mpr ⟨γ, hγ, fun _ => rfl⟩, e, he, ?_⟩
  have hx' : x = toRealVec Z.dependent.c + ∑ j, p j • toRealVec (Z.dependent.G j) := by
    funext i
    simp [hxp i, Finset.sum_apply, mul_comm, toRealVec]
  rw [hx', heq]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
