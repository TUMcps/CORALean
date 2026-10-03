import CORALean.HybridDynamics.Operations.LinearResetLift
import Mathlib.Data.Matrix.Mul

/-!
# `LinearReset.lift` restricted to the bound coordinates is the old reset

For an injective `stateBind`, the lifted affine reset at coordinate `stateBind j` is the old reset
at `j` of the bound state: the exactness statement for CORA's `lift`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearReset.lift_bind (W : Mat 𝕋 n n) (w : Vec 𝕋 n) (stateBind : Fin n → Fin N)
    (hinj : Function.Injective stateBind) (id : Bool) (x : Vec ℝ N) (j : Fin n) :
    (toRealMat (LinearReset.lift W w N stateBind id).1 *ᵥ x +
        toRealVec (LinearReset.lift W w N stateBind id).2) (stateBind j) =
      (toRealMat W *ᵥ (fun k => x (stateBind k)) + toRealVec w) j := by -- --- PROOF ---
  -- the source of a bound coordinate is its own index, since `stateBind` is injective
  have hsrc : ∀ l : Fin n, (List.finRange n).find? (fun j => stateBind j = stateBind l)
      = some l := by
    intro l
    rcases h : (List.finRange n).find? (fun j => stateBind j = stateBind l) with _ | l'
    · exact absurd (List.find?_eq_none.1 h l (List.mem_finRange l)) (by simp)
    · have h2 := List.find?_some h
      rw [hinj (of_decide_eq_true h2)]
  -- off the range of `stateBind` there is no source
  have hnone : ∀ k : Fin N, k ∉ Set.range stateBind →
      (List.finRange n).find? (fun j => stateBind j = k) = none := by
    intro k hk
    exact List.find?_eq_none.2 fun l _ => by simpa using fun h => hk ⟨l, h⟩
  simp only [Pi.add_apply, mulVec, dotProduct, toRealMat_apply, toRealVec_apply,
    LinearReset.lift, of_apply, hsrc]
  congr 1
  -- the sum over `Fin N` is the sum over the injective image of `Fin n`
  symm
  refine Fintype.sum_of_injective stateBind hinj _ _ ?_ ?_
  · intro k hk
    simp [hnone k hk, ExactScalar.toReal_zero]
  · intro l
    simp [hsrc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
