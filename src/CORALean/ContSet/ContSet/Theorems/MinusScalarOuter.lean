module

public import CORALean.ContSet.ContSet.Operations.MinusScalar

@[expose] public section

/-!
# `minusScalar` encloses the translate
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContSetLike Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] [Neg 𝕋] [NegScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSetLike (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [ExactScalar 𝕋] [Mtimes (Mat 𝕋) S] in
/-- Every `x - p`, `x` in `S` and `p` read as reals, is in `minusScalar S p`: `plus_outer`, the
point `-p` reading as `-toRealVec p`. -/
theorem ContSet.minusScalar_outer (s : S n) (p : Vec 𝕋 n) : -- --- CONCL ---
    (fun x => x - toRealVec p) '' toSet s ⊆
      toSet (ContSet.minusScalar s p) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  have hneg : toRealVec (-p) = -toRealVec p := by
    funext i
    rw [toRealVec_apply, Pi.neg_apply, Pi.neg_apply, toRealVec_apply, NegScalar.toReal_neg]
  refine Plus.plus_outer _ _ ⟨x, hx, toRealVec (-p), OfScalarPoint.mem_ofVec _, ?_⟩
  show x + toRealVec (-p) = x - toRealVec p
  rw [hneg, sub_eq_add_neg]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
