module

public import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplaneFloat

@[expose] public section

/-!
# `projectOnHyperplaneFloat` encloses the orthogonal projection

For the normal `c` and offset `d` the floats read as, `(I - c cᵀ) x + d c = x - (c ⬝ x - d) c`, the
foot of the perpendicular from `x`: the real projector lies in the bracketed interval matrix
entrywise and `d c` in its box, so `mtimes_outer`, `ofInterval_outer` and `plus_outer` carry it into
the result. Outer only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float FloatOps SoundFloatArithmetic Pointwise
open scoped CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ[𝕋] S]
variable [OfInterval S 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.projectOnHyperplaneFloat_outer (s : S n) (c : Vec 𝕋 n) (d : 𝕋) :
    (fun x : Vec ℝ n => x - (toRealVec c ⬝ᵥ x - toReal d) • toRealVec c) '' construct s ⊆
      construct (ContSet.projectOnHyperplaneFloat s c d) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  refine Plus.plus_outer _ _ ⟨(1 - Matrix.vecMulVec (toRealVec c) (toRealVec c)).mulVec x, ?_,
    toReal d • toRealVec c, OfInterval.ofInterval_outer _ ?_, ?_⟩
  · -- the projected point is the real projector's image of `x`, a point of the interval matrix's
    -- image
    refine Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) _ s ?_
    refine Set.mem_iUnion₂.mpr ⟨1 - Matrix.vecMulVec (toRealVec c) (toRealVec c), ?_, x, hx, rfl⟩
    -- the real projector lies between the bracketing entries
    rintro ⟨i, j⟩
    have hc : toReal (if i = j then (one : 𝕋) else zero) = if i = j then 1 else 0 := by
      split_ifs <;> simp [toReal_one, toReal_zero]
    have h₁ := subDown_le_sub (if i = j then (one : 𝕋) else zero) (mulUp (c i) (c j))
    have h₂ := sub_le_subUp (if i = j then (one : 𝕋) else zero) (mulDown (c i) (c j))
    have h₃ := mul_le_mulUp (c i) (c j)
    have h₄ := mulDown_le_mul (c i) (c j)
    rw [hc] at h₁ h₂
    show toReal (subDown (if i = j then (one : 𝕋) else zero) (mulUp (c i) (c j)))
        ≤ (1 - Matrix.vecMulVec (toRealVec c) (toRealVec c)) i j ∧
      (1 - Matrix.vecMulVec (toRealVec c) (toRealVec c)) i j
        ≤ toReal (subUp (if i = j then (one : 𝕋) else zero) (mulDown (c i) (c j)))
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, toRealVec]
    refine ⟨?_, ?_⟩ <;> split_ifs at h₁ h₂ ⊢ <;> linarith
  · -- `d c` lies between the bracketing products
    intro i
    exact ⟨mulDown_le_mul d (c i), mul_le_mulUp d (c i)⟩
  · -- the two points sum to the foot of the perpendicular
    funext i
    simp [Matrix.sub_mulVec, Matrix.mulVec, dotProduct, Matrix.vecMulVec, Finset.mul_sum,
      sub_smul, mul_comm, mul_left_comm]
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
