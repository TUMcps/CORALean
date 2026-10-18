module

public import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplaneIntervalFloat
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# `projectOnHyperplaneIntervalFloat` encloses the projection onto every allowed hyperplane

For any normal `c` in the box and offset `δ` in `[δ̲, δ̄]`, `x − (cᵀx − δ) c = (I − c cᵀ) x + δ c`:
the real projector lies in the bracketed interval matrix entrywise, `cᵢcⱼ` being between the
corner products of the boxes of `cᵢ` and `cⱼ`, and `δ c` in its box, so `mtimes_outer`,
`ofInterval_outer` and `plus_outer` carry it into the result. Outer only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float FloatOps SoundFloatArithmetic Pointwise
open scoped CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ[𝕋] S]
variable [OfInterval S 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.projectOnHyperplaneIntervalFloat_outer (s : S n) (c : Interval (Vec 𝕋 n))
    (dLo dHi : 𝕋) {cr : Vec ℝ n} (hc : cr ∈ c.construct) {δ : ℝ} (hδ : toReal dLo ≤ δ)
    (hδ' : δ ≤ toReal dHi) : -- --- STMT ---
    (fun x : Vec ℝ n => x - (cr ⬝ᵥ x - δ) • cr) '' construct s ⊆
      construct (ContSet.projectOnHyperplaneIntervalFloat s c dLo dHi) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  have hci : ∀ i, toReal (c.inf i) ≤ cr i ∧ cr i ≤ toReal (c.sup i) := hc
  refine Plus.plus_outer _ _ ⟨(1 - Matrix.vecMulVec cr cr).mulVec x, ?_,
    δ • cr, OfInterval.ofInterval_outer _ ?_, ?_⟩
  · -- the projected point is the real projector's image of `x`
    refine Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) _ s ?_
    refine Set.mem_iUnion₂.mpr ⟨1 - Matrix.vecMulVec cr cr, ?_, x, hx, rfl⟩
    -- the real projector lies between the bracketing entries
    rintro ⟨i, j⟩
    have hc1 : toReal (if i = j then (one : 𝕋) else zero) = if i = j then 1 else 0 := by
      split_ifs <;> simp [toReal_one, toReal_zero]
    have hm := Interval.mul_between_corners (hci i).1 (hci i).2 (hci j).1 (hci j).2
    have h₁ := subDown_le_sub (if i = j then (one : 𝕋) else zero)
      (Interval.mulHi (c.inf i) (c.sup i) (c.inf j) (c.sup j))
    have h₂ := sub_le_subUp (if i = j then (one : 𝕋) else zero)
      (Interval.mulLo (c.inf i) (c.sup i) (c.inf j) (c.sup j))
    rw [hc1] at h₁ h₂
    show toReal (subDown (if i = j then (one : 𝕋) else zero)
        (Interval.mulHi (c.inf i) (c.sup i) (c.inf j) (c.sup j)))
        ≤ (1 - Matrix.vecMulVec cr cr) i j ∧
      (1 - Matrix.vecMulVec cr cr) i j
        ≤ toReal (subUp (if i = j then (one : 𝕋) else zero)
          (Interval.mulLo (c.inf i) (c.sup i) (c.inf j) (c.sup j)))
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
    refine ⟨?_, ?_⟩ <;> split_ifs at h₁ h₂ ⊢ <;> linarith [hm.1, hm.2]
  · -- `δ c` lies between the bracketing products
    intro i
    exact Interval.mul_between_corners hδ hδ' (hci i).1 (hci i).2
  · -- the two points sum to the foot of the perpendicular
    funext i
    simp [Matrix.sub_mulVec, Matrix.mulVec, dotProduct, Matrix.vecMulVec, Finset.mul_sum,
      sub_smul, mul_comm, mul_left_comm]
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
