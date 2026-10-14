module

public import CORALean.ContSet.ContSet.Operations.ProjectHighDim
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# `projectHighDim_` encloses the zero-padded set

For an injective `proj`, `I(:, proj) x` is `x` placed at the coordinates `proj` and `0` elsewhere,
so `mtimes_outer` gives the padded points. CORA does not check injectivity; a repeated target
adds the two coordinates instead, and the padding map is no longer the statement.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.projectHighDim_outer (s : S n) (N : ℕ) {proj : Fin n → Fin N}
    (hp : Function.Injective proj) :
    (fun x : Vec ℝ n => Function.extend proj x (0 : Vec ℝ N)) '' construct s ⊆
      construct (ContSet.projectHighDim_ (𝕋 := 𝕋) s N proj) := by -- --- PROOF ---
  -- the padded point is the selection matrix applied to `x`, so `mtimes_outer` covers it
  rintro _ ⟨x, hx, rfl⟩
  refine Mtimes.mtimes_outer (𝕄 := Mat 𝕋) _ s ?_
  simp only [ContSet.construct_mat, Set.biUnion_singleton, Set.mem_image]
  refine ⟨x, hx, ?_⟩
  funext i
  -- the selection matrix reads back as the real indicator matrix
  have hE : ∀ j, toRealMat (Matrix.of fun i j => if proj j = i then (1 : 𝕋) else 0 : Mat 𝕋 N n) i j
      = if proj j = i then 1 else 0 := by
    intro j
    rw [toRealMat_apply]
    simp only [Matrix.of_apply]
    split_ifs
    · exact ExactScalar.toReal_one
    · exact ExactScalar.toReal_zero
  simp only [Matrix.mulVec, dotProduct, hE, ite_mul, one_mul, zero_mul]
  -- coordinate `i` is either the image of one `j₀`, or outside the range and `0`
  by_cases hi : ∃ j, proj j = i
  · obtain ⟨j₀, rfl⟩ := hi
    rw [hp.extend_apply, Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      simp [hp.ne hj]
    · simp
  · rw [Function.extend_apply' _ _ _ hi]
    refine (Finset.sum_eq_zero fun j _ => ?_)
    have : proj j ≠ i := fun h => hi ⟨j, h⟩
    simp [this]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
