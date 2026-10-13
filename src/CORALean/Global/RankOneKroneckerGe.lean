module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-!
# The rank of `I ⊗ M`

`rank (I_k ⊗ M) ≥ k · rank M`, the one direction the rank condition of the descriptor observer
needs (it is an equality). The range of `I ⊗ M` contains one copy of the range of `M` for
each of the `k` blocks, independent of one another: `y ↦ ((i, a) ↦ (y i) a)` is an injective
linear map of `k` copies of the range into it, as each `y i = M u_i` is read off the block
vector `(i, b) ↦ u_i b`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Kronecker

variable {ι m n : Type} [Fintype ι] [DecidableEq ι] [Fintype n]


-- =======================================  MAIN THEOREM  ======================================= --

theorem rank_one_kronecker_ge (M : Matrix m n ℝ) :
    Fintype.card ι * M.rank ≤ ((1 : Matrix ι ι ℝ) ⊗ₖ M).rank := by -- --- PROOF ---
  set S : Submodule ℝ (m → ℝ) := LinearMap.range M.mulVecLin with hS
  -- `k` copies of the range of `M`, read into the range of `I ⊗ M` block by block
  let g : (ι → S) →ₗ[ℝ] (ι × m → ℝ) :=
    { toFun := fun y p => (y p.1 : m → ℝ) p.2
      map_add' := fun y y' => rfl
      map_smul' := fun c y => rfl }
  have hginj : Function.Injective g := by
    intro y y' h
    funext i
    refine Subtype.ext (funext fun a => ?_)
    exact congrFun h (i, a)
  have hrange : LinearMap.range g ≤ LinearMap.range ((1 : Matrix ι ι ℝ) ⊗ₖ M).mulVecLin := by
    rintro _ ⟨y, rfl⟩
    -- each block `y i = M uᵢ`
    choose u hu using fun i => (y i).2
    refine ⟨fun p => u p.1 p.2, ?_⟩
    funext ⟨i, a⟩
    have := congrFun (hu i) a
    simp only [mulVecLin_apply] at this
    simp only [mulVecLin_apply, mulVec, dotProduct, g, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← this, ← Finset.univ_product_univ, Finset.sum_product]
    simp only [kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq]
    rfl
  calc Fintype.card ι * M.rank = Module.finrank ℝ (ι → S) := by
        rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
        rfl
    _ = Module.finrank ℝ (LinearMap.range g) := (LinearMap.finrank_range_of_inj hginj).symm
    _ ≤ ((1 : Matrix ι ι ℝ) ⊗ₖ M).rank := Submodule.finrank_mono hrange

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
