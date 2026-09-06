import CORALean.ContSet.VPolytope.Real.Theorems.LinCombOuter
import CORALean.ContSet.VPolytope.Real.Theorems.MtimesExact
import CORALean.ContSet.VPolytope.Real.Theorems.MtimesMatPolytopeOuter
import CORALean.ContSet.VPolytope.Real.Theorems.PlusExact

/-!
# What `VPolytope` instantiates

`reduce` is the identity: there is no order to reduce to, and dropping a vertex
shrinks the set, which is not what `reduce` may return.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance {α : Type} [AddCommGroup α] [Module ℝ α] : ContSet (VPolytope α) α :=
  ⟨VPolytope.construct⟩

instance : Plus (VPolytope (Vec ℝ n)) (Vec ℝ n) where
  plus := VPolytope.plus
  plus_outer P₁ P₂ := (VPolytope.plus_exact P₁ P₂).subset

instance : LinComb (VPolytope (Vec ℝ n)) (Vec ℝ n) where
  linComb := VPolytope.linComb
  linComb_outer := VPolytope.linComb_outer

instance : Reduce (VPolytope (Vec ℝ n)) (Vec ℝ n) where
  reduce P _ := P
  reduce_outer _ _ := subset_rfl

instance : Mtimes (Mat ℝ) (fun n => VPolytope (Vec ℝ n)) where
  mtimes := VPolytope.mtimes
  mtimes_outer M P := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (VPolytope.mtimes_exact M P).subset

/-- The matrix-polytope family. A generic theorem quantifies over `𝕄 : ℕ → ℕ → Type`
and the elaborator cannot read that family off one member, so a use site has to
name it: `(𝕄 := 𝕄𝒫)`. -/
scoped notation "𝕄𝒫" => fun m n => VPolytope (Mat ℝ m n)

noncomputable instance : Mtimes 𝕄𝒫 (fun n => VPolytope (Vec ℝ n)) where
  mtimes := VPolytope.mtimesMatPolytope
  mtimes_outer M P := VPolytope.mtimesMatPolytope_outer M P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
