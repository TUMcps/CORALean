module

public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.VPolytope.Real.Interfaces
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Operations.ConstructPoint
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Theorems.Convex
public import CORALean.ContSet.VPolytope.Real.Theorems.IntersectionOuter
public import CORALean.ContSet.VPolytope.Real.Theorems.LinCombOuter
public import CORALean.ContSet.VPolytope.Real.Theorems.MapExact
public import CORALean.ContSet.VPolytope.Real.Theorems.MtimesExact
public import CORALean.ContSet.VPolytope.Real.Theorems.MtimesMatPolytopeOuter
public import CORALean.ContSet.VPolytope.Real.Theorems.PlusExact

@[expose] public section

/-!
# What `VPolytope` instantiates

`reduce` is the identity: there is no order to reduce to, and dropping a vertex shrinks the set,
which `reduce` may not do. No `Recenter`: there is no center to pick at `k = 0`, where `construct`
is `∅` and no choice of one can put `0` inside the recentered polytope either.
`VPolytope.intersectionInstance` fixes two direction families for a whole run, as
`Ellipsoid.plusInstance` fixes its scalings: a `def`, not an `instance`, since choosing the
directions is a precision decision search must not make.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}

/-- The vertex-polytope family over vectors: pins `(S := 𝒱𝒫)`. -/
scoped notation "𝒱𝒫" => fun n => VPolytope (Vec ℝ n)


-- ========================================  INSTANCES  ========================================= --

instance {α : Type} [AddCommGroup α] [Module ℝ α] : ContSet (VPolytope α) α :=
  ⟨VPolytope.construct⟩

/-- A vertex polytope is its own vertices. -/
instance {α : Type} [AddCommGroup α] [Module ℝ α] : ExactVertices (VPolytope α) α :=
  ⟨id, fun _ => rfl⟩

instance {α : Type} [AddCommGroup α] [Module ℝ α] : ConvexSet (VPolytope α) α :=
  ⟨VPolytope.convex_construct⟩

instance {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] : CompactSet (VPolytope α) α :=
  ⟨VPolytope.isCompact_construct⟩

instance {α : Type} [AddCommGroup α] [Module ℝ α] : OfPoint (VPolytope α) α where
  ofPoint := VPolytope.point
  mem_ofPoint v := by
    show v ∈ (VPolytope.point v).construct
    rw [VPolytope.construct_point]; exact rfl

instance : Plus (VPolytope (Vec ℝ n)) (Vec ℝ n) where
  plus := VPolytope.plus
  plus_outer P₁ P₂ := (VPolytope.plus_exact P₁ P₂).subset

/-- `Intersection` at two direction families the caller fixes for a whole run, exactly
as `Ellipsoid.plusInstance` fixes its scalings. A `def`, not an `instance`:
choosing the directions is a precision decision instance search may not make. -/
@[reducible] noncomputable def VPolytope.intersectionInstance {q₁ q₂ : ℕ}
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    Intersection (VPolytope (Vec ℝ n)) (Vec ℝ n) where
  intersection P₁ P₂ := VPolytope.intersection P₁ P₂ Aq₁ Aq₂
  intersection_outer P₁ P₂ := VPolytope.intersection_outer P₁ P₂ Aq₁ Aq₂

instance : LinComb (VPolytope (Vec ℝ n)) (Vec ℝ n) where
  linComb := VPolytope.linComb
  linComb_outer := VPolytope.linComb_outer

instance : Reduce (VPolytope (Vec ℝ n)) (Vec ℝ n) where
  reduce P _ := P
  reduce_outer _ _ := subset_rfl

instance : Mtimes (Mat ℝ) (𝒱𝒫) where
  mtimes := VPolytope.mtimes
  mtimes_outer M P := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (VPolytope.mtimes_exact M P).subset

/-- The matrix-polytope family. A generic theorem quantifies over `𝕄 : ℕ → ℕ → Type`
and the elaborator cannot read that family off one member, so a use site has to
name it: `(𝕄 := 𝕄𝒫)`. -/
scoped notation "𝕄𝒫" => fun m n => VPolytope (Mat ℝ m n)

noncomputable instance : Mtimes 𝕄𝒫 (𝒱𝒫) where
  mtimes := VPolytope.mtimesMatPolytope
  mtimes_outer M P := VPolytope.mtimesMatPolytope_outer M P

instance : Reindex (𝒱𝒫) where
  reindex e P := VPolytope.map (reindexLin e) P
  reindex_exact e P := (VPolytope.map_exact (reindexLin e) P).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
