module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Rank
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqImage
public import CORALean.Global.EuclideanNorm
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# An ellipsoid is full-dimensional iff its generator matrix has full rank

`isFullDim` of CORA's `@ellipsoid`: `rank(E) == dim(E)`. The ellipsoid `q + G · ball` has an
interior point exactly when the range of `G` is the whole space, i.e. when `rank G = n`. Exact,
tolerance `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Set


-- =======================================  MAIN THEOREM  ======================================= --

/-- `isFullDim`: nonempty interior iff the rank is the ambient dimension. -/
theorem Ellipsoid.isFullDim_iff {n : ℕ} (E : Ellipsoid n) :
    (interior E.construct).Nonempty ↔ E.rank = n := by -- --- PROOF ---
  -- the generator map, and the rank as the dimension of its range
  let L : Vec ℝ E.k →ₗ[ℝ] Vec ℝ n := Matrix.mulVecLin E.G
  have hrank : E.rank = n ↔ LinearMap.range L = ⊤ := by
    unfold Ellipsoid.rank Matrix.rank
    constructor
    · intro h
      exact Submodule.eq_top_of_finrank_eq (by rw [h]; simp)
    · intro h
      rw [show Matrix.mulVecLin E.G = L from rfl, h, finrank_top]; simp
  rw [hrank]
  -- the ellipsoid sits inside the translate of the range
  have hsub : E.construct ⊆ (fun v => E.q + v) '' (LinearMap.range L : Set (Vec ℝ n)) := by
    rintro x ⟨u, -, rfl⟩
    exact ⟨L u, ⟨u, rfl⟩, rfl⟩
  constructor
  · -- an interior point makes the subspace have one, so it is everything
    rintro ⟨y, hy⟩
    have h1 := interior_mono hsub hy
    have h1' : y ∈ (Homeomorph.addLeft E.q) '' interior (LinearMap.range L : Set (Vec ℝ n)) := by
      rw [Homeomorph.image_interior]; exact h1
    obtain ⟨v, hv, -⟩ := h1'
    exact Submodule.eq_top_of_nonempty_interior' _ ⟨v, hv⟩
  · -- onto, so open: the open unit ball maps to an open set around the centre
    intro htop
    have hsurj : Function.Surjective L := by
      rw [← LinearMap.range_eq_top]; exact htop
    have hopen : IsOpenMap L := L.isOpenMap_of_finiteDimensional hsurj
    let U : Set (Vec ℝ E.k) := {u | ‖u‖₂ < 1}
    have hU : IsOpen U := continuous_norm₂.isOpen_preimage _ isOpen_Iio
    have hV : IsOpen ((fun v => E.q + v) '' (L '' U)) :=
      (Homeomorph.addLeft E.q).isOpenMap _ (hopen _ hU)
    have hVsub : (fun v => E.q + v) '' (L '' U) ⊆ E.construct := by
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, le_of_lt hu, rfl⟩
    refine ⟨E.q, interior_maximal hVsub hV ⟨0, ⟨0, ?_, map_zero L⟩, by simp⟩⟩
    show ‖(0 : Vec ℝ E.k)‖₂ < 1
    rw [norm₂_zero]; exact one_pos

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
