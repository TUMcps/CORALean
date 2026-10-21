module

public import CORALean.ContSet.HPolytope.Real.Theorems.IneqsEqImageRestrict
public import CORALean.ContSet.HPolytope.Real.Theorems.Convex
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# The restriction of a polytope to its affine hull is non-degenerate

[1, Sec. 4.1 (H vertex enumeration)]: with `B` a basis of the affine hull of `P = ⟨A, b⟩` —
injective, its range the direction of the hull — and `c ∈ P`, the polytope `P' = ⟨A B, b - A c⟩
⊆ ℝʳ` has an interior, "by definition of `B`": the directions `P'` spans are mapped by `B` onto
the directions `P` spans, which are all of `range B`, so `P'` spans all of `ℝʳ`.

## Inputs
* `A` – `q × n` matrix
* `b` – offset vector of length `q`
* `B` – `n × r` matrix
* `c` – center of length `n`

## Hypotheses
* `hc` – `c` lies in `(HPolytope.ineqs A b)`
* `hB` – `B` is injective as a linear map
* `hspan` – the range of `B` is the vector span of the polytope

## Conclusion
* the restriction of a polytope to its affine hull is non-degenerate

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.interior_restrict_nonempty (A : Mat ℝ q n) (b : Vec ℝ q) (B : Mat ℝ n r)
    (c : Vec ℝ n) (hc : c ∈ (HPolytope.ineqs A b).construct)
    (hB : Function.Injective (Matrix.mulVecLin B))
    (hspan : LinearMap.range (Matrix.mulVecLin B) = vectorSpan ℝ (HPolytope.ineqs A b).construct)
    : -- --- CONCL ---
    (interior (HPolytope.ineqs (A * B) (b - A *ᵥ c)).construct).Nonempty := by -- --- PROOF ---
  set P := (HPolytope.ineqs A b).construct
  set P' := (HPolytope.ineqs (A * B) (b - A *ᵥ c)).construct
  -- `P ⊆ c + range B`, so `P = B P' + c`
  have hP : ∀ x ∈ P, ∃ y, x - c = B *ᵥ y := fun x hx => by
    have hmem : x -ᵥ c ∈ vectorSpan ℝ P := vsub_mem_vectorSpan ℝ hx hc
    rw [← hspan] at hmem
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, hy.symm⟩
  have heq : P = (fun y => B *ᵥ y + c) '' P' := HPolytope.ineqs_eq_image_restrict A b B c hP
  -- the directions of `P` are those of `P'`, mapped by `B`
  have hmap : vectorSpan ℝ P = (vectorSpan ℝ P').map (Matrix.mulVecLin B) := by
    rw [vectorSpan_def, vectorSpan_def, Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨x₁, hx₁, x₂, hx₂, rfl⟩
      rw [heq] at hx₁ hx₂
      obtain ⟨y₁, hy₁, rfl⟩ := hx₁
      obtain ⟨y₂, hy₂, rfl⟩ := hx₂
      refine ⟨y₁ -ᵥ y₂, ⟨y₁, hy₁, y₂, hy₂, rfl⟩, ?_⟩
      simp [vsub_eq_sub, Matrix.mulVec_sub]
    -- back: a difference in `P'`, mapped, is a difference in `P`
    · rintro ⟨_, ⟨y₁, hy₁, y₂, hy₂, rfl⟩, rfl⟩
      refine ⟨B *ᵥ y₁ + c, ?_, B *ᵥ y₂ + c, ?_, ?_⟩
      · rw [heq]
        exact ⟨y₁, hy₁, rfl⟩
      · rw [heq]
        exact ⟨y₂, hy₂, rfl⟩
      · simp [vsub_eq_sub, Matrix.mulVec_sub]
  -- `B` is injective and its range is all of `P`'s directions
  have htop : vectorSpan ℝ P' = ⊤ := by
    apply Submodule.map_injective_of_injective hB
    rw [← hmap, ← hspan, Submodule.map_top]
  have hne : P'.Nonempty := ⟨0, HPolytope.mem_ineqs_iff.mpr fun i => by
    have := HPolytope.mem_ineqs_iff.mp hc i
    simp only [Matrix.mulVec_zero, Pi.zero_apply, Pi.sub_apply]
    linarith⟩
  rw [(HPolytope.ineqs (A * B) (b - A *ᵥ c)).convex_construct
      |>.interior_nonempty_iff_affineSpan_eq_top,
    AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hne]
  exact htop

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
