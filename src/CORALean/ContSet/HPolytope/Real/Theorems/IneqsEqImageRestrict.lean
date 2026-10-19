module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A degenerate H-polytope, restricted to its affine hull

[1, Sec. 4.1 (H vertex enumeration)]: if `P = ⟨A, b⟩ ⊆ c + span(B)`, then `P = B P' + c` with
`P' = ⟨A B, b - A c⟩`, so the vertices of `P` are those of `P'` mapped back. Every point of `P`
is `B y + c` for some `y`, and `y ∈ P'` is the same inequalities rewritten.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
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

theorem HPolytope.ineqs_eq_image_restrict (A : Mat ℝ q n) (b : Vec ℝ q) (B : Mat ℝ n r)
    (c : Vec ℝ n)
    (hP : ∀ x ∈ (HPolytope.ineqs A b).construct, ∃ y, x - c = B *ᵥ y) : -- --- CONCL ---
    (HPolytope.ineqs A b).construct =
      (fun y => B *ᵥ y + c) ''
        (HPolytope.ineqs (A * B) (b - A *ᵥ c)).construct := by -- --- PROOF ---
  have hrow : ∀ y i, (A *ᵥ (B *ᵥ y + c)) i ≤ b i ↔ ((A * B) *ᵥ y) i ≤ (b - A *ᵥ c) i :=
    fun y i => by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Pi.add_apply, Pi.sub_apply]
      constructor <;> intro h <;> linarith
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hP x hx
    have hxy : x = B *ᵥ y + c := by rw [← hy, sub_add_cancel]
    refine ⟨y, HPolytope.mem_ineqs_iff.mpr fun i => (hrow y i).mp ?_, hxy.symm⟩
    rw [← hxy]
    exact HPolytope.mem_ineqs_iff.mp hx i
  · rintro ⟨y, hy, rfl⟩
    exact HPolytope.mem_ineqs_iff.mpr fun i => (hrow y i).mpr (HPolytope.mem_ineqs_iff.mp hy i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
