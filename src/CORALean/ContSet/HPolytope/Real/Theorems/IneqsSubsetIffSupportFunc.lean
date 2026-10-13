import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
import CORALean.ContSet.HPolytope.Real.Operations.RowLin
import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff

/-!
# H-polytope in H-polytope by support functions

[1, Eq. 5]: `⟨A₁, b₁⟩ ⊆ ⟨A₂, b₂⟩` exactly when the support function of the first stays below
each offset of the second along that row's normal. The support function is extended-valued, so an
empty inbody (`-∞`) and one unbounded in a direction (`+∞`) need no case of their own.

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

variable {q₁ q₂ n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_subset_iff_supportFunc {A₁ : Mat ℝ q₁ n} {b₁ : Vec ℝ q₁}
    {A₂ : Mat ℝ q₂ n} {b₂ : Vec ℝ q₂} :
    (HPolytope.ineqs A₁ b₁).construct ⊆ (HPolytope.ineqs A₂ b₂).construct ↔
      ∀ j, supportFunc (HPolytope.ineqs A₁ b₁).construct (HPolytope.rowLin A₂ j)
        ≤ (b₂ j : EReal) := by -- --- PROOF ---
  simp only [supportFunc_le_coe_iff]
  constructor
  · intro h j x hx
    exact HPolytope.mem_ineqs_iff.mp (h hx) j
  · intro h x hx
    exact HPolytope.mem_ineqs_iff.mpr fun j => h j x hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
