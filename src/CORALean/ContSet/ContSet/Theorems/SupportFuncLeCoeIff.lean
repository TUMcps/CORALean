module

public import CORALean.ContSet.ContSet.Definitions.SupportFunc

@[expose] public section

/-!
# `supportFunc_le_coe_iff`

A real bound on the support function is a bound on every point: the step that turns the
support-function tests of [1, Eq. 5] and [1, Eq. 16] into statements about points.

## Inputs
* `S` – set
* `ℓ` – linear functional
* `b` – bound

## Hypotheses
* none

## Conclusion
* the support function is at most `b` iff `ℓ x ≤ b` on all of `S`

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

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem supportFunc_le_coe_iff {S : Set α} {ℓ : α →ₗ[ℝ] ℝ} {b : ℝ} :
    supportFunc S ℓ ≤ (b : EReal) ↔ ∀ x ∈ S, ℓ x ≤ b := by
  unfold supportFunc
  rw [iSup₂_le_iff]
  exact forall₂_congr fun _ _ => EReal.coe_le_coe_iff

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
