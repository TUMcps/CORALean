module

public import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs

@[expose] public section

/-!
# Do two H-polytopes intersect?

[1, Eq. 13]: they do exactly when the stacked system [1, Eq. 36] is not empty — a single
emptiness check, [1, Eq. 9], rather than any intersection being computed.

## Inputs
* `A₁` – `q₁ × n` matrix
* `b₁` – offset vector of length `q₁`
* `A₂` – `q₂ × n` matrix
* `b₂` – offset vector of length `q₂`

## Hypotheses
* none

## Conclusion
* do two H-polytopes intersect?

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

variable {q₁ q₂ n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_inter_nonempty_iff (A₁ : Mat ℝ q₁ n) (b₁ : Vec ℝ q₁) (A₂ : Mat ℝ q₂ n)
    (b₂ : Vec ℝ q₂) :
    ((HPolytope.ineqs A₁ b₁).construct ∩ (HPolytope.ineqs A₂ b₂).construct).Nonempty ↔
      ¬ ((HPolytope.ineqs A₁ b₁).intersection (HPolytope.ineqs A₂ b₂)).construct = ∅ := by
  rw [← HPolytope.intersection_exact]
  exact Set.nonempty_iff_ne_empty

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
