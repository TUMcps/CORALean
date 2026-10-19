module

public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# A vertex description's combinations never exceed a bound on the vertices

Where a halfspace description needs a dual solution to bound a direction, a
vertex description reads the answer off its own data: the weights are
nonnegative and sum to one, so a combination cannot reach past the furthest
vertex.

## Inputs
* `P` – polytope
* `c` – linear functional
* `v` – bound
* `x` – point

## Hypotheses
* `h` – `c` is at most `v` on every vertex
* `hx` – `x` in `P`

## Conclusion
* `c x` is at most `v`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.le_of_forall_le (P : VPolytope α) (c : α →ₗ[ℝ] ℝ) {v : ℝ}
    (h : ∀ l, c (P.V l) ≤ v) {x : α} (hx : x ∈ P.construct) : c x ≤ v := by -- --- PROOF ---
  obtain ⟨β, hβ, hsum, rfl⟩ := hx
  rw [map_sum]
  calc ∑ l, c (β l • P.V l) = ∑ l, β l * c (P.V l) :=
        Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul]
    _ ≤ ∑ l, β l * v := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h l) (hβ l)
    _ = v := by rw [← Finset.sum_mul, hsum, one_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
