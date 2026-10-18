module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# The error of restarted Krylov steps is at most the sum of the local errors

[1, Sec. 7]: the time range `[0, t]` is split into substeps `Δt_j`, the exact solution advances
by `v^{[j]} = E(Δt_j)v^{[j-1]}` and the restarted Krylov approximation by
`w^{[j]} = S^{[j]}_m(Δt_j)w^{[j-1]}`, from `w^{[0]} = v`. With `E(·)` nonexpansive and the
local error of each substep at most `tol · Δt_j` (7.3), the accumulated error (7.2) satisfies
`‖L⋆_m(t)v‖ ≤ tol · t`. The local error is that of the substep's own start vector,
`‖L^{[j]}_m(Δt_j)w^{[j-1]}‖`, which the proof uses; (7.3) prints `w^{[j]}`. By induction:
`v^{[j]} - w^{[j]} = E(Δt_j)(v^{[j-1]} - w^{[j-1]}) + L^{[j]}_m(Δt_j)w^{[j-1]}`. The steps are
taken from `0` here, for any additive maps `E_j` that do not increase the norm and any maps
`S_j`.

## References

* [1] T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations
  to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197,
  2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type*} [NormedAddCommGroup X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 7]: `‖v^{[N]} - w^{[N]}‖ ≤ tol Σ_j Δt_j` for `v^{[j+1]} = E_j v^{[j]}`,
`w^{[j+1]} = S_j w^{[j]}`, `v^{[0]} = w^{[0]}`, `E_j` nonexpansive and every local error
`‖E_j w^{[j]} - S_j w^{[j]}‖ ≤ tol Δt_j` (7.3, at the substep's start vector). -/
theorem Krylov.restarted_error_le (E : ℕ → X →+ X) (S : ℕ → X → X) (v w : ℕ → X)
    (Δt : ℕ → ℝ) (tol : ℝ) (hE : ∀ j x, ‖E j x‖ ≤ ‖x‖) (hv : ∀ j, v (j + 1) = E j (v j))
    (hw : ∀ j, w (j + 1) = S j (w j)) (h0 : v 0 = w 0)
    (hloc : ∀ j, ‖E j (w j) - S j (w j)‖ ≤ tol * Δt j) (N : ℕ) : -- --- STMT ---
    ‖v N - w N‖ ≤ tol * ∑ j ∈ Finset.range N, Δt j := by -- --- PROOF ---
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    have hsplit : v (N + 1) - w (N + 1) = E N (v N - w N) + (E N (w N) - S N (w N)) := by
      rw [hv, hw, map_sub]
      abel
    rw [hsplit, Finset.sum_range_succ, mul_add]
    exact (norm_add_le _ _).trans (add_le_add ((hE N _).trans ih) (hloc N))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
