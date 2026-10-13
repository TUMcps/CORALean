module

public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# A Euclidean error bound is a box

[1, Lemma III.1]: from the a-posteriori bound (3), `‖e^{At}x₀ - x̂_h(t)‖ ≤ ‖x₀‖ε t`, the exact
solution lies in `x̂_h(t) ⊕ [-1, 1]ⁿ ‖x₀‖ε t` (10). Taken here with (3) as its hypothesis, for
any vector `x` and approximation `x̂`: every coordinate is at most the Euclidean norm. The
bound itself is [1]'s citation of Wang and Ye's a-posteriori estimate, not proved here.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.mem_box_of_norm₂_le {x xhat : Vec ℝ n} {e : ℝ} (h : ‖x - xhat‖₂ ≤ e) :
    ∃ r : Vec ℝ n, (∀ j, |r j| ≤ e) ∧ x = xhat + r :=
  ⟨x - xhat, fun j => (abs_le_norm₂ _ j).trans h, by abel⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
