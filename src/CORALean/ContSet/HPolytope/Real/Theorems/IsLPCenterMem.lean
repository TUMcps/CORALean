module

public import CORALean.ContSet.HPolytope.Real.Operations.IsLPCenter

@[expose] public section

/-!
# A Chebyshev center lies in its polytope

The center of `aux_center_LP` is feasible with a radius `r ≥ 0`, and a row norm is nonnegative, so
`aᵢ x ≤ bᵢ - ‖aᵢ‖₂ r ≤ bᵢ`: the center satisfies every row, and every equality row is the
program's own constraint. That is all the program promises about `x`; it is not a characterisation
of which optimal `x` CORA returns.

## Inputs
* `P` – H-polytope
* `x` – point of length `n`

## Hypotheses
* `h` – `P.IsLPCenter x`

## Conclusion
* A Chebyshev center lies in its polytope
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.IsLPCenter.mem {P : HPolytope (Vec ℝ n)} {x : Vec ℝ n}
    (h : P.IsLPCenter x) : -- --- CONCL ---
    x ∈ P.construct := by -- --- PROOF ---
  obtain ⟨r, hr, hA, hAe, -⟩ := h
  refine ⟨fun i => ?_, hAe⟩
  have h0 : 0 ≤ HPolytope.rowNorm (P.A i) * r :=
    mul_nonneg (_root_.Real.sqrt_nonneg _) hr
  linarith [hA i]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
