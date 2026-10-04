import CORALean.ContSet.HPolytope.Real.Operations.IsLPCentre

/-!
# A Chebyshev centre lies in its polytope

The centre of `aux_center_LP` is feasible with a radius `r ≥ 0`, and a row norm is nonnegative, so
`aᵢ x ≤ bᵢ - ‖aᵢ‖₂ r ≤ bᵢ`: the centre satisfies every row, and every equality row is the
program's own constraint. That is all the program promises about `x`; it is not a characterisation
of which optimal `x` CORA returns.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.IsLPCentre.mem {P : HPolytope (Vec ℝ n)} {x : Vec ℝ n}
    (h : P.IsLPCentre x) : x ∈ P.construct := by -- --- PROOF ---
  obtain ⟨r, hr, hA, hAe, -⟩ := h
  refine ⟨fun i => ?_, hAe⟩
  have h0 : 0 ≤ HPolytope.rowNorm (P.A i) * r :=
    mul_nonneg (_root_.Real.sqrt_nonneg _) hr
  linarith [hA i]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
