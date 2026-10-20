module

public import CORALean.Specification.STL.Operations.DepReachAt

@[expose] public section

/-!
# The particular solution has `γ_u` generators per step

[1, Alg. 1]: `P_c(t_{i+1}) = e^{AΔt}P_c(t_i) ⊕ T U₀` appends the `γ_u` generators of `T U₀` to
the mapped old ones, so `P_c(t_i)` has `iγ_u` of them: the indices `γ_x+1, ..., γ_x+γ_u i` of
`H_i` in [1, Prop. 1], those of the input factors `α_{u,1}, ..., α_{u,i}` in this order.

## Inputs
* `A` – dynamics matrix
* `Δt` – time step
* `cs` – constants of the algorithm
* `X₀` – initial set
* `i` – step index

## Hypotheses
* none

## Conclusion
* the particular solution has the input generators once per step

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.depReachAt_Pc_h (A : Mat ℝ n n) (Δt : ℝ) (cs : STL.DepReachConsts n)
    (X₀ : Zonotope (Vec ℝ n)) (i : ℕ) : -- --- CONCL ---
    (STL.depReachAt A Δt cs X₀ i).Pc.h = i * cs.U₀.h := by -- --- PROOF ---
  induction i with
  | zero => simp [STL.depReachAt, STL.depReachInit, Zonotope.ofPoint]
  | succ i ih =>
    show (STL.depReachAt A Δt cs X₀ i).Pc.h + cs.U₀.h = (i + 1) * cs.U₀.h
    rw [ih]; ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
