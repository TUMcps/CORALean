module

public import CORALean.ContDynamics.LinearSys.Definitions.HeldSim
public import CORALean.Specification.STL.Operations.DepReachConstsOf
public import CORALean.Specification.STL.Theorems.DepReachAtPcH
public import CORALean.Specification.STL.Theorems.SumGenMtimes
public import CORALean.Specification.STL.Theorems.SumGenOfPoint
public import CORALean.Specification.STL.Theorems.SumGenPlus
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# The state of the reach sequence at `t_i` is the held-input solution, factor by factor

[1, Alg. 1]: with the factors `α̃ = [α_x; α_{u,1}; ...]` of [1, Prop. 1] — the first `γ_x` weights
the generators of `H(t_i)`, the next `γ_u` those of the first step of `P_c(t_i)`, and so on — the
center and the weighted generators of `H(t_i)` and `P_c(t_i)` add up to the state of
`x(k+1) = e^{AΔt}x(k) + T B u(k)` from `x₀ = c_x + G_xα_x` under the inputs
`u(j) = c_u + G_uα_{u,j+1}`: the dependency of the reachable state on `x₀` and `u(·)` that
[1, Prop. 1] reads off.

## Inputs
* `A` – dynamics matrix
* `B` – input matrix
* `X₀` – initial set
* `U` – input set
* `Δt` – time step
* `κ` – Taylor order
* `α` – factor values
* `i` – step index

## Hypotheses
* none

## Conclusion
* the solution of the held input is the sum of the two parts factor by factor

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.depReachAt_sum (A : Mat ℝ n n) (B : Mat ℝ n m) (X₀ : Zonotope (Vec ℝ n))
    (U : Zonotope (Vec ℝ m)) (Δt : ℝ) (κ : ℕ) (α : ℕ → ℝ) (i : ℕ) : -- --- CONCL ---
    let s := STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i
    s.H.c + ∑ k : Fin s.H.h, α k • s.H.G k + ∑ k : Fin s.Pc.h, α (X₀.h + k) • s.Pc.G k
      = (LinearSys.canonical A).heldSim Δt (X₀.c + ∑ l : Fin X₀.h, α l • X₀.G l)
          (fun j => B *ᵥ (U.c + ∑ l : Fin U.h, α (X₀.h + j * U.h + l) • U.G l))
          i := by -- --- PROOF ---
  induction i with
  | zero =>
    intro s
    show X₀.c + ∑ k : Fin X₀.h, α k • X₀.G k
      + ∑ k : Fin (Zonotope.ofPoint (0 : Vec ℝ n)).h, α (X₀.h + k) • (Zonotope.ofPoint 0).G k
      = X₀.c + ∑ l : Fin X₀.h, α l • X₀.G l
    rw [STL.sumGen_ofPoint, add_zero]
  | succ i ih =>
    intro s
    have ih' := ih
    simp only [] at ih'
    have hPc : (STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i).Pc.h = i * U.h := by
      rw [STL.depReachAt_Pc_h]; rfl
    -- the sum over the inputs `U₀ = B(U ⊕ (-c_u))`
    have hU₀ : ∀ g : ℕ → ℝ,
        ∑ k : Fin (Zonotope.mtimes B (U.plus (Zonotope.ofPoint (-U.c)))).h,
            g k • (Zonotope.mtimes B (U.plus (Zonotope.ofPoint (-U.c)))).G k
          = B *ᵥ ∑ l : Fin U.h, g l • U.G l := by
      intro g
      rw [STL.sumGen_mtimes, STL.sumGen_plus]
      simp only [STL.sumGen_ofPoint, add_zero]
    -- `s` is one pass of the loop from the state at `t_i`, which is then held abstract
    have hs : s = STL.depReachStep A Δt (STL.depReachConsts A B U Δt κ)
        (STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i) := rfl
    rw [hs]
    clear_value s
    generalize STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i = si at ih' hPc ⊢
    -- the weighted generators of `H(t_{i+1})`: `e^{AΔt}` applied, no generator appended
    have e1 := STL.sumGen_plus (Zonotope.mtimes (exp (Δt • A)) si.H)
      (Zonotope.ofPoint ((MatExp.expIntegral A Δt) *ᵥ (B *ᵥ U.c))) α
    rw [STL.sumGen_ofPoint, add_zero, STL.sumGen_mtimes _ _ α] at e1
    -- the input's contribution, mapped by `T`
    set Tu := Zonotope.mtimes (MatExp.expIntegral A Δt)
      (Zonotope.mtimes B (U.plus (Zonotope.ofPoint (-U.c)))) with hTu
    -- those of `P_c(t_{i+1})`: the old ones mapped, the `γ_u` of `T U₀` after them
    have e2 := STL.sumGen_plus (Zonotope.mtimes (exp (Δt • A)) si.Pc)
      Tu (fun k => α (X₀.h + k))
    have hP2 : (Zonotope.mtimes (exp (Δt • A)) si.Pc).h = i * U.h := hPc
    rw [STL.sumGen_mtimes _ _ (fun k => α (X₀.h + k)),
      STL.sumGen_mtimes _ _ (fun k => α (X₀.h + ((Zonotope.mtimes (exp (Δt • A)) si.Pc).h + k))),
      hU₀ (fun k => α (X₀.h + ((Zonotope.mtimes (exp (Δt • A)) si.Pc).h + k)))] at e2
    simp only [hP2] at e2
    -- the stepped set plus the input's point
    set st := (Zonotope.mtimes (exp (Δt • A)) si.H).plus
      (Zonotope.ofPoint ((MatExp.expIntegral A Δt) *ᵥ (B *ᵥ U.c))) with hst
    -- the state after the pass in terms of the state before, over the stepped sets
    have main : st.c
        + ∑ k : Fin st.h,
          α k • st.G k
        -- the sum over `P_c(t_{i+1})`
        + ∑ k : Fin ((Zonotope.mtimes (exp (Δt • A)) si.Pc).plus Tu).h,
          α (X₀.h + k) • ((Zonotope.mtimes (exp (Δt • A)) si.Pc).plus Tu).G k
        = exp (Δt • A) *ᵥ (si.H.c + ∑ k : Fin si.H.h, α k • si.H.G k
            + ∑ k : Fin si.Pc.h, α (X₀.h + k) • si.Pc.G k)
          + MatExp.expIntegral A Δt
            *ᵥ (B *ᵥ (U.c + ∑ l : Fin U.h, α (X₀.h + i * U.h + l) • U.G l)) := by
      rw [e1, e2]
      simp only [st, Zonotope.plus, Zonotope.mtimes, Zonotope.ofPoint, Matrix.mulVec_add,
        Matrix.mulVec_mulVec]
      simp only [add_assoc]
      abel
    rw [ih'] at main
    exact main

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
