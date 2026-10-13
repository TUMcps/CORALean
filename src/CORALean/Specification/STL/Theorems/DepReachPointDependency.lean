module

public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormHeldInput
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
public import CORALean.Specification.STL.Operations.DepReachPoint
public import CORALean.Specification.STL.Theorems.DepBloatingC
public import CORALean.Specification.STL.Theorems.DepReachAtDC
public import CORALean.Specification.STL.Theorems.DepReachAtHh
public import CORALean.Specification.STL.Theorems.DepReachAtPcC
public import CORALean.Specification.STL.Theorems.DepReachAtPcH
public import CORALean.Specification.STL.Theorems.DepReachAtSum
public import CORALean.Specification.STL.Theorems.SumGenPlus

@[expose] public section

/-!
# [1, Prop. 1] at the time points

For `X₀ = ⟨c_x, G_x⟩_Z`, `U = ⟨c_u, G_u⟩_Z`, factors `α̃ = [α_x; α_{u,1}; ...]` in `[-1,1]`
(`α`, indexed from `0`), `x₀ = c_x + G_xα_x` and the piecewise constant `u(t) = c_u + G_uα_{u,j}`
on `((j-1)Δt, jΔt]` (`B u(t)` enters the state, as [1, Sec. 3] has it), the solution at
`t_i = iΔt` is `ξ = μ + c_{i1}` with `μ = [G_{i1}(·,H_i) 0] α̃` of [1, Prop. 1]: the generators
of `R(t_i)` weighted by `α̃` for the first `|H_i| = γ_x + γ_u i` indices and by `0` after, `H_i` as
in [1, Prop. 1]. So `ξ ∈ μ ⊕ E(t_i)`, `E(t_i) = ⟨c_{i1}, G_{i1}(·,K_i)⟩_Z` at the factor `0` of
its generators, and `μ ⊕ E(t_i) ⊆ R(t_i)` for any factors of `E` in `[-1,1]`: [1, Def. 4].

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

open CORALean.Real Matrix NormedSpace

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.depReachPoint_dependency (A : Mat ℝ n n) (B : Mat ℝ n m) (X₀ : Zonotope (Vec ℝ n))
    (U : Zonotope (Vec ℝ m)) {Δt : ℝ} (hΔt : 0 < Δt) (κ : ℕ) (α : ℕ → ℝ)
    (hα : ∀ k, |α k| ≤ 1) (i : ℕ) :
    let R := STL.depReachPoint (STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i)
    let μ : Vec ℝ n := ∑ k : Fin R.h, (if (k : ℕ) < X₀.h + i * U.h then α k else 0) • R.G k
    let ξ := (LinearSys.mk A).closedForm (X₀.c + ∑ l : Fin X₀.h, α l • X₀.G l)
      (LinearSys.heldInput Δt
        (fun j => B *ᵥ (U.c + ∑ l : Fin U.h, α (X₀.h + j * U.h + l) • U.G l))) (i * Δt)
    ξ = μ + R.c ∧ ∀ β : Fin R.h → ℝ, (∀ k, |β k| ≤ 1) →
      μ + (R.c + ∑ k : Fin R.h, (if (k : ℕ) < X₀.h + i * U.h then 0 else β k) • R.G k)
        ∈ R.construct := by -- --- PROOF ---
  -- name the three objects and their definitions, then hold the state at `t_i` abstract
  intro R μ ξ
  have hRd : R = (STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i).H.plus
      ((STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i).Pc.plus
        (STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i).D) := rfl
  have hμd : μ = ∑ k : Fin R.h, (if (k : ℕ) < X₀.h + i * U.h then α k else 0) • R.G k := rfl
  have hξd : ξ = (LinearSys.mk A).closedForm (X₀.c + ∑ l : Fin X₀.h, α l • X₀.G l)
      (LinearSys.heldInput Δt
        (fun j => B *ᵥ (U.c + ∑ l : Fin U.h, α (X₀.h + j * U.h + l) • U.G l))) (i * Δt) := rfl
  clear_value μ ξ R
  have hU0c : (STL.depReachConsts A B U Δt κ).U₀.c = 0 := by
    show B *ᵥ (U.c + -U.c) = 0
    simp
  have hDc : (STL.depReachConsts A B U Δt κ).D.c = 0 := STL.depBloating_c _ _ _ _ hU0c
  -- the layout of `R(t_i)`: the sizes of the blocks and where each is centred
  have hHh := STL.depReachAt_H_h A Δt (STL.depReachConsts A B U Δt κ) X₀ i
  have hPh : (STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i).Pc.h = i * U.h :=
    STL.depReachAt_Pc_h A Δt (STL.depReachConsts A B U Δt κ) X₀ i
  have hPcc := STL.depReachAt_Pc_c A Δt (STL.depReachConsts A B U Δt κ) X₀ hU0c i
  have hDcc := STL.depReachAt_D_c A Δt (STL.depReachConsts A B U Δt κ) X₀ hDc i
  have hsum := STL.depReachAt_sum A B X₀ U Δt κ α i
  simp only [] at hsum
  -- the held-input solution at `t_i`
  have hxi : ξ = (LinearSys.mk A).heldSim Δt (X₀.c + ∑ l : Fin X₀.h, α l • X₀.G l)
      (fun j => B *ᵥ (U.c + ∑ l : Fin U.h, α (X₀.h + j * U.h + l) • U.G l)) i := by
    rw [hξd]
    -- `heldSim` is the solution at `t_i`, for the inputs `B u` in `B U`
    refine (LinearSys.mk A).closedForm_heldInput (S := fun k => Zonotope (Vec ℝ k))
      (U := Zonotope.mtimes B U) (Zonotope.isBounded_construct _) hΔt _ ?_ i
    intro j
    refine ⟨fun l => α (X₀.h + j * U.h + l), fun l => hα _, ?_⟩
    simp only [Zonotope.mtimes, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul]
    rfl
  generalize STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i = si at *
  subst hRd
  -- `R(t_i) = H ⊕ (P_c ⊕ D)`: the weighted sum splits into those of the three blocks
  have hblocks := STL.sumGen_plus si.H (si.Pc.plus si.D)
    (fun k => if k < X₀.h + i * U.h then α k else 0)
  rw [STL.sumGen_plus si.Pc si.D
    (fun k => (fun k => if k < X₀.h + i * U.h then α k else 0) (si.H.h + k))] at hblocks
  -- `μ` is the weighted sum over `H` and over `P_c`, the last block has weight `0`
  have hμ : μ = ∑ k : Fin si.H.h, α k • si.H.G k
      + ∑ k : Fin si.Pc.h, α (X₀.h + k) • si.Pc.G k := by
    rw [hμd, hblocks]
    have e1 : ∑ k : Fin si.H.h, (if (k : ℕ) < X₀.h + i * U.h then α k else 0) • si.H.G k
        = ∑ k : Fin si.H.h, α k • si.H.G k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have : (k : ℕ) < X₀.h + i * U.h := by have := k.2; omega
      rw [if_pos this]
    have e2 : ∑ k : Fin si.Pc.h, (if si.H.h + (k : ℕ) < X₀.h + i * U.h then α (si.H.h + k) else 0)
          • si.Pc.G k = ∑ k : Fin si.Pc.h, α (X₀.h + k) • si.Pc.G k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have : si.H.h + (k : ℕ) < X₀.h + i * U.h := by have := k.2; omega
      rw [if_pos this, hHh]
    -- the weight of `D`'s generators is `0`
    have e3 : ∑ k : Fin si.D.h, (if si.H.h + (si.Pc.h + (k : ℕ)) < X₀.h + i * U.h
          then α (si.H.h + (si.Pc.h + k)) else 0) • si.D.G k = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have : ¬ si.H.h + (si.Pc.h + (k : ℕ)) < X₀.h + i * U.h := by omega
      rw [if_neg this, zero_smul]
    rw [e1, e2, e3, add_zero]
  -- the centre of `R(t_i)` is that of `H(t_i)`
  have hc : (si.H.plus (si.Pc.plus si.D)).c = si.H.c := by
    show si.H.c + (si.Pc.c + si.D.c) = _
    rw [hPcc, hDcc]; simp
  -- `μ + c` is the solution, and `μ ⊕ E` is in `R` for any factors of `E`
  refine ⟨?_, ?_⟩
  · rw [hxi, ← hsum, hμ, hc]
    abel
  · intro β hβ
    -- the factors: `α` on `H_i`, `β` on the rest
    refine ⟨fun k => if (k : ℕ) < X₀.h + i * U.h then α k else β k, ?_, ?_⟩
    · intro k
      dsimp only
      split_ifs
      · exact hα _
      · exact hβ k
    · rw [hμd]
      have hk : ∀ k : Fin (si.H.plus (si.Pc.plus si.D)).h,
          (if (k : ℕ) < X₀.h + i * U.h then α k else β k) • (si.H.plus (si.Pc.plus si.D)).G k
            = (if (k : ℕ) < X₀.h + i * U.h then α k else 0) • (si.H.plus (si.Pc.plus si.D)).G k
              + (if (k : ℕ) < X₀.h + i * U.h then 0 else β k)
                • (si.H.plus (si.Pc.plus si.D)).G k := by
        intro k
        split_ifs <;> simp
      rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib]
      abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
