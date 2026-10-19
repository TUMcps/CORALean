module

public import CORALean.Specification.STL.Theorems.DepReachPointDependency
public import CORALean.Specification.STL.Theorems.NotMemOfNotMemUnsafeFactors
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# [1, Prop. 2] at the time points: the polytope `K_i1`

For `R(t_i) = ⟨c_i1, G_i1⟩_Z` of [1, Alg. 1] and `P = ⟨C, d⟩_P`, a factor `α̃` outside
`K_i1 = ⟨[C G_i1(·,H_i) 0], d - C c_i1 + Σ_{j∈K_i} |C G_i1(·,j)|⟩_P`, `H_i` the first
`γ_x + γ_u i` generators, has `ξ(t_i,x₀,u(·)) ∉ P`. [1, Prop. 1] holds at `t_i`
(`STL.depReachPoint_dependency`), so `ξ = c_i1 + G_i1(·,H_i) α̃` and the hypothesis `hξ` of
`STL.not_mem_of_not_mem_unsafeFactors` is proved, with the uncertain part `β = 0`. The half
for the time interval `K_i2` is false: `STL.unsafeFactors_interval_counterexample`.

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

theorem STL.not_mem_of_not_mem_unsafeFactors_point (A : Mat ℝ n n) (B : Mat ℝ n m)
    (X₀ : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m)) {Δt : ℝ} (hΔt : 0 < Δt) (κ : ℕ)
    (α : ℕ → ℝ) (hα : ∀ k, |α k| ≤ 1) (i : ℕ) {s : ℕ} (C : Matrix (Fin s) (Fin n) ℝ)
    (d : Fin s → ℝ) {p : ℕ} (hp : X₀.h + i * U.h ≤ p) : -- --- CONCL ---
    let R := STL.depReachPoint (STL.depReachAt A Δt (STL.depReachConsts A B U Δt κ) X₀ i)
    ∀ (hle : X₀.h + i * U.h ≤ R.h),
      (fun l : Fin p => α l) ∉ STL.unsafeFactors C d R.c (Matrix.of fun j k => R.G k j)
          (Fin.castLE hle) (Finset.univ.filter fun k : Fin R.h => X₀.h + i * U.h ≤ k) hp →
      ¬ (∀ r, C.mulVec ((LinearSys.canonical A).closedForm (X₀.c + ∑ l : Fin X₀.h, α l • X₀.G l)
        (LinearSys.heldInput Δt
          (fun j => B *ᵥ (U.c + ∑ l : Fin U.h, α (X₀.h + j * U.h + l) • U.G l))) (i * Δt)) r
          ≤ d r) := by -- --- PROOF ---
  intro R hle hα' hP
  obtain ⟨hξ, -⟩ := STL.depReachPoint_dependency A B X₀ U hΔt κ α hα i
  refine STL.not_mem_of_not_mem_unsafeFactors C d R.c (Matrix.of fun j k => R.G k j)
    (Fin.castLE hle) (Finset.univ.filter fun k : Fin R.h => X₀.h + i * U.h ≤ k) hp
    (fun l : Fin p => α l) (fun _ => 0) (fun k _ => by simp) _ ?_ hα' hP
  intro j
  have hj := congrFun hξ j
  simp only [Pi.add_apply] at hj
  rw [hj]
  simp only [Matrix.of_apply, mul_zero, Finset.sum_const_zero, add_zero]
  -- the sum over all generators with the cut-off weight is the sum over the first ones
  have hsum : ∑ k : Fin R.h, (if (k : ℕ) < X₀.h + i * U.h then α k else 0) • R.G k =
      ∑ k : Fin (X₀.h + i * U.h), α k • R.G (Fin.castLE hle k) := by
    -- first the weight `0` terms are dropped, then the first generators are the image of `castLE`
    calc _ = ∑ k ∈ Finset.univ.filter (fun k : Fin R.h => (k : ℕ) < X₀.h + i * U.h),
          α k • R.G k := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> simp
      _ = ∑ k ∈ Finset.univ.map (Fin.castLEEmb hle), α k • R.G k := by
          congr 1
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
            Fin.coe_castLEEmb]
          constructor
          · intro hk; exact ⟨⟨k, hk⟩, Fin.ext rfl⟩
          · rintro ⟨a, rfl⟩; simp
      _ = _ := Finset.sum_map _ _ _
  -- the component `j` of the sum, the generator before the factor
  change (∑ k : Fin R.h, (if (k : ℕ) < X₀.h + i * U.h then α k else 0) • R.G k) j + R.c j = _
  rw [hsum, Finset.sum_apply, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
