module

public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMemAddClosureConvexHull
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularSolutionOuter

@[expose] public section

/-!
# `P^U(Δt)` lies in the closed convex hull of eq. (20)'s set

[1, Prop. 11], eq. (20)'s soundness `P^U(Δt) ⊆ P̂^U(Δt)` is open (see `Prop. 11` on [1]'s page)
but where a point of `U₀` dominates (`inputReach_subset_particularSolutionOuter_of_dominant`): the
remainder block `E(Δt,η)ΔtU₀` is an exact interval product, which is not convex, and the
remainder of the exact solution is an integral over it. What the integral does give is the
closed convex hull. With `U₀` convex, closed, bounded and containing `0`, as [1]'s Alg. 1 has it
(`U₀ = ⟨0, BG_u⟩`), `P^U(Δt) ⊆ cl conv P̂^U(Δt)`. Every error [1] measures with `err` is the
same over a set and over its closed convex hull, so this enclosure is enough for [1, Prop. 2],
[1, Prop. 3] and [1, Prop. 11].

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 11], eq. (20): `P^U(Δt) ⊆ cl conv(⊕_{i≤η} ÃᵢU₀ ⊕ E(Δt,η)ΔtU₀)` for `U₀` convex,
closed, bounded and containing `0`. -/
theorem LinearSys.inputReach_subset_closure_convexHull (sys : LinearSys 𝕋 n) {U : S n}
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U)) (h0 : (0 : Vec ℝ n) ∈ construct U) {Δt : ℝ}
    (hΔt : 0 < Δt) (η : ℕ) :
    sys.inputReach U Δt ⊆ closure (convexHull ℝ
      (MatExp.particularSolutionOuter (toRealMat sys.A) (construct U) 0 Δt
        η)) := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set U0 := construct U with hU0
  set Eset := MatExp.intervalMulVecSet (MatExp.expRemainderMat A Δt η) (Δt • U0) with hEset
  -- the remainder block is bounded: it sits in `P̂^U_∞(Δt)`, `0` being in every other block
  have hsum0 : (0 : Vec ℝ n) ∈ ∑ i ∈ Finset.Ico 1 (η + 1),
      (fun x => (MatExp.particularCoeff A Δt i).mulVec x) '' U0 := by
    have := Set.finsetSum_mem_finsetSum (Finset.Ico 1 (η + 1))
      (fun i => (fun x => (MatExp.particularCoeff A Δt i).mulVec x) '' U0) (fun _ => 0)
      (fun i _ => ⟨0, h0, by simp⟩)
    simpa using this
  have hEO1 : Eset ⊆ MatExp.particularSolutionOuter A U0 1 Δt η := fun e he => by
    rw [MatExp.particularSolutionOuter]
    exact ⟨0, hsum0, e, he, zero_add e⟩
  have hEbdd : Bornology.IsBounded Eset := by
    obtain ⟨r, hr⟩ : ∃ r, ∀ y ∈ MatExp.particularSolutionOuter A U0 1 Δt η, ‖y‖₂ ≤ r :=
      ⟨_, MatExp.norm₂_le_of_mem_particularSolutionOuter A hbdd 1 Δt η⟩
    refine (isBounded_iff_forall_norm_le.mpr ⟨max r 0, fun y hy => ?_⟩).subset hEO1
    refine (pi_norm_le_iff_of_nonneg (le_max_right r 0)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact ((abs_le_norm₂ y i).trans (hr y hy)).trans (le_max_left r 0)
  -- a point is `x + t`, and `x + cl conv Eset = cl conv (x + Eset) ⊆ cl conv P̂`
  intro y hy
  obtain ⟨x, hx, t, ht, rfl⟩ := sys.inputReach_mem_add_closure_convexHull hconv hclosed hbdd
    hΔt η hEbdd hy
  have hxE : x +ᵥ Eset ⊆ MatExp.particularSolutionOuter A U0 0 Δt η := by
    rintro _ ⟨e, he, rfl⟩
    rw [MatExp.particularSolutionOuter]
    exact Set.add_mem_add hx he
  have hmem : x + t ∈ x +ᵥ closure (convexHull ℝ Eset) := ⟨t, ht, rfl⟩
  rw [← closure_vadd, ← convexHull_vadd] at hmem
  exact closure_mono (convexHull_mono hxE) hmem

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
