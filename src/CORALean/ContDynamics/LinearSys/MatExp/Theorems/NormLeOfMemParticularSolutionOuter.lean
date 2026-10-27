module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.Global.Err
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularCoeffImage
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemIntervalMulVecSet

@[expose] public section

/-!
# Every point of `bPU`/`bPU_∞` is within an explicit polynomial of the origin

`norm₂_le_of_mem_particularSolutionOuter` is the one fact both `[1, Lemma 2]` and `[1, Lemma
4]` build on: every point of `bPU`/`bPU_∞` is within an explicit, `err U0`-scaled polynomial
in `Δt` of the origin, so `err`'s own asymptotics as `Δt → 0` reduce to a real-valued
computation once `err_le_of_forall_norm₂_le` is applied.

## Inputs
* `A` – system matrix
* `U0` – input set
* `i0` – start index
* `Δt` – step length
* `η` – Taylor order

## Hypotheses
* `hU0` – input set bounded

## Conclusion
* every point is within an explicit polynomial of the origin

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A pointwise bound on finitely many Minkowski summands adds to a bound on their sum. -/
private theorem aux_norm₂_le_of_mem_sum {ι : Type} (f : ι → Set (Vec ℝ n)) (bound : ι → ℝ)
    (s : Finset ι) (h : ∀ i ∈ s, ∀ y ∈ f i, ‖y‖₂ ≤ bound i) : -- --- CONCL ---
    ∀ y ∈ ∑ i ∈ s, f i, ‖y‖₂ ≤ ∑ i ∈ s, bound i := by -- --- PROOF ---
  classical
  induction s using Finset.induction with
  | empty =>
    intro y hy
    rw [Finset.sum_empty, ← Set.singleton_zero, Set.mem_singleton_iff] at hy
    rw [Finset.sum_empty, hy, norm₂_zero]
  | insert a s ha ih =>
    intro y hy
    rw [Finset.sum_insert ha, Set.mem_add] at hy
    obtain ⟨ya, hya, yrest, hyrest, rfl⟩ := hy
    rw [Finset.sum_insert ha]
    have h1 : ‖ya‖₂ ≤ bound a := h a (Finset.mem_insert_self a s) ya hya
    have h2 : ‖yrest‖₂ ≤ ∑ i ∈ s, bound i :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) yrest hyrest
    exact (norm₂_add_le _ _).trans (add_le_add h1 h2)


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of `bPU`/`bPU_∞` is within this explicit `Δt`-polynomial of the origin. -/
theorem MatExp.norm₂_le_of_mem_particularSolutionOuter (A : Mat ℝ n n) {U0 : Set (Vec ℝ n)}
    (hU0 : Bornology.IsBounded U0) (i0 : ℕ) (Δt : ℝ) (η : ℕ) : -- --- CONCL ---
    ∀ y ∈ MatExp.particularSolutionOuter A U0 i0 Δt η,
      ‖y‖₂ ≤ (∑ i ∈ Finset.Ico i0 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
          * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0)
        + (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 := by -- --- PROOF ---
  rintro y hy
  rw [MatExp.particularSolutionOuter, Set.mem_add] at hy
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := hy
  have h1 : ‖y1‖₂ ≤ ∑ i ∈ Finset.Ico i0 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
      * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0 :=
    aux_norm₂_le_of_mem_sum _ _ _
      (fun i _ => norm₂_le_of_mem_particularCoeff_image A hU0 Δt i) y1 hy1
  have h2 : ‖y2‖₂ ≤ (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 :=
    norm₂_le_of_mem_intervalMulVecSet A hU0 Δt η y2 hy2
  exact (norm₂_add_le _ _).trans (add_le_add h1 h2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
