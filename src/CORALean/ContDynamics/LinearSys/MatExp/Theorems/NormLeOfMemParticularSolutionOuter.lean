module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.Global.Err

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

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
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
theorem aux_norm₂_le_of_mem_sum {ι : Type} (f : ι → Set (Vec ℝ n)) (bound : ι → ℝ) (s : Finset ι)
    (h : ∀ i ∈ s, ∀ y ∈ f i, ‖y‖₂ ≤ bound i) : -- --- CONCL ---
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

/-- One `Ãᵢ`-scaled summand of `bPU`, bounded pointwise by its own polynomial order in `Δt`. -/
theorem aux_norm₂_le_of_mem_particularCoeff_image (A : Mat ℝ n n) {U0 : Set (Vec ℝ n)}
    (hU0 : Bornology.IsBounded U0) (Δt : ℝ) (i : ℕ) : -- --- CONCL ---
    ∀ y ∈ (fun x => (MatExp.particularCoeff A Δt i).mulVec x) '' U0,
      ‖y‖₂ ≤ (∑ j, ‖(fun k => (A ^ i) j k)‖₂) * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ))
        * err U0 := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  have hcoeff : (MatExp.particularCoeff A Δt i).mulVec x
      = (Δt ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • (A ^ i).mulVec x := by
    simp only [MatExp.particularCoeff, Matrix.smul_mulVec]
  have h1 : ‖(A ^ i).mulVec x‖₂ ≤ (∑ j, ‖(fun k => (A ^ i) j k)‖₂) * err U0 :=
    (norm₂_mulVec_le _ x).trans (mul_le_mul_of_nonneg_left (norm₂_le_err_of_mem hU0 hx)
      (Finset.sum_nonneg fun j _ => norm₂_nonneg _))
  -- pull the scalar factor `Δtⁱ⁺¹/(i+1)!` out, then bound the matrix's own image by `h1`
  rw [hcoeff, norm₂_smul]
  have habs : |Δt ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)|
      = |Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ) := by
    rw [abs_div, abs_pow, Nat.abs_cast]
  have hmul := mul_le_mul_of_nonneg_left h1
    (abs_nonneg (Δt ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)))
  rw [habs] at hmul
  calc |Δt ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)| * ‖(A ^ i).mulVec x‖₂
      = |Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ) * ‖(A ^ i).mulVec x‖₂ := by rw [habs]
    _ ≤ |Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)
        * ((∑ j, ‖(fun k => (A ^ i) j k)‖₂) * err U0) := hmul
    _ = (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
        * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0 := by ring

/-- The interval-matrix summand of `bPU`, bounded pointwise by `n²` times the remainder's own
operator norm, scaled by the step and `U0`'s size. -/
theorem aux_norm₂_le_of_mem_intervalMulVecSet (A : Mat ℝ n n) {U0 : Set (Vec ℝ n)}
    (hU0 : Bornology.IsBounded U0) (Δt : ℝ) (η : ℕ) : -- --- CONCL ---
    ∀ y ∈ MatExp.intervalMulVecSet (MatExp.expRemainderMat A Δt η) (Δt • U0),
      ‖y‖₂ ≤ (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 := by -- --- PROOF ---
  rintro _ ⟨M, hM, x, hx, rfl⟩
  obtain ⟨x0, hx0, rfl⟩ := hx
  -- each entry of `M.mulVec (Δt • x0)` is a dot product bounded row-by-row, then summed over `n`
  have hrow : ∀ i, |M.mulVec (Δt • x0) i| ≤ (n : ℝ) * ‖MatExp.expRemainderMat A Δt η‖
      * (|Δt| * err U0) := by
    intro i
    have hpt : ‖Δt • x0‖₂ ≤ |Δt| * err U0 := by
      rw [norm₂_smul]
      exact mul_le_mul_of_nonneg_left (norm₂_le_err_of_mem hU0 hx0) (abs_nonneg _)
    -- Cauchy–Schwarz per entry against `|E|`, then the coarse `n` copies of the same bound
    calc |M.mulVec (Δt • x0) i| = |∑ j, M i j * (Δt • x0) j| := rfl
      _ ≤ ∑ j, |M i j * (Δt • x0) j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, ‖MatExp.expRemainderMat A Δt η‖ * ‖Δt • x0‖₂ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          refine mul_le_mul (hM i j |>.trans (abs_entry_le_norm _ i j)) (abs_le_norm₂ _ j)
            (abs_nonneg _) (norm_nonneg _)
      _ = (n : ℝ) * ‖MatExp.expRemainderMat A Δt η‖ * ‖Δt • x0‖₂ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
      _ ≤ (n : ℝ) * ‖MatExp.expRemainderMat A Δt η‖ * (|Δt| * err U0) :=
          mul_le_mul_of_nonneg_left hpt (by positivity)
  calc ‖M.mulVec (Δt • x0)‖₂ ≤ ∑ _i : Fin n, (n : ℝ) * ‖MatExp.expRemainderMat A Δt η‖
        * (|Δt| * err U0) :=
        (norm₂_le_sum_abs _).trans (Finset.sum_le_sum fun i _ => hrow i)
    _ = (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring


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
      (fun i _ => aux_norm₂_le_of_mem_particularCoeff_image A hU0 Δt i) y1 hy1
  have h2 : ‖y2‖₂ ≤ (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 :=
    aux_norm₂_le_of_mem_intervalMulVecSet A hU0 Δt η y2 hy2
  exact (norm₂_add_le _ _).trans (add_le_add h1 h2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
