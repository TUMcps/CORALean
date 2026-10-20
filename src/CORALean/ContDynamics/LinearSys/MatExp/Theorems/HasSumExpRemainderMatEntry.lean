module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul

@[expose] public section

/-!
# One entry of the entrywise remainder, as the series it is

`expRemainderMat A Δt η` is `e^{Δt|A|}` less its Taylor sum through order `η`, so each entry is
the exponential series at `|A|` from order `η+1` on,
`Σᵢ (Δt)^{i+η+1}/(i+η+1)! · (|A|^{i+η+1})_{jk}`.
Stated as a `HasSum`, so a caller comparing it term by term against another series gets the
summability with the value, which a `tsum` equation alone does not give.

Reading one entry is `1`-Lipschitz under the `l∞` operator norm the local instances put on
`Mat ℝ n n`, which is what carries the matrix series' convergence to the entry's.

## Inputs
* `A` – system matrix
* `Δt` – step length
* `η` – Taylor order
* `j` – row index
* `k` – column index

## Hypotheses
* none

## Conclusion
* the remainder entry is the sum of the series past the order
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Evaluating a matrix at one entry, as an additive homomorphism. -/
def aux_expRemainderMatEntryHom (j k : Fin n) : Mat ℝ n n →+ ℝ where
  toFun M := M j k
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Reading one entry is continuous, being `1`-Lipschitz. -/
theorem aux_continuous_expRemainderMatEntryHom (j k : Fin n) :
    Continuous (aux_expRemainderMatEntryHom (n := n) j k) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun M N => ?_).continuous
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  simpa only [aux_expRemainderMatEntryHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Matrix.sub_apply] using abs_entry_le_norm (M - N) j k


-- =======================================  MAIN THEOREM  ======================================= --

/-- An entry of `E(Δt,η)` is the sum of the exponential series at `|A|Δt` past order `η`. -/
theorem MatExp.hasSum_expRemainderMat_entry (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) (j k : Fin n) :
    HasSum (fun i : ℕ => ((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * Δt ^ (i + (η + 1)))
        * ((MatExp.absMat A) ^ (i + (η + 1))) j k)
      (MatExp.expRemainderMat A Δt η j k) := by -- --- PROOF ---
  set B := MatExp.absMat A with hB
  set h : ℕ → Mat ℝ n n := fun i => ((Nat.factorial i : ℝ)⁻¹ * Δt ^ i) • B ^ i with hh
  have hsum : Summable h := summable_exp_smul B Δt
  have htay : MatExp.expTaylor (Δt • B) η = ∑ i ∈ Finset.range (η + 1), h i :=
    Finset.sum_congr rfl fun i _ => by rw [hh]; simp only; rw [smul_pow, smul_smul]
  -- the remainder is the series' own tail past `η`, which converges since the series does
  have hE : MatExp.expRemainderMat A Δt η = ∑' i, h (i + (η + 1)) := by
    rw [MatExp.expRemainderMat, ← hB, exp_smul_tsum B Δt, htay,
      ← hsum.sum_add_tsum_nat_add (η + 1)]
    abel
  have htail := ((summable_nat_add_iff (η + 1)).mpr hsum).hasSum
  rw [← hE] at htail
  exact htail.map (aux_expRemainderMatEntryHom j k) (aux_continuous_expRemainderMatEntryHom j k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
