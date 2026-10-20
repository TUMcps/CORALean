module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpmFrom
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExponentialRemainderOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.FoldlPlusMem
public import CORALean.ContSet.Interval.Real.Theorems.PowersOuter
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

@[expose] public section

/-!
# `MatExp.expmFrom` encloses the tail of the exponential series

If `P` encloses `Mᵏ`, the powers `P Mʲ` enclose `Mᵏ⁺ʲ` (`powers_outer`), the terms `k … η` are
added one at a time (`foldl_plus_mem`), and the remainder encloses what the series has past `η`,
so the result holds `e^M - Σ_{i < k} Mⁱ/i!` for every member `M`. Proved for `k ≤ η`; CORA
runs `η < k` as well, where the remainder already covers order `k`.

## Inputs
* `A` – interval matrix
* `P` – enclosure of the start power
* `η` – Taylor order
* `k` – start order
* `M` – member matrix

## Hypotheses
* `hk` – start order at most the Taylor order
* `hM` – member lies in the interval matrix
* `hP` – enclosure contains the member's start power

## Conclusion
* the series tail from the start order lies in the enclosure
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `expmFrom` encloses the tail `e^M - Σ_{i < k} Mⁱ/i!` of the series, for `k ≤ η`. -/
theorem MatExp.expmFrom_outer (A P : Interval (Mat ℝ n n)) {η k : ℕ} (hk : k ≤ η)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) (hP : M ^ k ∈ P.construct) : -- --- CONCL ---
    exp M - ∑ i ∈ Finset.range k, ((Nat.factorial i : ℝ)⁻¹) • M ^ i
      ∈ (MatExp.expmFrom A η k P).construct := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ : ∃ m, η = k + m := ⟨η - k, by omega⟩
  -- the powers continue from `P`
  have hpow : ∀ j, M ^ (k + j) ∈ (Interval.powers A P j).construct := fun j => by
    have h := Interval.powers_outer A P hM hP j
    rwa [← pow_add] at h
  have hfold := MatExp.foldl_plus_mem
    (fun i => Interval.smul ((Nat.factorial i : ℝ)⁻¹) (Interval.powers A P (i - k)))
    (fun i => ((Nat.factorial i : ℝ)⁻¹) • M ^ i) (k + 1) m
    (fun j _ => Interval.smul_outer _ _ (by
      have h := hpow (j + 1)
      rwa [show k + 1 + j - k = j + 1 by omega, show k + 1 + j = k + (j + 1) by ring]))
    (Interval.smul_outer ((Nat.factorial k : ℝ)⁻¹) P hP)
  -- the series splits at order `k`, and its first term is the start of the sum
  have hsplit : MatExp.expTaylor M (k + m) = ∑ i ∈ Finset.range k, ((Nat.factorial i : ℝ)⁻¹) • M ^ i
      + (((Nat.factorial k : ℝ)⁻¹) • M ^ k
      + ∑ j ∈ Finset.range m, ((Nat.factorial (k + 1 + j) : ℝ)⁻¹) • M ^ (k + 1 + j)) := by
    unfold MatExp.expTaylor
    rw [show k + m + 1 = k + (m + 1) by ring, Finset.sum_range_add, Finset.sum_range_succ']
    simp only [add_zero]
    rw [add_comm (∑ j ∈ Finset.range m, _)]
    congr 3
    ext
    ring_nf
  have key : exp M - ∑ i ∈ Finset.range k, ((Nat.factorial i : ℝ)⁻¹) • M ^ i
      = (((Nat.factorial k : ℝ)⁻¹) • M ^ k
        + ∑ j ∈ Finset.range m, ((Nat.factorial (k + 1 + j) : ℝ)⁻¹) • M ^ (k + 1 + j))
      + (exp M - MatExp.expTaylor M (k + m)) := by
    rw [hsplit]; abel
  rw [key]
  simp only [MatExp.expmFrom, Nat.add_sub_cancel_left]
  exact Interval.plus_outer _ _ (Set.add_mem_add hfold
    (MatExp.exponentialRemainder_outer A (k + m) hM))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
