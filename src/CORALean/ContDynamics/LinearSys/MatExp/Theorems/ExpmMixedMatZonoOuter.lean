module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpmMixedMatZono
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.DependentTermsMatZonoOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpmFromOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorTwo
public import CORALean.ContSet.Zonotope.Real.Theorems.PowersOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Real.Theorems.MatMulOuter

@[expose] public section

/-!
# `MatExp.expmMixedMatZono` encloses the two parts of the exponential series

For `2 ≤ k < η` the first part holds the Taylor sum of order `k`: `H` of the scaled `dependentTerms`
is `I + M + ½ M²` of the member, and the zonotope powers from the square (`powers_outer`) are added
one at a time. The second part holds the rest of the series, `e^M - Σ_{i ≤ k} Mⁱ/i!`
(`expmFrom_outer` from order `k + 1`), started at the product of the box of the zonotope with the
box of its last power, which contains `M * Mᵏ`. Their sum encloses `e^M`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The left fold of `Zonotope.plus` over `f s, …, f (s + m - 1)` encloses `a + ∑ x (s + j)`. -/
theorem MatExp.aux_foldl_plus_mem_zono (f : ℕ → Zonotope (Mat ℝ n n)) (x : ℕ → Mat ℝ n n) (s m : ℕ)
    (hx : ∀ j, j < m → x (s + j) ∈ (f (s + j)).construct) {acc : Zonotope (Mat ℝ n n)}
    {a : Mat ℝ n n} (ha : a ∈ acc.construct) :
    a + ∑ j ∈ Finset.range m, x (s + j) ∈ ((List.range' s m).foldl
      (fun e i => Zonotope.plus e (f i)) acc).construct := by -- --- PROOF ---
  -- peel the last index off both the list and the sum
  induction m with
  | zero => simpa using ha
  | succ m ih =>
    rw [List.range'_concat, one_mul, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← add_assoc]
    rw [← Zonotope.plus_exact]
    exact Set.add_mem_add (ih fun j hj => hx j (Nat.lt_succ_of_lt hj)) (hx m (Nat.lt_succ_self m))


-- =======================================  MAIN THEOREM  ======================================= --

/-- `eZ` holds the Taylor sum of order `k` and `eI` the rest of the series, of every member. -/
theorem MatExp.expmMixedMatZono_outer (Z : Zonotope (Mat ℝ n n)) {r : ℝ} (hr : r ≠ 0) {k η : ℕ}
    (hk : 2 ≤ k) (hη : k < η) {M : Mat ℝ n n} (hM : M ∈ Z.construct) :
    MatExp.expTaylor M k ∈ (MatExp.expmMixedMatZono Z r k η).eZ.construct ∧
      exp M - MatExp.expTaylor M k ∈
        (MatExp.expmMixedMatZono Z r k η).eI.construct := by -- --- PROOF ---
  -- the member scaled by `1 / r` is in the scaled zonotope
  have hM' : r⁻¹ • M ∈ (Z.map ((1 / r) • LinearMap.id)).construct := by
    rw [← Zonotope.map_exact]
    exact ⟨M, hM, by simp [one_div]⟩
  -- `dependentTerms` of the scaled zonotope encloses the terms of the scaled member
  have hdep := MatExp.dependentTermsMatZono_outer (Z.map ((1 / r) • LinearMap.id)) r hM'
  have hMM : M * M = r ^ 2 • ((r⁻¹ • M) * (r⁻¹ • M)) := by
    rw [smul_mul_smul_comm, smul_smul]
    have : r ^ 2 * (r⁻¹ * r⁻¹) = 1 := by field_simp
    rw [this, one_smul]
  have hsq := hdep.1
  rw [← hMM] at hsq
  -- the powers from the square enclose `M ^ j`, for `j ≥ 2`
  have hpow : ∀ j, 2 ≤ j → M ^ j ∈ (Zonotope.powers Z
      (MatExp.dependentTermsMatZono (Z.map ((1 / r) • LinearMap.id)) r).zSq (j - 2)).construct := by
    intro j hj
    have h := Zonotope.powers_outer Z _ hM hsq (j - 2)
    rwa [← pow_two, ← pow_add, show 2 + (j - 2) = j by omega] at h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  refine ⟨?_, ?_⟩
  · -- the Taylor terms `3 … k` added to `H` enclose the partial sum
    have hT2 : 1 + MatExp.expW (r⁻¹ • M) r = MatExp.expTaylor M 2 := by
      rw [← MatExp.expTaylor_two, smul_smul, mul_inv_cancel₀ hr, one_smul]
    have hH := hdep.2
    have hfold := MatExp.aux_foldl_plus_mem_zono
      (fun i => (Zonotope.powers Z
        (MatExp.dependentTermsMatZono (Z.map ((1 / r) • LinearMap.id)) r).zSq (i - 2)).map
          ((Nat.factorial i : ℝ)⁻¹ • LinearMap.id))
      (fun i => ((Nat.factorial i : ℝ)⁻¹) • M ^ i) 3 j
      (fun l _ => by
        rw [← Zonotope.map_exact]
        exact ⟨_, hpow (3 + l) (by omega), by simp⟩) hH
    rw [hT2] at hfold
    -- and the series splits at order two
    have hsplit : MatExp.expTaylor M (j + 2) = MatExp.expTaylor M 2
        + ∑ l ∈ Finset.range j, ((Nat.factorial (3 + l) : ℝ)⁻¹) • M ^ (3 + l) := by
      unfold MatExp.expTaylor
      rw [show j + 2 + 1 = 3 + j by omega, Finset.sum_range_add]
    rw [hsplit]
    simpa only [MatExp.expmMixedMatZono, Nat.add_sub_cancel] using hfold
  · -- `Z.interval * interval(zPow{k})` encloses `M ^ (k + 1)`, the start of the tail
    have hP : M ^ (j + 2 + 1) ∈ (Interval.matMul Z.interval
        (Zonotope.powers Z (MatExp.dependentTermsMatZono (Z.map ((1 / r) • LinearMap.id)) r).zSq
          (j + 2 - 2)).interval).construct := by
      rw [pow_succ']
      exact Interval.matMul_outer _ _ (Z.interval_contains hM)
        (Zonotope.interval_contains _ (hpow (j + 2) (by omega)))
    exact MatExp.expmFrom_outer Z.interval _ (η := η) (k := j + 2 + 1) hη
      (Z.interval_contains hM) hP

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
