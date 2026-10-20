module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpmIndPolytope
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExponentialRemainderOuter
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Theorems.PlusExact
public import CORALean.ContSet.VPolytope.Real.Theorems.MapExact
public import CORALean.ContSet.VPolytope.Real.Operations.ConstructPoint
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalMatrixContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalMatPolytopeExact

@[expose] public section

/-!
# `MatExp.expmIndPolytope` encloses the exponential of every member

The running product `ePpow` holds `M ^ i` at pass `i` (`matMul_outer`, the identity at pass zero),
so the Taylor terms `Mⁱ/i!` are in the vertex-sum polytope term by term (`plus_exact`, `map_exact`),
and with the identity make `expTaylor M η`. The rest of the series is in the remainder box of the
interval matrix (`exponentialRemainder_outer`, the box containing the polytope), and the box is its
own vertex polytope (`matPolytope_exact`): a nonempty box, as it contains that very remainder. Holds
for every `η`.

## Inputs
* `P` – matrix polytope
* `η` – Taylor order
* `M` – member matrix

## Hypotheses
* `hM` – member lies in the polytope

## Conclusion
* the exponential of the member lies in the polytope enclosure
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

/-- The left fold of `VPolytope.plus` over `f s, …, f (s + m - 1)` contains `a + ∑ x (s + j)`. -/
theorem MatExp.aux_foldl_plus_mem_poly (f : ℕ → VPolytope (Mat ℝ n n)) (x : ℕ → Mat ℝ n n) (s m : ℕ)
    (hx : ∀ j, j < m → x (s + j) ∈ (f (s + j)).construct) {acc : VPolytope (Mat ℝ n n)}
    {a : Mat ℝ n n} (ha : a ∈ acc.construct) : -- --- CONCL ---
    a + ∑ j ∈ Finset.range m, x (s + j) ∈ ((List.range' s m).foldl
      (fun e i => VPolytope.plus e (f i)) acc).construct := by -- --- PROOF ---
  -- peel the last index off both the list and the sum
  induction m with
  | zero => simpa using ha
  | succ m ih =>
    rw [List.range'_concat, one_mul, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← add_assoc]
    rw [← VPolytope.plus_exact]
    exact Set.add_mem_add (ih fun j hj => hx j (Nat.lt_succ_of_lt hj)) (hx m (Nat.lt_succ_self m))


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e^M` of every member `M` of the matrix polytope lies in `expmInd`. -/
theorem MatExp.expmIndPolytope_outer (P : VPolytope (Mat ℝ n n)) (η : ℕ) {M : Mat ℝ n n}
    (hM : M ∈ P.construct) :
    exp M ∈ (MatExp.expmIndPolytope P η).construct := by -- --- PROOF ---
  -- the running product `ePpow` encloses the powers of the member
  have hpow : ∀ i, M ^ i ∈ ((fun Q => VPolytope.matMul Q P)^[i] (VPolytope.point 1)).construct := by
    intro i
    induction i with
    | zero =>
      rw [pow_zero, Function.iterate_zero_apply, VPolytope.construct_point]
      rfl
    | succ i ih =>
      rw [pow_succ, Function.iterate_succ_apply']
      exact VPolytope.matMul_outer _ P ih hM
  -- the Taylor terms of orders `1 … η`, added to the identity
  have hfold := MatExp.aux_foldl_plus_mem_poly
    (fun i => ((fun Q => VPolytope.matMul Q P)^[i] (VPolytope.point 1)).map
      ((Nat.factorial i : ℝ)⁻¹ • LinearMap.id))
    (fun i => ((Nat.factorial i : ℝ)⁻¹) • M ^ i) 1 η
    (fun j _ => by
      rw [← VPolytope.map_exact]
      exact ⟨_, hpow (1 + j), by simp⟩)
    (show (1 : Mat ℝ n n) ∈ (VPolytope.point (1 : Mat ℝ n n)).construct by
      rw [VPolytope.construct_point]; rfl)
  -- they are the Taylor sum of the member
  have hT : MatExp.expTaylor M η =
      1 + ∑ j ∈ Finset.range η, ((Nat.factorial (1 + j) : ℝ)⁻¹) • M ^ (1 + j) := by
    unfold MatExp.expTaylor
    rw [Finset.sum_range_succ', add_comm]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul, add_comm 1]
  -- the remainder box holds the rest of the series, and its vertices the box
  have hrem := MatExp.exponentialRemainder_outer P.intervalMatrix η (P.intervalMatrix_contains hM)
  have hne : ∀ p q, (MatExp.exponentialRemainder P.intervalMatrix η).inf p q ≤
      (MatExp.exponentialRemainder P.intervalMatrix η).sup p q := fun p q =>
    (Interval.mem_mat_iff.mp hrem p q).1.trans (Interval.mem_mat_iff.mp hrem p q).2
  have hE := (Interval.matPolytope_exact _ hne).symm ▸ hrem
  -- the Taylor sum and the rest
  have key : exp M = (1 + ∑ j ∈ Finset.range η, ((Nat.factorial (1 + j) : ℝ)⁻¹) • M ^ (1 + j))
      + (exp M - MatExp.expTaylor M η) := by rw [← hT]; abel
  rw [key, MatExp.expmIndPolytope, ← VPolytope.plus_exact]
  exact Set.add_mem_add hfold hE

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
