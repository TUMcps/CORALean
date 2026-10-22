module

public import CORALean.ContSet.Zonotope.Real.Operations.ReducePCA
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceByCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReducePCACost

@[expose] public section

/-!
# `Zonotope.reducePCACost_mono`

Monotone in the generator count.

## Inputs
* `h` – smaller generator count
* `h'` – larger generator count
* `n` – dimension
* `eig` – cost of the eigendecomposition
* `inv` – cost of the basis inverse

## Hypotheses
* `hle` – generator counts ordered

## Conclusion
* cost is monotone in the generator count
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Monotone in the kept and the absorbed count. -/
theorem Zonotope.aux_reduceByBasisCost_mono {q q' r r' : ℕ} (n : ℕ) (inv : Cost) (hq : q ≤ q')
    (hr : r ≤ r') : -- --- CONCL ---
    Zonotope.aux_reduceByBasisCost n q r inv ≤
      Zonotope.aux_reduceByBasisCost n q' r' inv := by -- --- PROOF ---
  have := Nat.mul_le_mul_right (2 * n * n) hr
  have := Nat.mul_le_mul_left n hr
  have := Nat.mul_le_mul_left n hq
  simp only [Zonotope.aux_reduceByBasisCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul, Cost.matVec]
  nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the generator count. -/
theorem Zonotope.reducePCACost_mono {h h' : ℕ} (n : ℕ) (eig inv : Cost)
    (hle : h ≤ h') : -- --- CONCL ---
    Zonotope.reducePCACost n h eig inv ≤
      Zonotope.reducePCACost n h' eig inv := by -- --- PROOF ---
  have a := Cost.sort_mono hle
  have b := Zonotope.aux_reduceByBasisCost_mono n inv hle hle
  have c := Nat.mul_le_mul_right (4 * n + 2) hle
  have d := Nat.mul_le_mul_left (2 * (n * n)) hle
  simp only [Zonotope.reducePCACost, Cost.le_iff, Cost.ops_add] at a b ⊢
  have e : 2 * (n * n * h) = 2 * (n * n) * h := by ring
  have f : 2 * (n * n * h') = 2 * (n * n) * h' := by ring
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
