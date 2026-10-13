import CORALean.ContSet.Zonotope.Real.Operations.ReducePCA
import CORALean.ContSet.Zonotope.Real.Cost.ReduceGirard
import CORALean.ContSet.Zonotope.Real.Cost.ReduceByBasis

/-!
# `Zonotope.reducePCACost`

Asserted, not proved, by reading `Operations/ReducePCA.lean`. Girard's partition
as in `reduceGirardCost` (metrics and sort); the scatter matrix `G Gᵀ` of the
dropped block, `n * n` entries of `2 * r` operations, bounded at `r = h`; the
eigendecomposition behind `pcaBasis`, which the definition takes from Mathlib's
`eigenvectorUnitary` and so fixes no algorithm for — its price `eig` is a
parameter, as is the inverse's inside `reduceByBasisCost`. A caller who runs a
dense symmetric solver would pass an `O(n^3)` count for each. At order `o`
or below the operation is the identity, so this bounds every `o` at once.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.reducePCA` costs at `Vec ℝ n` on `h` generators, the
eigendecomposition costing at most `eig` and the basis inverse at most `inv`. -/
def Zonotope.reducePCACost (n h : ℕ) (eig inv : Cost) : Cost :=
  ⟨h * (4 * n + 2)⟩ + Cost.sort h + ⟨2 * (n * n * h)⟩ + eig + Zonotope.reduceByBasisCost n h inv

/-- Monotone in the generator count. -/
theorem Zonotope.reducePCACost_mono {h h' : ℕ} (n : ℕ) (eig inv : Cost) (hle : h ≤ h') :
    Zonotope.reducePCACost n h eig inv ≤
      Zonotope.reducePCACost n h' eig inv := by -- --- PROOF ---
  have a := Cost.sort_mono hle
  have b := Zonotope.reduceByBasisCost_mono n inv hle
  have c := Nat.mul_le_mul_right (4 * n + 2) hle
  have d := Nat.mul_le_mul_left (2 * (n * n)) hle
  simp only [Zonotope.reducePCACost, Cost.le_iff, Cost.ops_add] at a b ⊢
  have e : 2 * (n * n * h) = 2 * (n * n) * h := by ring
  have f : 2 * (n * n * h') = 2 * (n * n) * h' := by ring
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
