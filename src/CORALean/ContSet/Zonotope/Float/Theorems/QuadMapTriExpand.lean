module

public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapTri
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapTriPairsSplit
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The quadratic form on a zonotope, split as `Zonotope.quadMapTri` splits it

With `z₀` the center, `z₁ … z_N` the generators and `B_ab = z_aᵀ Q z_b`, the form at
`z₀ + Σⱼ pⱼ zⱼ₊₁` is `Σ_{a,b} p'_a p'_b B_ab`, `p' = (1, p)`. With `quadMapTri_pairs_split` it
is the center `B₀₀ + ½ Σₛ Bₛₛ`, the halved squares with coefficient `2pₛ² - 1` and the pairs with
coefficient `p'_r p'_j`.

## Inputs
* `Qm` – quadratic form
* `z` – the center and the generators
* `p` – factor vector

## Hypotheses
* none

## Conclusion
* the form splits into the center, the squares and the pairs
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Finset Matrix

variable {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The quadratic form at `z₀ + Σⱼ pⱼ zⱼ₊₁`: the center `B₀₀ + ½ Σₛ Bₛₛ`, the squares with
coefficient `2pₛ² - 1`, and the pairs with `pᵣ pⱼ`, `B_ab = z_aᵀ Q z_b`. -/
theorem Zonotope.quadMapTri_expand (Qm : Mat ℝ n n) (z : Fin (N + 1) → Vec ℝ n)
    (p : Fin N → ℝ) : -- --- CONCL ---
    (z 0 + ∑ j, p j • z j.succ) ⬝ᵥ (Qm *ᵥ (z 0 + ∑ j, p j • z j.succ))
      = z 0 ⬝ᵥ (Qm *ᵥ z 0) + (1 / 2) * ∑ s : Fin N, z s.succ ⬝ᵥ (Qm *ᵥ z s.succ)
        + ∑ s : Fin N, (2 * p s ^ 2 - 1) * ((1 / 2) * (z s.succ ⬝ᵥ (Qm *ᵥ z s.succ)))
        + ∑ u : Fin (Zonotope.step_quadMapTriPairs N),
            ((Fin.cons 1 p : Fin (N + 1) → ℝ) (Zonotope.step_quadMapTriRow N u) *
              (Fin.cons 1 p : Fin (N + 1) → ℝ) (Zonotope.step_quadMapTriCol N u)) *
            (z (Zonotope.step_quadMapTriRow N u) ⬝ᵥ (Qm *ᵥ z (Zonotope.step_quadMapTriCol N u))
              + z (Zonotope.step_quadMapTriCol N u) ⬝ᵥ
                (Qm *ᵥ z (Zonotope.step_quadMapTriRow N u))) := by -- --- PROOF ---
  set q : Fin (N + 1) → ℝ := Fin.cons 1 p with hq
  -- the point as a sum over the extended list
  have hx : z 0 + ∑ j, p j • z j.succ = ∑ a, q a • z a := by
    rw [Fin.sum_univ_succ]; simp [hq]
  -- the form as the double sum over the extended list
  have hB : (∑ a, q a • z a) ⬝ᵥ (Qm *ᵥ ∑ b, q b • z b)
      = ∑ a, ∑ b, (q a * q b) * (z a ⬝ᵥ (Qm *ᵥ z b)) := by
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, sum_dotProduct,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  -- the diagonal and the entries below it, then the diagonal against the center and the squares
  rw [hx, hB, Zonotope.quadMapTri_pairs_split]
  have hd : ∑ a, (q a * q a) * (z a ⬝ᵥ (Qm *ᵥ z a))
      = z 0 ⬝ᵥ (Qm *ᵥ z 0) + (1 / 2) * ∑ s : Fin N, z s.succ ⬝ᵥ (Qm *ᵥ z s.succ)
        + ∑ s : Fin N, (2 * p s ^ 2 - 1) * ((1 / 2) * (z s.succ ⬝ᵥ (Qm *ᵥ z s.succ))) := by
    rw [Fin.sum_univ_succ]
    simp only [hq, Fin.cons_zero, Fin.cons_succ, one_mul]
    rw [Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hd]
  congr 1
  refine Finset.sum_congr rfl fun u _ => by ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
