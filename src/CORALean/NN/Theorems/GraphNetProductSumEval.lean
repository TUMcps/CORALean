module

public import CORALean.NN.Operations.GraphNetProductSum
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `GraphNet.productSum` is the sum of the products

With `y = A x + a`, output `j` of the network is `∑ᵢ S_j,i y_i y_{k+i}`: the product layer
zeroes the second half, so the sums read the products alone. For `C = P Q` this is `∑ₜ P_rt Q_ts`.

## Inputs
* `A` – the factors' maps
* `a` – the factors' offsets
* `S` – the sums of the products
* `x` – the point the network reads

## Hypotheses
* none

## Conclusion
* the network's output is the sum of the products
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {k n o : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The latest output of `cons x e` is `x`. -/
private theorem GraphNet.aux_cons_zero {V : ℕ → Type} {Γ : List ℕ} {m : ℕ} (x : V m)
    (e : GraphEnv V Γ) (h : 0 < (m :: Γ).length) : GraphEnv.cons x e ⟨0, h⟩ = x := rfl

/-- The earlier outputs of `cons x e` are `e`'s. -/
private theorem GraphNet.aux_cons_succ {V : ℕ → Type} {Γ : List ℕ} {m : ℕ} (x : V m)
    (e : GraphEnv V Γ) (i : ℕ) (h : i + 1 < (m :: Γ).length) :
    GraphEnv.cons x e ⟨i + 1, h⟩ = e ⟨i, Nat.lt_of_succ_lt_succ h⟩ := rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem GraphNet.productSum_eval (A : Mat ℝ (k + k) n) (a : Vec ℝ (k + k)) (S : Mat ℝ o (k + k))
    (x : Vec ℝ n) : -- --- CONCL ---
    (GraphNet.productSum A a S).eval (GraphEnv.cons x fun i => i.elim0) = fun j =>
      ∑ i : Fin k, S j (Fin.castAdd k i) * ((A *ᵥ x + a) (Fin.castAdd k i)
        * (A *ᵥ x + a) (Fin.natAdd k i)) := by -- --- PROOF ---
  funext j
  simp only [GraphNet.eval, GraphNet.productSum, GraphLayer.preact, GraphAct.apply,
    GraphNet.aux_cons_zero, List.map_nil, List.sum_nil, add_zero]
  -- the second half of the products is zero
  erw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, mul_zero, Finset.sum_const_zero, add_zero]
  simp [Matrix.mulVec, dotProduct]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
