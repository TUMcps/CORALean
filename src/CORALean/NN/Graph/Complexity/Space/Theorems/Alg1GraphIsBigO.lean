module

public import CORALean.NN.Graph.Complexity.Space.Theorems.Alg1GraphCountLe
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Prod

@[expose] public section

/-!
# [1, Thm. 1 (generators)]: `Alg. 1` is `O(h_e^(3κ') (h_x + |N| c_max) + (κ - 2κ') n_max)`

`alg1Graph_count_le` read as the theorem states it, the number `m` of uncertain edges and the number
`h_x` of the input's generators both growing, the graph and the network fixed: with `ν = |N| c_max`
the neurons an activation of the graph layers adds at most, the count is at most `C (m^(3κ')
(h_x + ν) + E)` with `C = K^κ' (κ' + 2) + 1`, `E` the most the layers after the pooling add. The
`h_x` of the statement is `X.h + X.q`.

## Inputs
* `R` – relaxation of the activations
* `A` – adjacency matrix
* `U` – uncertain edges for each edge count
* `L` – number of graph layers
* `T` – number of layers after the pooling
* `c` – layer widths
* `cmax` – widest hidden layer
* `W` – graph layer weights
* `acts` – activation layers
* `f` – enclosure maps of the later layers
* `e` – generators each later layer adds at most
* `X` – input zonotopes, one for each generator count

## Hypotheses
* `hc` – hidden widths are at most cmax
* `hadd` – each graph activation adds at most N · c neurons
* `hf` – later layer t adds at most e t generators
* `hX` – the k-th input has k generators

## Conclusion
* generator count of the output is big-O of the stated bound in edges and input generators

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The count against the printed bound, for one uncertain-edge count and one input size. -/
private theorem aux_alg1Graph_le_bound (K L ν E μ k y : ℕ) (hk : 1 ≤ k)
    (h : y + 1 ≤ K ^ L * μ ^ (3 * L) * (k + 1 + L * ν) + E) : -- --- CONCL ---
    y ≤ (K ^ L * (L + 2) + 1) * (μ ^ (3 * L) * (k + ν) + E) := by -- --- PROOF ---
  -- `k + 1 + L ν ≤ (L + 2)(k + ν)` once there is an input generator
  have h1 : k + 1 + L * ν ≤ (L + 2) * (k + ν) := by nlinarith
  have h2 : K ^ L * μ ^ (3 * L) * (k + 1 + L * ν) ≤ K ^ L * (L + 2) * (μ ^ (3 * L) * (k + ν)) := by
    calc K ^ L * μ ^ (3 * L) * (k + 1 + L * ν)
        ≤ K ^ L * μ ^ (3 * L) * ((L + 2) * (k + ν)) := Nat.mul_le_mul (le_refl _) h1
      _ = K ^ L * (L + 2) * (μ ^ (3 * L) * (k + ν)) := by ring
  have h3 : y ≤ K ^ L * (L + 2) * (μ ^ (3 * L) * (k + ν)) + E := by omega
  calc y ≤ K ^ L * (L + 2) * (μ ^ (3 * L) * (k + ν)) + E := h3
    _ ≤ (K ^ L * (L + 2) + 1) * (μ ^ (3 * L) * (k + ν) + E) := by
        nlinarith [Nat.zero_le (μ ^ (3 * L) * (k + ν)), Nat.zero_le (K ^ L * (L + 2) * E)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1 (generators)]: the output of `Alg. 1` has `O(m^(3κ') (h_x + |N| c_max) + E)`
generators. -/
theorem GNN.alg1Graph_isBigO (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : ∀ μ : ℕ, Fin μ → Fin N × Fin N) (L T : ℕ) (c : ℕ → ℕ) (cmax : ℕ)
    (hc : ∀ s, s < L → c (s + 1) ≤ cmax) (W : ∀ s, Mat ℝ (c s) (c (s + 1)))
    (acts : ∀ s, GNN.ActLayer N (c (s + 1)))
    (hadd : ∀ s, s < L → (acts s).AddsAtMost (N * c (s + 1)))
    (f : ∀ t, PolyZonotope (Vec ℝ (c (L + t))) → PolyZonotope (Vec ℝ (c (L + (t + 1)))))
    (e : ℕ → ℕ) (hf : ∀ t S, (f t S).h + (f t S).q ≤ S.h + S.q + e t)
    (X : ℕ → PolyZonotope (Mat ℝ N (c 0))) (hX : ∀ k, (X k).h + (X k).q = k) : -- --- CONCL ---
    (fun x : ℕ × ℕ =>
        (((GNN.alg1Graph R A (U x.1) L T c W acts f (X x.2)).h
          + (GNN.alg1Graph R A (U x.1) L T c W acts f (X x.2)).q : ℕ) : ℝ))
      =O[Filter.atTop] fun x : ℕ × ℕ =>
        ((x.1 ^ (3 * L) * (x.2 + N * cmax)
          + ∑ t ∈ Finset.range T, e t : ℕ) : ℝ) := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound
    ((((N + 2) * (N + 2) + 1) * (N + 2) + 2) ^ L * (L + 2) + 1 : ℕ)
  filter_upwards [Filter.eventually_ge_atTop ((1, 1) : ℕ × ℕ)] with x hx
  have hμ : 1 ≤ x.1 := hx.1
  have hk : 1 ≤ x.2 := hx.2
  -- the neurons an activation adds are at most `|N| c_max`
  have hadd' : ∀ s, s < L → (acts s).AddsAtMost (N * cmax) := fun s hs S =>
    (hadd s hs S).trans (by have := hc s hs; gcongr)
  have hcount := GNN.alg1Graph_count_le R A (U x.1) hμ L T c W acts (N * cmax) hadd' f e hf (X x.2)
  rw [hX] at hcount
  have hbound := aux_alg1Graph_le_bound _ L (N * cmax) _ x.1 x.2 _ hk hcount
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast hbound

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
