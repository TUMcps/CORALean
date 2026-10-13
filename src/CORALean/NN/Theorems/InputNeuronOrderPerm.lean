module

public import CORALean.NN.Operations.InputNeuronOrder
public import CORALean.NN.Theorems.SnakeOrderMultiset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# `getInputNeuronOrder` ranks every input neuron once

The result is a permutation of `0, …, K - 1`, `K` the number of neurons ranked (`n`, or `h * w`
given an `inputSize`): none left out, none repeated. For `snake` that is the spiral visiting each
cell of the image once, whatever its shape; for `sensitivity` it is that a sort permutes. The order
itself, which neuron goes first, is not claimed here: it is `inOrder`'s by definition, and the
spiral's and the sort's by their own definitions. `snake` needs an `inputSize`, as CORA does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Finset


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `range N` as a multiset is the sum of the singletons below `N`. -/
private theorem aux_coe_range (N : ℕ) :
    ((List.range N : List ℕ) : Multiset ℕ) = ∑ k ∈ range N, ({k} : Multiset ℕ) := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, Finset.sum_range_succ, ← ih]; rfl

/-- The column-major numbering of an `h × w` grid is a bijection onto `range (h * w)`. -/
private theorem aux_grid_perm (h w : ℕ) :
    (∑ p : Fin h × Fin w, ({(p.1 : ℕ) + h * p.2} : Multiset ℕ)) =
      ((List.range (h * w) : List ℕ) : Multiset ℕ) := by
  rw [aux_coe_range, mul_comm h w, ← Fin.sum_univ_eq_sum_range (fun k => ({k} : Multiset ℕ))]
  exact Fintype.sum_equiv ((Equiv.prodComm _ _).trans finProdFinEquiv) _ _ fun p => rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem getInputNeuronOrder_perm {n m : ℕ} (c : Chain n m) (method : InputOrderMethod)
    (x : Vec ℝ n) (sz : Option (ℕ × ℕ × ℕ))
    (hs : method = .snake → sz.isSome = true) :
    (getInputNeuronOrder c method x sz).Perm
      (List.range (match sz with | none => n | some (h, w, _) => h * w)) := by -- --- PROOF ---
  -- one case per method and per shape of `inputSize`
  rcases sz with _ | ⟨h, w, ch⟩ <;> cases method <;>
    simp only [getInputNeuronOrder] <;> try exact List.Perm.refl _
  · exact List.mergeSort_perm _ _
  · simp at hs
  · exact List.mergeSort_perm _ _
  · -- the spiral is a rearrangement of the grid, which is the range
    rw [← Multiset.coe_eq_coe, snakeOrder_coe]
    exact aux_grid_perm h w

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
