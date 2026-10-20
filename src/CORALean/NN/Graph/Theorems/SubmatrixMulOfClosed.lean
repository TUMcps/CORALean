module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The matrix statement behind `[1, §4.3]`'s locality argument

[1]'s subgraph verification argues in prose that once a subgraph is closed under the message-passing
edges reaching it, restricting after one step is the same as restricting first. `hclosed` is that
closure, read off `P`: no node outside the subgraph's image sends anything into it. In practice it
is discharged by a breadth-first search over the `(κ' + 1)`-hop neighbourhood, one hop further than
the steps, because an entry of `P` depends on the degree of *both* its endpoints. It is a
**hypothesis** here, not computed: the selection owes no proof, only the enclosure does.

## Inputs
* `N` – number of nodes
* `K` – number of kept nodes
* `F` – feature width
* `P` – message-passing matrix
* `X` – node-feature matrix
* `κ` – indices of the kept nodes

## Hypotheses
* `hinj` – kept indices are distinct
* `hclosed` – the kept nodes receive nothing from outside

## Conclusion
* restricting the product equals the product of the restrictions

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Nothing outside the subgraph feeds into it, so restricting after multiplying
is multiplying the restrictions. -/
theorem GNN.submatrix_mul_of_closed {N K F : ℕ} (P : Mat ℝ N N) (X : Mat ℝ N F)
    (κ : Fin K → Fin N) (hinj : Function.Injective κ)
    (hclosed : ∀ k i, (∀ l, κ l ≠ i) → P (κ k) i = 0) :
    (P * X).submatrix κ id = P.submatrix κ κ * X.submatrix κ id := by -- --- PROOF ---
  funext k j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id_eq]
  -- nothing outside the subgraph's image contributes, so the sum needs only that image
  have hcut : ∑ i, P (κ k) i * X i j = ∑ i ∈ Finset.univ.image κ, P (κ k) i * X i j := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
    have hnot : ∀ l, κ l ≠ i := fun l hl =>
      hi (Finset.mem_image.mpr ⟨l, Finset.mem_univ l, hl⟩)
    rw [hclosed k i hnot, zero_mul]
  -- inside that image, `κ` is a faithful reindexing: shrink the sum to the subgraph's own
  rw [hcut, Finset.sum_image hinj.injOn]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
