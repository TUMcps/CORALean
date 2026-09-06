import CORALean.NN.Graph.Subgraph

/-!
# The matrix statement behind `[1, §4.3]`'s locality argument

[1]'s subgraph verification argues in prose that once a subgraph is closed under the
message-passing edges reaching it, restricting after one step of message passing is the
same as restricting first and passing messages on the restriction alone. `hclosed` is
that closure, read off `P`: no node outside the subgraph's image sends anything into it.

In practice `hclosed` is discharged by a breadth-first search over the `(κ' + 1)`-hop
neighbourhood of the subgraph, `κ'` the number of message-passing steps still to run —
one hop further than the steps themselves, because an entry of `P` depends on the degree
of *both* its endpoints, so bounding `P` on a ball needs the ring just past it.

Left a **hypothesis** here rather than computed, which matches the rest of the library:
`neuronMerging_sandwich_outer` is sound at every bucket, `ConPolyZono.reduceBy_outer` at
every partition, `Relaxation.ofDeriv` at every slope inside its bracket — the selection
owes no proof, only the enclosure does. The *radius-indexed* form of this fact — a ball
of radius `κ' + 1` suffices for `κ'` steps — needs a notion of graph distance this file
does not have, and stays out of scope for that reason, not as an oversight.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


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
