module

public import CORALean.NN.Operations.CatMaxSegments

@[expose] public section

/-!
# Max pooling as a CAT function

[1, Sec. II (MaxPool to CAT)]: `MaxPool' = f_{mn r/(pq)} ∘ … ∘ f₁ ∘ f^MP`. `f^MP` is the
selection matrix bringing each window's `k + 1` coordinates together, window `j` at positions
`j (k + 1), …, j (k + 1) + k`, then `Cat.maxSegments` pools them one window at a time, and an
identity renames `0 + m` coordinates to `m`. The windows are any stencil `tap`, as for
`Layer.maxPool`; the paper's Appendix A's `p × q` blocks of an `m × n × r` image are one, its
`W^MP` a permutation because they partition the image, which nothing here needs.

## Inputs
* `tap` – input index of every window position

## Output
* CAT function pooling the windows by their maximum

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `MaxPool'`: reorder by `f^MP`, then pool window after window. -/
def Cat.maxPool (tap : Fin m → Fin (k + 1) → Fin n) : Cat 𝕋 n m :=
  let fMP : Cat 𝕋 n (0 + (k + 1) * m) := .affine (selectMat fun i =>
      tap ⟨i.val / (k + 1), Nat.div_lt_of_lt_mul (by have := i.isLt; omega)⟩
        ⟨i.val % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩) fun _ => zero
  let pool := Cat.maxSegments k 0 m
  let rename : Cat 𝕋 (0 + m) m := .affine (selectMat fun i => ⟨i.val, by omega⟩) fun _ => zero
  .comp rename (.comp pool fMP)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
