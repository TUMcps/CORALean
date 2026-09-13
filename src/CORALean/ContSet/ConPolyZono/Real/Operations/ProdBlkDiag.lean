import CORALean.ContSet.ConPolyZono.Real.Operations.BlkDiag

/-!
# The monomial of a block-diagonal column

A column of `blkDiag` reads only the factors of its own block — every other
block sits at exponent zero — so the monomial it names is the original matrix's,
over that block's factors. This is what makes the `a` copies of [1, Prop. 9]
independent of each other rather than one set of factors shared `a` ways.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A product over `a` blocks of `r`, as a product of products. -/
theorem ConPolyZono.aux_prod_rep {M : Type} [CommMonoid M] {a r : ℕ} (F : Fin (a * r) → M) :
    ∏ x, F x = ∏ j : Fin a, ∏ k : Fin r, F (finProdFinEquiv (j, k)) := by
  rw [← Equiv.prod_comp finProdFinEquiv F, Fintype.prod_prod_type]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Block `j`'s column of `blkDiag E` names `E`'s column over block `j`'s own
factors. -/
theorem ConPolyZono.prod_blkDiag {a p h : ℕ} (E : Fin p → Fin h → ℕ) (v : Fin (a * p) → ℝ)
    (j : Fin a) (i : Fin h) :
    (∏ x, v x ^ ConPolyZono.blkDiag a E x (finProdFinEquiv (j, i)))
      = ∏ k, v (finProdFinEquiv (j, k)) ^ E k i := by -- --- PROOF ---
  rw [ConPolyZono.aux_prod_rep (fun x => v x ^ ConPolyZono.blkDiag a E x (finProdFinEquiv (j, i)))]
  refine (Finset.prod_eq_single j (fun j' _ hj' => ?_)
    (fun h => absurd (Finset.mem_univ j) h)).trans ?_
  -- off the diagonal the whole block sits at exponent zero
  · exact Finset.prod_eq_one fun k _ => by simp [ConPolyZono.blkDiag, hj']
  · exact Finset.prod_congr rfl fun k _ => by simp [ConPolyZono.blkDiag]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
