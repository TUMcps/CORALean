module

public import CORALean.ContSet.Zonotope.Real.Operations.FacetNormal

@[expose] public section

/-!
# [1, Thm. 2]'s normals up to sign under a reordering of the selection

Reordering the `n` generators a selection holds changes the cross product by the permutation's
sign, so every pairing with it keeps its absolute value. This is what lets one canonical ordering of
a generator subset stand for all of its `n!` selections.

## Inputs
* `n` – dimension minus one
* `Z` – zonotope
* `S` – selected generator indices
* `σ` – permutation of the selection
* `y` – vector

## Hypotheses
* none

## Conclusion
* permuting the selection leaves the absolute dot product unchanged

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794, 2015.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Permuting the selection scales `Z.facetNormal` by a sign, so `|y ⬝ᵥ ·|` is unchanged. -/
theorem Zonotope.abs_dot_facetNormal_comp_perm {n : ℕ} (Z : Zonotope (Vec ℝ (n + 1)))
    (S : Fin n → Fin Z.h) (σ : Equiv.Perm (Fin n)) (y : Vec ℝ (n + 1)) : -- --- CONCL ---
    |y ⬝ᵥ Z.facetNormal (S ∘ σ)| = |y ⬝ᵥ Z.facetNormal S| := by -- --- PROOF ---
  unfold Zonotope.facetNormal
  -- pairing with the cross product is a determinant with `y` prepended
  have e : ∀ T : Fin n → Fin Z.h, y ⬝ᵥ nCross (Matrix.of fun i j => Z.G (T j) i)
      = (Matrix.of fun i => Fin.cons (y i) (fun j => Z.G (T j) i)
        : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det :=
    fun T => dotProduct_nCross _ _
  rw [e, e]
  -- the permuted selection is the same matrix at a column permutation fixing the first
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i => Fin.cons (y i) (fun j => Z.G (S j) i) with hM
  have hτ : (Matrix.of fun i => Fin.cons (y i) (fun j => Z.G ((S ∘ σ) j) i)
      : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      = M.submatrix id (Equiv.Perm.decomposeFin.symm (0, σ)) := by
    ext i k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [hM]
    · simp [hM, Equiv.Perm.decomposeFin_symm_apply_succ]
  -- a permutation's sign has absolute value one
  rw [hτ, Matrix.det_permute', abs_mul]
  have : |((Equiv.Perm.sign (Equiv.Perm.decomposeFin.symm (0, σ)) : ℤˣ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.Perm.decomposeFin.symm (0, σ))) with h | h
    <;> simp [h]
  rw [this, one_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
