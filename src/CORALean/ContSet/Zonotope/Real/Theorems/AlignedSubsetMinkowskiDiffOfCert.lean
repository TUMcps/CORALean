import CORALean.ContSet.Zonotope.Real.Operations.Aligned
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.SubsetOfCert
import CORALean.ContSet.ContSet.Theorems.SubsetMinkowskiDiffIff

/-!
# A feasible point of (17) gives an aligned zonotope inside `Z ⊖ EW`

[1, Eq. 17], the alternative to (max-in) built on [2, Thm. 3]: for `W = (G_W, c_W)` a
zonotope, `[G_Z diag(α), E G_W] = G_Z Γ`, `c_Z - (c + E c_W) = G_Z γ` and
`‖[Γ, γ]‖∞ ≤ 1` give `(G_Z diag(α), c) ⊆ Z ⊖ EW`. The matrix `[G_Z diag(α), E G_W]`
is the generator family of the aligned zonotope plus `EW`, which is how it is
written here; `‖·‖∞` is the maximum row sum, one inequality per row. That `(17)`
maximizes `Σαᵢ` is not used.

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
* [2] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 17]: a feasible point `(Γ, γ, α, c)` puts the aligned zonotope inside the
Minkowski difference of `Z` and the image of the zonotope `W` under `E`. -/
theorem Zonotope.aligned_subset_minkowskiDiff_of_cert (Z : Zonotope (Vec ℝ n))
    (W : Zonotope (Vec ℝ p)) (E : Mat ℝ n p) (c : Vec ℝ n) (a : Fin Z.h → ℝ)
    (Γ : Mat ℝ Z.h ((Z.aligned c a).plus (W.mtimes E)).h) (γ : Vec ℝ Z.h)
    (hX : ∀ j, ((Z.aligned c a).plus (W.mtimes E)).G j = ∑ k, Γ k j • Z.G k)
    (hγ : Z.c - (c + E *ᵥ W.c) = ∑ k, γ k • Z.G k) (hn : ∀ k, ∑ j, |Γ k j| + |γ k| ≤ 1) :
    (Z.aligned c a).construct
      ⊆ minkowskiDiff Z.construct ((E *ᵥ ·) '' W.construct) := by
  rw [subset_minkowskiDiff_iff, Zonotope.mtimes_exact, Zonotope.plus_exact]
  -- [2, Thm. 3] at the aligned zonotope plus `EW` inside `Z`
  exact Zonotope.construct_subset_of_cert _ Z Γ γ hX hγ hn

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
