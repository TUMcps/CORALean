import CORALean.ContSet.Zonotope.Real.Theorems.BoxSTight

/-!
# `Box_S(Z)` meets a guard whose normal is in `S` exactly when `Z` does

[1, Prop. 3]: with `Ω̄ᵢ = Box_S(Ωᵢ)` and the guard `G_e = {x | n_e·x = f_e}`, if `n_e ∈ S`
then `Ω̄ᵢ` intersects `G_e` if and only if `Ωᵢ` does. Stated for any zonotope `Z`,
which is what `Ωᵢ` is (`LinearSysDT.glmReach_eq`). A point of `Box_S(Z)` on `G_e` puts
`f_e` between `m_{n_e}` and `M_{n_e}`, and `Z`, being convex, reaches every value between
the two (`Zonotope.inter_hyperplane_iff`); the converse is `Z ⊆ Box_S(Z)`.

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3]: for `n_e ∈ S`, `Box_S(Z) ∩ G_e ≠ ∅ ⟺ Z ∩ G_e ≠ ∅`. -/
theorem Zonotope.boxS_inter_hyperplane_iff (Z : Zonotope (Vec ℝ n)) {S : Finset (Vec ℝ n)}
    {nₑ : Vec ℝ n} (hnₑ : nₑ ∈ S) (fₑ : ℝ) :
    (∃ x ∈ Z.boxS S, x ⬝ᵥ nₑ = fₑ) ↔ ∃ x ∈ Z.construct, x ⬝ᵥ nₑ = fₑ := by -- --- PROOF ---
  constructor
  · -- `m_{n_e} ≤ f_e ≤ M_{n_e}`, so `Z` reaches `f_e` along `n_e`
    rintro ⟨x, hx, rfl⟩
    exact (Z.inter_hyperplane_iff nₑ _).2 (hx nₑ hnₑ)
  · -- `Z ⊆ Box_S(Z)`
    rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Z.boxS_tight S).1 hx, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
