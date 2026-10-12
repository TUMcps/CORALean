import CORALean.ContSet.Zonotope.Real.Operations.BoxS
import CORALean.ContSet.Zonotope.Real.Theorems.InterHyperplaneIff

/-!
# `Box_S(Z)` encloses `Z` and every face of it touches `Z`

[1, Prop. 2]: `Box_S(Z)` is an over-approximation of `Z`, and each face of it has at
least one common point with `Z`: for every `s ∈ S` some point of `Z` has `s·x = m_s` and
some has `s·x = M_s`. Both halves are the two directions of
`Zonotope.inter_hyperplane_iff`: a value is reached along `s` exactly when it lies
between `m_s` and `M_s`. The paper's witnesses are `u ∓ Σⱼ sign(s·vⱼ)vⱼ`.

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: `Z ⊆ Box_S(Z)`, and along each `s ∈ S` both bounds are attained in `Z`. -/
theorem Zonotope.boxS_tight (Z : Zonotope (Vec ℝ n)) (S : Finset (Vec ℝ n)) :
    Z.construct ⊆ Z.boxS S ∧
      ∀ s ∈ S, (∃ x ∈ Z.construct, x ⬝ᵥ s = Z.c ⬝ᵥ s - ∑ j, |Z.G j ⬝ᵥ s|) ∧
        ∃ x ∈ Z.construct, x ⬝ᵥ s = Z.c ⬝ᵥ s + ∑ j, |Z.G j ⬝ᵥ s| := by -- --- PROOF ---
  have h0 : ∀ s : Vec ℝ n, 0 ≤ ∑ j, |Z.G j ⬝ᵥ s| := fun s =>
    Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨fun x hx s _ => ?_, fun s _ => ⟨?_, ?_⟩⟩
  · -- the value of `x` along `s` is one `Z` reaches, so it lies between the bounds
    exact (Z.inter_hyperplane_iff s (x ⬝ᵥ s)).1 ⟨x, hx, rfl⟩
  · -- each bound lies between the bounds, so it is reached
    exact (Z.inter_hyperplane_iff s _).2 ⟨le_rfl, by linarith [h0 s]⟩
  · exact (Z.inter_hyperplane_iff s _).2 ⟨by linarith [h0 s], le_rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
