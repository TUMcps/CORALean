import CORALean.ContDynamics.NonlinDASys.Theorems.ComposeSubsystemsExact

/-!
# The composed set is the set whose every subsystem part is in place

[1, Eq. 15]: when the matrices `Φ⁽ⁱ⁾` embed the subsystems' coordinates into the full system's
and `Υ⁽ⁱ⁾` read them back (`Υ⁽ⁱ⁾ Φ⁽ⁱ⁾ = I`, `Υ⁽ⁱ⁾ Φ⁽ʲ⁾ = 0` for `i ≠ j`, `Σ Φ⁽ⁱ⁾ Υ⁽ⁱ⁾ = I`:
a partition of the coordinates), the Minkowski sum `Φ⁽¹⁾R⁽¹⁾ ⊕ ... ⊕ Φ⁽ⁿˢ⁾R⁽ⁿˢ⁾` is exactly
`{x | ∀ i, Υ⁽ⁱ⁾ x ∈ R⁽ⁱ⁾}`, the Cartesian product of the subsystems' sets. This is the form
that `[1, Alg. 2]` tests against, `Υ⁽ⁱ⁾ R(τ_k) ⊆ Λ⁽ⁱ⁾ Û⁽ⁱ⁾`.

## References

* [1] M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets".
      IEEE Transactions on Power Systems, 29(5):2270-2280, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix Pointwise

variable {ns n : ℕ} {d : Fin ns → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 15]: for a partition `Φ`, `Υ` of the coordinates, the composed set is
`{x | ∀ i, Υ⁽ⁱ⁾ x ∈ R⁽ⁱ⁾}`. -/
theorem NonlinDASys.composeSubsystems_eq_preimage (Φ : ∀ i, Mat ℝ n (d i))
    (Υ : ∀ i, Mat ℝ (d i) n) (hdiag : ∀ i, Υ i * Φ i = 1)
    (hoff : ∀ i j, i ≠ j → Υ i * Φ j = 0) (hsum : ∑ i, Φ i * Υ i = 1)
    (R : ∀ i, Zonotope (Vec ℝ (d i))) :
    (NonlinDASys.composeSubsystems Φ R).construct
      = {x | ∀ i, Υ i *ᵥ x ∈ (R i).construct} := by -- --- PROOF ---
  rw [NonlinDASys.composeSubsystems_exact]
  ext x
  rw [Set.mem_finsetSum]
  constructor
  · -- each part `Φ⁽ⁱ⁾ v⁽ⁱ⁾` is read back by `Υ⁽ʲ⁾` as `v⁽ʲ⁾` at `j = i` and `0` elsewhere
    rintro ⟨g, hg, rfl⟩ j
    choose v hv hvg using fun i : Fin ns => hg (Finset.mem_univ i)
    have hgv : ∀ i, g i = Φ i *ᵥ v i := fun i => (hvg i).symm
    simp_rw [hgv, Matrix.mulVec_sum, Matrix.mulVec_mulVec]
    rw [Finset.sum_eq_single j]
    · rw [hdiag j, Matrix.one_mulVec]; exact hv j
    · intro i _ hij; rw [hoff j i (Ne.symm hij), Matrix.zero_mulVec]
    · intro h; exact absurd (Finset.mem_univ j) h
  · -- `x = Σ Φ⁽ⁱ⁾ (Υ⁽ⁱ⁾ x)`
    intro hx
    refine ⟨fun i => Φ i *ᵥ (Υ i *ᵥ x), fun {i} _ => ⟨Υ i *ᵥ x, hx i, rfl⟩, ?_⟩
    calc ∑ i, Φ i *ᵥ (Υ i *ᵥ x) = (∑ i, Φ i * Υ i) *ᵥ x := by
          rw [Matrix.sum_mulVec]; exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mulVec_mulVec]
      _ = x := by rw [hsum, Matrix.one_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
