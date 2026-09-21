import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Interval.Real.Operations.IsNonempty
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

/-!
# `Zonotope.plus` at a box is exact, [1, Prop. 2]

[1]'s Prop. 2 prints an *identity*, `Z ⊕ I = ⟨c + c_I, [G  Diag((u-l)/2)]⟩_Z`, and a
box really is a zonotope, so `PlusIntervalOuter`'s inclusion is not the whole claim.
The one hypothesis is `I.IsNonempty`: `Interval.zonotope` is the box with its bounds
swapped where they cross, and the swapped box is not empty, so without it the right
side is strictly larger than an empty left side.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The conversion of `Interval_to_Zonotope` run backwards, which holds exactly when the
bounds do not cross: only generator `i` reaches coordinate `i`, so `|β i| ≤ 1` puts the
coordinate within its own radius of its own centre. -/
theorem aux_zonotope_subset_of_isNonempty {I : Interval (Vec ℝ n)}
    (hI : I.IsNonempty (ι := Fin n)) : I.zonotope.construct ⊆ I.construct := by -- --- PROOF ---
  rintro x ⟨β, hβ, rfl⟩
  intro i
  -- only the diagonal generator `i` contributes to coordinate `i`
  have hsum : (∑ j : Fin n, β j •
        (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i
      = β i * ((I.sup i - I.inf i) / 2) := by
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp only [Pi.smul_apply, smul_eq_mul, if_neg (Ne.symm hj), mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ i) hc
  -- the coefficient can move the coordinate by at most the radius, either way
  have hIi : I.inf i ≤ I.sup i := hI i
  have hrad : 0 ≤ (I.sup i - I.inf i) / 2 := by linarith
  have habs := abs_le.mp (hβ i)
  have hlo : -((I.sup i - I.inf i) / 2) ≤ β i * ((I.sup i - I.inf i) / 2) := by
    nlinarith [habs.1, hrad]
  have hhi : β i * ((I.sup i - I.inf i) / 2) ≤ (I.sup i - I.inf i) / 2 := by
    nlinarith [habs.2, hrad]
  -- and the centre plus that offset is exactly where `Interval.construct` asks it to be
  show I.inf i ≤ ((fun i => (I.inf i + I.sup i) / 2 : Vec ℝ n) + ∑ j : Fin n, β j •
      (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i ∧
    ((fun i => (I.inf i + I.sup i) / 2 : Vec ℝ n) + ∑ j : Fin n, β j •
      (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i ≤ I.sup i
  rw [Pi.add_apply, hsum]
  exact ⟨by linarith, by linarith⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: a zonotope plus a box *is* the zonotope that concatenates the box's own
generators onto it — an identity, not merely an enclosure. -/
theorem Zonotope.plus_interval_exact (Z : Zonotope (Vec ℝ n)) {I : Interval (Vec ℝ n)}
    (hI : I.IsNonempty (ι := Fin n)) :
    Z.construct + I.construct = (Z.plus I.zonotope).construct := by
  rw [← Zonotope.plus_exact]
  exact congrArg (Z.construct + ·)
    (Set.Subset.antisymm (Interval.zonotope_contains I) (aux_zonotope_subset_of_isNonempty hI))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
