module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes

@[expose] public section

/-!
# The exact image, regrouped so the centre and each generator appear once

Over the three blocks rather than over a `PolyZonotope`, since a constrained one
has the same three and regrouping them knows nothing about a constraint. Stated
at an arbitrary coefficient vector `t` for the dependent block rather than at
`monomial pZ.E a`: the regrouping is linear algebra and knows nothing about
where the coefficients came from. It carries no `aux_` prefix and takes the
three blocks loose, the constrained representation needing the same regrouping
at its own fields.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mulVec_split {hh qq : ℕ} (M : Mat 𝕋 m n) (c : Vec 𝕋 n)
    (G : Fin hh → Vec 𝕋 n) (GI : Fin qq → Vec 𝕋 n) (t : Vec ℝ hh) (β : Vec ℝ qq) {x : Vec ℝ n}
    (hx : ∀ k, x k = toReal (c k) + (∑ l, toReal (G l k) * t l)
            + ∑ j, toReal (GI j k) * β j) (i : Fin m) :
    (toRealMat M *ᵥ x) i
      = (∑ k, toReal (M i k) * toReal (c k))
        + (∑ l, (∑ k, toReal (M i k) * toReal (G l k)) * t l)
        + ∑ j, (∑ k, toReal (M i k) * toReal (GI j k)) * β j := by -- --- PROOF ---
  -- unfold `x`, then regroup each of its three summands against the outer sum
  show ∑ k, toReal (M i k) * x k = _
  calc ∑ k, toReal (M i k) * x k
      = ∑ k, (toReal (M i k) * toReal (c k)
              + (∑ l, toReal (M i k) * toReal (G l k) * t l)
              + ∑ j, toReal (M i k) * toReal (GI j k) * β j) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hx k, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
        refine congrArg₂ _ (congrArg₂ _ rfl ?_) ?_
        · exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm
        · exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
    -- then the three sums separated, and each index swapped to the outside
    _ = (∑ k, toReal (M i k) * toReal (c k))
        + (∑ k, ∑ l, toReal (M i k) * toReal (G l k) * t l)
        + ∑ k, ∑ j, toReal (M i k) * toReal (GI j k) * β j := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ k, toReal (M i k) * toReal (c k))
        + (∑ l, (∑ k, toReal (M i k) * toReal (G l k)) * t l)
        + ∑ j, (∑ k, toReal (M i k) * toReal (GI j k)) * β j := by
        refine congrArg₂ _ (congrArg₂ _ rfl ?_) ?_
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => (Finset.sum_mul _ _ _).symm
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
