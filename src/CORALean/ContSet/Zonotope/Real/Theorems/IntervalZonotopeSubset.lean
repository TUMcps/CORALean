module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Real.Operations.IsNonempty

@[expose] public section

/-!
# The zonotope of a box is the box, when the bounds do not cross

`Interval_to_Zonotope` run backwards, which holds exactly when the bounds do not cross: only
generator `i` reaches coordinate `i`, so `|β i| ≤ 1` puts the coordinate within its own radius of
its own center.

## Inputs
* `I` – interval

## Hypotheses
* `hI` – interval nonempty

## Conclusion
* the zonotope of the interval lies in the interval
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.zonotope_subset_of_isNonempty {I : Interval (Vec ℝ n)}
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
  -- and the center plus that offset is exactly where `Interval.construct` asks it to be
  show I.inf i ≤ ((fun i => (I.inf i + I.sup i) / 2 : Vec ℝ n) + ∑ j : Fin n, β j •
      (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i ∧
    ((fun i => (I.inf i + I.sup i) / 2 : Vec ℝ n) + ∑ j : Fin n, β j •
      (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i ≤ I.sup i
  rw [Pi.add_apply, hsum]
  exact ⟨by linarith, by linarith⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
