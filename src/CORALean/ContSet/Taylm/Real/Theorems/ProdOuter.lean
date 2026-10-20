module

public import CORALean.ContSet.Taylm.Real.Operations.Prod
public import CORALean.ContSet.Taylm.Real.Theorems.TimesOuter

@[expose] public section

/-!
# `Taylm.prod` encloses the product

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the product model encloses the product of the functions
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.prod_outer : ∀ {m : ℕ} {T : Fin (m + 1) → Taylm n} {f : Fin (m + 1) → Vec ℝ n → ℝ},
    (∀ i, (T i).Encloses (f i)) →
    (Taylm.prod T).Encloses fun t => ∏ i, f i t := by -- --- PROOF ---
  intro m
  induction m with
  | zero => intro T f h; simpa [Taylm.prod] using h 0
  | succ m ih =>
    intro T f h
    have := Taylm.times_outer (ih (T := fun i => T i.castSucc) (f := fun i => f i.castSucc)
      fun i => h i.castSucc) (h (Fin.last _))
    simpa only [Taylm.prod, Fin.prod_univ_castSucc] using this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
