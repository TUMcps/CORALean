module

public import CORALean.ContSet.Taylm.Real.Operations.Basic

@[expose] public section

/-!
# `Taylm.getSyms` is the polynomial part

`getSyms` is the model's polynomial `poly` (`rfl`), and a function the model encloses lies
within the remainder interval of it, at every point of the box: `getSyms` is the model with
the remainder dropped, and the remainder is what separates it from the enclosed function.

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `t` – point

## Hypotheses
* `h` – the model encloses the function
* `ht` – point lies in the unit box

## Conclusion
* the function value lies between the polynomial plus remainder ends
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.getSyms_mem {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) {t : Vec ℝ n}
    (ht : t ∈ Taylm.box n) :
    T.getSyms t + T.rem.inf ≤ f t ∧ f t ≤ T.getSyms t + T.rem.sup := by
  obtain ⟨h1, h2⟩ := h t ht
  have hp : T.getSyms t = T.poly t := rfl
  rw [hp]
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
