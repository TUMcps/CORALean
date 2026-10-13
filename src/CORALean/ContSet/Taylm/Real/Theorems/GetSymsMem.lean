import Mathlib.Tactic.Linarith
import CORALean.ContSet.Taylm.Real.Operations.GetSyms

/-!
# `Taylm.getSyms` is the polynomial part

`getSyms` is the model's polynomial `poly` (`rfl`), and a function the model encloses lies
within the remainder interval of it, at every point of the box: `getSyms` is the model with
the remainder dropped, and the remainder is what separates it from the enclosed function.
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
    T.getSyms t + T.remInf ≤ f t ∧ f t ≤ T.getSyms t + T.remSup := by
  obtain ⟨h1, h2⟩ := h t ht
  have hp : T.getSyms t = T.poly t := rfl
  rw [hp]
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
