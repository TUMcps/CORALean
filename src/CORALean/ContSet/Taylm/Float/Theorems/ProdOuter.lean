import CORALean.ContSet.Taylm.Float.Operations.Prod
import CORALean.ContSet.Taylm.Float.Theorems.TimesOuter

/-!
# `Taylm.prod` encloses the product
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.prod_outer :
    ∀ {m : ℕ} {T : Fin (m + 1) → Taylm 𝕋 n} {f : Fin (m + 1) → Vec ℝ n → ℝ},
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
