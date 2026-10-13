import CORALean.NN.Layers.Operations.TapEntry

/-!
# An input no tap reads gets weight zero

The recursion runs off the end of the kernel without matching, and returns the stored `zero`.
This is what makes the first tap's weight vanish from the rest of a row when the taps are
injective.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem tapEntry_eq_zero {n : ℕ} :
    ∀ {k : ℕ} (t : Fin k → Fin n) (v : Fin k → 𝕋) (i : Fin n),
      (∀ l, t l ≠ i) → tapEntry t v i = zero := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro _ _ _ _; rfl
  | succ k ih =>
    intro t v i h
    show (if t 0 = i then v 0 else tapEntry (fun l => t l.succ) (fun l => v l.succ) i) = zero
    rw [if_neg (h 0)]
    exact ih _ _ _ fun l => h l.succ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
