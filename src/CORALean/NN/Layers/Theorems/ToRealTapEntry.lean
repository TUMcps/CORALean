import CORALean.Global.Float.Instances.Real.Instances
import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.NN.Layers.Operations.TapEntry

/-!
# A stencil entry reads back exactly

`if` commutes with `toReal`, and the recursion does nothing else, so the entry a machine
scalar stores reads as the entry the same recursion builds over ℝ from the weights read in:
an equality, with no hypothesis, which is what "a stencil rounds nowhere" means.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_tapEntry {n : ℕ} :
    ∀ {k : ℕ} (t : Fin k → Fin n) (v : Fin k → 𝕋) (i : Fin n),
      toReal (tapEntry t v i) = tapEntry t (fun l => toReal (v l)) i := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro _ _ _; exact toReal_zero
  | succ k ih =>
    intro t v i
    show toReal (if t 0 = i then v 0 else tapEntry (fun l => t l.succ) (fun l => v l.succ) i)
      = (if t 0 = i then toReal (v 0)
        else tapEntry (fun l => t l.succ) (fun l => toReal (v l.succ)) i)
    by_cases hi : t 0 = i
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi]
      exact ih _ _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
