import CORALean.ContSet.Zoo.Real.Operations.OfInterval
import Mathlib.Tactic.Linarith

/-!
# `Zoo.ofInterval` encloses the coordinate

Both members enclose the map the domain's `i`-th variable stands for, `mid + rad · tᵢ` on
the normalized box, which ranges over `[inf i, sup i]`; for a nonempty coordinate interval.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.ofInterval_encloses (I : Interval (Vec ℝ n)) (N : ℕ) (i : Fin n)
    (hI : I.inf i ≤ I.sup i) :
    (Zoo.ofInterval I N i).Encloses fun t => (I.inf i + I.sup i) / 2 + (I.sup i - I.inf i) / 2 * t i
    := by -- --- PROOF ---
  refine ⟨fun T hT => ?_, fun J hJ t ht => ?_⟩
  · obtain rfl : I.taylm N i = T := Option.some.inj hT
    exact Interval.taylm_outer I N i
  · obtain rfl : (⟨fun _ => I.inf i, fun _ => I.sup i⟩ : Interval (Vec ℝ 1)) = J :=
      Option.some.inj hJ
    have h1 := abs_le.1 (ht i)
    have hr : 0 ≤ (I.sup i - I.inf i) / 2 := by linarith
    intro k
    constructor
    · show I.inf i ≤ (I.inf i + I.sup i) / 2 + (I.sup i - I.inf i) / 2 * t i
      nlinarith
    · show (I.inf i + I.sup i) / 2 + (I.sup i - I.inf i) / 2 * t i ≤ I.sup i
      nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
