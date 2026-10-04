import CORALean.ContSet.Interval.Real.Operations.EBoxConstruct
import CORALean.ContSet.Interval.Real.Operations.Lift

/-!
# `Interval.lift_` is exact

For distinct target coordinates `proj`, the lifted box is the set of points of `ℝᴺ` whose
`proj`-coordinates lie in `I`, the others free.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.lift_exact (I : Interval (Vec ℝ m)) (N : ℕ) (proj : Fin m → Fin N)
    (hp : Function.Injective proj) :
    (I.lift_ N proj).construct = {x | (fun i => x (proj i)) ∈ I.construct} := by -- --- PROOF ---
  ext x
  simp only [Interval.EBox.construct, Interval.lift_, Set.mem_setOf_eq, Interval.construct]
  constructor
  · intro h i
    have := h (proj i)
    rw [hp.extend_apply, hp.extend_apply] at this
    exact ⟨EReal.coe_le_coe_iff.mp this.1, EReal.coe_le_coe_iff.mp this.2⟩
  · intro h j
    by_cases hj : ∃ i, proj i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hp.extend_apply, hp.extend_apply]
      exact ⟨EReal.coe_le_coe_iff.mpr (h i).1, EReal.coe_le_coe_iff.mpr (h i).2⟩
    · rw [Function.extend_apply' _ _ _ hj, Function.extend_apply' _ _ _ hj]
      exact ⟨bot_le, le_top⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
