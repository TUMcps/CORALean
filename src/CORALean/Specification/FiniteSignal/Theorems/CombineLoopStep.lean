module

public import CORALean.Specification.FiniteSignal.Operations.CombineLoop
public import Mathlib.Order.Basic

@[expose] public section

/-!
# One step of the combination loop

For breakpoints `l :: ls` and `r :: rs` with strictly increasing times, the loop sets the value at
the earlier time and moves on to the remaining breakpoints `ls'` and `rs'`: the later times are
all strictly after it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.combineLoop_step {T V W : Type} [LinearOrder T] [DecidableEq W]
    (op : V → V → W) (l r : T × V) (ls rs : List (T × V)) (hls : ∀ y ∈ ls, l.1 < y.1)
    (hrs : ∀ y ∈ rs, r.1 < y.1) : -- --- CONCL ---
    ∃ (t₀ : T) (ls' rs' : List (T × V)),
      FiniteSignal.combineLoop op (l :: ls) (r :: rs) = FiniteSignal.combineEmit op t₀
        (op l.2 r.2) ls' rs' (FiniteSignal.combineLoop op ls' rs') ∧
      (∀ y ∈ ls', t₀ < y.1) ∧ (∀ y ∈ rs', t₀ < y.1) ∧ t₀ = min l.1 r.1 ∧
      ((ls' = ls ∧ t₀ = l.1) ∨ (ls' = l :: ls ∧ t₀ < l.1)) ∧
      ((rs' = rs ∧ t₀ = r.1) ∨ (rs' = r :: rs ∧ t₀ < r.1)) := by -- --- PROOF ---
  by_cases h1 : l.1 < r.1
  · -- the left signal makes progress
    refine ⟨l.1, ls, r :: rs, ?_, hls, ?_, (min_eq_left h1.le).symm, Or.inl ⟨rfl, rfl⟩,
      Or.inr ⟨rfl, h1⟩⟩
    · rw [FiniteSignal.combineLoop, if_pos h1]
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h1
      · exact h1.trans (hrs y hy)
  · by_cases h2 : l.1 = r.1
    · -- both signals make progress
      refine ⟨l.1, ls, rs, ?_, hls, fun y hy => h2 ▸ hrs y hy, (min_eq_left h2.le).symm,
        Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, h2⟩⟩
      rw [FiniteSignal.combineLoop, if_neg h1, if_pos h2]
    · -- the right signal makes progress
      have h3 : r.1 < l.1 := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
      refine ⟨r.1, l :: ls, rs, ?_, ?_, hrs, (min_eq_right h3.le).symm, Or.inr ⟨rfl, h3⟩,
        Or.inl ⟨rfl, rfl⟩⟩
      · rw [FiniteSignal.combineLoop, if_neg h1, if_neg h2]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h3
        · exact h3.trans (hls y hy)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
