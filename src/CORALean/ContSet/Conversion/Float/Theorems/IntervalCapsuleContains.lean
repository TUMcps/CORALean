module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.Capsule.Real.Theorems.ConstructSubsetOfDistLe
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalCapsuleAlongContains
public import CORALean.Global.Float.Sqrt
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Capsule
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalCapsuleAlongContains
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Capsule

@[expose] public section

/-!
# A box as a capsule, over a floating-point scalar

`Interval.capsule_contains`: its `capsule` contains it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


omit [SoundFloatArithmetic 𝕋] in
private theorem foldl_widest_some (I : Interval (Vec 𝕋 n)) : -- --- STMT ---
    ∀ (l : List (Fin n)) (b : Fin n), ∃ b', l.foldl
      (fun best i =>
        match best with
        | none => some i
        | some b =>
          if le (subUp (I.sup i) (I.inf i)) (subUp (I.sup b) (I.inf b)) then some b else some i)
      (some b) = some b' := by -- --- PROOF ---
  intro l
  induction l with
  | nil => exact fun b => ⟨b, rfl⟩
  | cons i l ih =>
    intro b
    simp only [List.foldl_cons]
    split_ifs
    · exact ih b
    · exact ih i


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.capsule_contains (k : ℕ) (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ (I.capsule k).construct := by -- --- PROOF ---
  unfold Interval.capsule
  cases h : I.widestAxis with
  | some a => exact I.capsuleAlong_contains k a
  | none =>
    have hn : n = 0 := by
      by_contra hn
      have hne : List.finRange n ≠ [] := by simpa [List.finRange_eq_nil_iff] using hn
      obtain ⟨i, l, hl⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨b', hb'⟩ := foldl_widest_some I l i
      unfold Interval.widestAxis at h
      rw [hl, List.foldl_cons] at h
      simp only at h
      -- the fold's `match` is a second auxiliary definition here, so it is compared up to unfolding
      exact absurd (h.symm.trans hb') (by simp)
    subst hn
    intro x _
    exact ⟨0, by simp, by simp [Capsule.nominal, toReal_zero]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
