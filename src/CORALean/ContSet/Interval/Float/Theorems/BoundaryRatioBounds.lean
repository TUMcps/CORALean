module

public import CORALean.ContSet.Interval.Float.Operations.BoundaryRatio

@[expose] public section

/-!
# `Interval.boundaryRatio` is the least of the coordinates' bounds

The result is `none` exactly when no coordinate has a ratio, and otherwise its lower end is at
most each coordinate's lower end, its upper end at most each coordinate's upper end, and it is the
greatest real bound with that property: any `y` below every coordinate's upper end is below the
result's. So a real ratio below every coordinate's upper bound is below the result's, and a real
ratio below the result's lower end is below every coordinate's.

## Inputs
* `I` – interval box
* `dir` – ray direction
* `start` – ray start point

## Hypotheses
* none

## Conclusion
* the result is none iff every coordinate gives none, else it is the least of the bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What the fold keeps of the coordinates it has processed. -/
def Interval.aux_ratioInv (f : Fin n → Option (Interval 𝕋)) (idx : List (Fin n))
    (acc : Option (Interval 𝕋)) : Prop :=
  (acc = none ↔ ∀ i ∈ idx, f i = none) ∧
    ∀ a, acc = some a →
      (∀ i ∈ idx, ∀ x, f i = some x → toReal a.inf ≤ toReal x.inf ∧ toReal a.sup ≤ toReal x.sup) ∧
        ∀ y : ℝ, (∀ i ∈ idx, ∀ x, f i = some x → y ≤ toReal x.sup) → y ≤ toReal a.sup

/-- One step keeps the invariant for the coordinates up to `i`. -/
theorem Interval.aux_ratio_step (f : Fin n → Option (Interval 𝕋)) (idx : List (Fin n)) (i : Fin n)
    (acc : Option (Interval 𝕋)) (h : Interval.aux_ratioInv f idx acc) : -- --- CONCL ---
    Interval.aux_ratioInv f (idx ++ [i])
      (Interval.aux_boundaryRatioStep acc (f i)) := by -- --- PROOF ---
  obtain ⟨h1, h2⟩ := h
  rcases hfi : f i with _ | r
  · -- no ratio at `i`: nothing changes
    simp only [Interval.aux_boundaryRatioStep]
    refine ⟨?_, fun a ha => ?_⟩
    · simp only [List.mem_append, List.mem_singleton]
      constructor
      · intro hn j hj
        rcases hj with hj | rfl
        · exact h1.1 hn j hj
        · exact hfi
      · intro hall; exact h1.2 fun j hj => hall j (Or.inl hj)
    · obtain ⟨h3, h4⟩ := h2 a ha
      refine ⟨fun j hj x hx => ?_, fun y hy => h4 y fun j hj x hx => hy j (by simp [hj]) x hx⟩
      simp only [List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact h3 j hj x hx
      · rw [hfi] at hx; exact absurd hx (by simp)
  · cases acc with
    | none =>
      -- the first ratio
      simp only [Interval.aux_boundaryRatioStep]
      refine ⟨?_, fun b hb => ?_⟩
      · simp only [List.mem_append, List.mem_singleton]
        constructor
        · intro hn; exact absurd hn (by simp)
        · intro hall; exact absurd (hall i (Or.inr rfl)) (by simp [hfi])
      · have hb' : r = b := Option.some.inj hb
        subst hb'
        refine ⟨fun j hj x hx => ?_, fun y hy => hy i (by simp) r hfi⟩
        simp only [List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · -- an earlier coordinate had no ratio
          have := h1.1 rfl j hj
          rw [this] at hx; exact absurd hx (by simp)
        · rw [hfi] at hx; cases Option.some.inj hx; exact ⟨le_rfl, le_rfl⟩
    | some a =>
      -- the least of the ratio so far and this one
      simp only [Interval.aux_boundaryRatioStep]
      refine ⟨?_, fun b hb => ?_⟩
      · simp only [List.mem_append, List.mem_singleton]
        constructor
        · intro hn; exact absurd hn (by simp)
        · intro hall; exact absurd (hall i (Or.inr rfl)) (by simp [hfi])
      · have hb' : (⟨minimum a.inf r.inf, minimum a.sup r.sup⟩ : Interval 𝕋) = b :=
          Option.some.inj hb
        subst hb'
        obtain ⟨h3, h4⟩ := h2 a rfl
        -- each processed coordinate's bounds are above the minimum, which is below both
        refine ⟨fun j hj x hx => ?_, fun y hy => ?_⟩
        · simp only [List.mem_append, List.mem_singleton] at hj
          rw [toReal_minimum, toReal_minimum]
          rcases hj with hj | rfl
          · exact ⟨le_trans (min_le_left _ _) (h3 j hj x hx).1,
              le_trans (min_le_left _ _) (h3 j hj x hx).2⟩
          · rw [hfi] at hx; cases Option.some.inj hx
            exact ⟨min_le_right _ _, min_le_right _ _⟩
        · rw [toReal_minimum]
          exact le_min (h4 y fun j hj x hx => hy j (by simp [hj]) x hx) (hy i (by simp) r hfi)

theorem Interval.aux_ratio_foldl (f : Fin n → Option (Interval 𝕋)) : -- --- CONCL ---
    ∀ (l : List (Fin n)) (acc : Option (Interval 𝕋)) (idx : List (Fin n)),
      Interval.aux_ratioInv f idx acc →
      Interval.aux_ratioInv f (idx ++ l)
        (l.foldl (fun acc i => Interval.aux_boundaryRatioStep acc (f i)) acc) := by -- --- PROOF ---
  intro l
  induction l with
  | nil => intro acc idx h; simpa using h
  | cons i l ih =>
    intro acc idx h
    have := ih _ (idx ++ [i]) (Interval.aux_ratio_step f idx i acc h)
    simpa [List.append_assoc] using this


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.boundaryRatio_bounds (I : Interval (Vec 𝕋 n))
    (dir start : Vec 𝕋 n) : -- --- CONCL ---
    (Interval.boundaryRatio I dir start = none ↔
        ∀ i, Interval.boundaryRatioAt I dir start i = none) ∧
      ∀ a, Interval.boundaryRatio I dir start = some a →
        (∀ i x, Interval.boundaryRatioAt I dir start i = some x →
          toReal a.inf ≤ toReal x.inf ∧ toReal a.sup ≤ toReal x.sup) ∧
        ∀ y : ℝ, (∀ i x, Interval.boundaryRatioAt I dir start i = some x → y ≤ toReal x.sup) →
          y ≤ toReal a.sup := by -- --- PROOF ---
  have h := Interval.aux_ratio_foldl (Interval.boundaryRatioAt I dir start) (List.finRange n)
    none [] ⟨by simp, fun a ha => absurd ha (by simp)⟩
  obtain ⟨h1, h2⟩ := h
  simp only [List.nil_append, List.mem_finRange, true_implies] at h1 h2
  refine ⟨h1, fun a ha => ?_⟩
  obtain ⟨h3, h4⟩ := h2 a ha
  exact ⟨fun i x hx => h3 i x hx, fun y hy => h4 y fun i x hx => hy i x hx⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
