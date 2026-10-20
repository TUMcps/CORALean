module

public import CORALean.ContSet.Interval.Float.Operations.Lift
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Interval.lift_` is exact, over a floating-point scalar

For distinct target coordinates, the result denotes the points whose `proj`-coordinates lie in the
box; nothing rounds.

## Inputs
* `I` – interval box
* `N` – ambient dimension
* `proj` – coordinate embedding

## Hypotheses
* `hp` – embedding injective

## Conclusion
* the lifted box is exactly the set of points whose chosen coordinates lie in `I`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


variable {m N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Interval.aux_lift_find (proj : Fin m → Fin N) (hp : Function.Injective proj)
    (j : Fin m) : -- --- CONCL ---
    ∀ l : List (Fin m), j ∈ l → l.find? (fun k => proj k = proj j) = some j := by -- --- PROOF ---
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons a l ih =>
    intro h
    by_cases ha : proj a = proj j
    · rw [List.find?_cons_of_pos (by simpa using ha), hp ha]
    · rw [List.find?_cons_of_neg (by simpa using ha)]
      refine ih ?_
      rcases List.mem_cons.1 h with rfl | h
      · exact absurd rfl ha
      · exact h


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.lift_exact (I : Interval (Vec 𝕋 m)) (N : ℕ) (proj : Fin m → Fin N)
    (hp : Function.Injective proj) : -- --- CONCL ---
    (I.lift_ N proj).construct = {x | (fun i => x (proj i)) ∈ I.construct} := by -- --- PROOF ---
  -- every source coordinate is found at its own image
  have hfind : ∀ i, (List.finRange m).find? (fun j => proj j = proj i) = some i := fun i =>
    Interval.aux_lift_find proj hp i _ (List.mem_finRange i)
  ext x
  constructor
  · -- a point of the lifted box restricts to a point of the box
    intro h i
    have h1 := (h (proj i)).1
    have h2 := (h (proj i)).2
    simp only [Interval.lift_, hfind, Option.map_some] at h1 h2
    exact ⟨h1 _ rfl, h2 _ rfl⟩
  · -- and conversely: unbounded off the image of `proj`, the stored bounds on it
    intro h j
    by_cases hj : ∃ i, proj i = j
    · obtain ⟨i, rfl⟩ := hj
      have := h i
      simp only [Interval.lift_, hfind, Option.map_some]
      refine ⟨fun l hl => ?_, fun u hu => ?_⟩
      · cases Option.some.inj hl; exact this.1
      · cases Option.some.inj hu; exact this.2
    · have hn : (List.finRange m).find? (fun i => proj i = j) = none := by
        rw [List.find?_eq_none]
        intro i _ hi
        exact hj ⟨i, by simpa using hi⟩
      simp [Interval.lift_, hn]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
