module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# The range set is the union of the enclosed functions' images

A point of `construct` is the value at one point of the box of functions the models
enclose, and conversely: the range-set semantics follows from the functional one.

## Inputs
* `m` – number of functions
* `T` – family of Taylor models
* `x` – point

## Hypotheses
* none

## Conclusion
* membership means some enclosed functions take that value at a box point
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.mem_construct_iff {m : ℕ} (T : Fin m → Taylm n) (x : Vec ℝ m) :
    x ∈ Taylm.construct T ↔
      ∃ f : Fin m → Vec ℝ n → ℝ, (∀ i, (T i).Encloses (f i)) ∧
        ∃ t ∈ Taylm.box n, ∀ i, x i = f i t := by -- --- PROOF ---
  constructor
  · -- the polynomial shifted by the remainder value `x` has at `t`
    rintro ⟨t, ht, hx⟩
    refine ⟨fun i s => (T i).poly s + (x i - (T i).poly t), fun i s _ => ?_, t, ht,
      fun i => ?_⟩
    · simp only [add_sub_cancel_left]; exact hx i
    · ring
  · rintro ⟨f, hf, t, ht, hx⟩
    exact ⟨t, ht, fun i => by rw [hx i]; exact hf i t ht⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
