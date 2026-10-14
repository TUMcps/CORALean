module

public import CORALean.ContSet.Taylm.Real.Operations.Bounds
public import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.MemConstructIff
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# An array of Taylor models as a box

CORA's `interval(taylm)` with its default `'int'` method: each coordinate's `bounds`, the
term ranges summed with the remainder. Outer, as interval arithmetic is: the box contains
the range set and in general more, the dependence between terms being dropped. The
branch-and-bound methods (`optBnb`, `optLinQuad`, `optBernstein`) are tighter and not here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.interval_contains {m : ℕ} (T : Fin m → Taylm n) :
    Taylm.construct T ⊆ (Taylm.interval T).construct := by -- --- PROOF ---
  intro x hx i
  obtain ⟨f, hf, t, ht, hxf⟩ := (Taylm.mem_construct_iff T x).1 hx
  have := Taylm.bounds_mem (hf i) ht
  rw [← hxf i] at this
  exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
