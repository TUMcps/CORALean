module

public import CORALean.ContSet.StarSet.Real.StarSet

@[expose] public section

/-!
# `ContSet/StarSet/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {m : ℕ}


-- ================================  `StarSet.LinPred.addRows`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The predicate with the rows `rs` added after its own. -/
def StarSet.LinPred.addRows (p : StarSet.LinPred m) (rs : List ((Fin m → ℝ) × ℝ)) :
    StarSet.LinPred m :=
  { p with cons := p.cons ++ rs }


-- ==================================  `StarSet.LinPred.snoc`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- One more factor, in `[lo, hi]` and read by no row: every row padded with a zero. -/
def StarSet.LinPred.snoc (p : StarSet.LinPred m) (lo hi : ℝ) : StarSet.LinPred (m + 1) :=
  ⟨p.cons.map fun r => (Fin.snoc (α := fun _ => ℝ) r.1 0, r.2), Fin.snoc (α := fun _ => ℝ) p.l lo,
    Fin.snoc (α := fun _ => ℝ) p.u hi⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
