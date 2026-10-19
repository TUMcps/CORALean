module

public import CORALean.ContSet.StarSet.Float.Definitions.LinPred
public import CORALean.Global.Float.FloatOps
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# `ContSet/StarSet/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m : ℕ}


-- ================================  `StarSet.LinPred.addRows`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The predicate with the rows `rs` added after its own. -/
def StarSet.LinPred.addRows (p : StarSet.LinPred 𝕋 m) (rs : List ((Fin m → 𝕋) × 𝕋)) :
    StarSet.LinPred 𝕋 m :=
  { p with cons := p.cons ++ rs }


-- =================================  `StarSet.LinPred.append`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `k` more factors, in `[lo, hi]` and read by no row: every row padded with zeros. -/
def StarSet.LinPred.append {k : ℕ} (p : StarSet.LinPred 𝕋 m) (lo hi : Fin k → 𝕋) :
    StarSet.LinPred 𝕋 (m + k) :=
  ⟨p.cons.map fun r => (Fin.append r.1 fun _ => zero, r.2), Fin.append p.l lo, Fin.append p.u hi⟩


-- ==================================  `StarSet.LinPred.snoc`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- One more factor, in `[lo, hi]` and read by no row: every row padded with a zero. -/
def StarSet.LinPred.snoc (p : StarSet.LinPred 𝕋 m) (lo hi : 𝕋) : StarSet.LinPred 𝕋 (m + 1) :=
  ⟨p.cons.map fun r => (Fin.snoc (α := fun _ => 𝕋) r.1 zero, r.2),
    Fin.snoc (α := fun _ => 𝕋) p.l lo, Fin.snoc (α := fun _ => 𝕋) p.u hi⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
