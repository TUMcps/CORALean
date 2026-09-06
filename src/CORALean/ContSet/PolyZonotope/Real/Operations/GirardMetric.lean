import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# Girard's ranking metric on one generator

Split out of `Reduce.lean` (issue #62), no longer `aux_`: `reduceGirard` and
`reduceGirardDependent` each need it from their own file, so neither can keep
it file-local.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, over a bare family so that
either block and their concatenation are ranked by this one line. Zero on the
axis-aligned generators; the max folds from `0`, which no `|G i j|` undercuts. -/
noncomputable def PolyZonotope.girardMetric {m : ℕ} (G : Fin m → Vec ℝ n) (l : Fin m) : ℝ :=
  (∑ i, |G l i|) - Finset.univ.fold max 0 fun i => |G l i|

end CORALean.Real
