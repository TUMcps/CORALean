import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExp

/-!
# `PolyZonotope.relaxExp`

The exact layer's `relaxExp`, rounded. Two things it computes are sums of stored
floats — the merged dependent column and the `ξ_E` copies of the relaxed one —
and each is stored downward with the gap to its upward rounding paid into the
box, as `compact` pays for merging columns.

`ξ_E` itself rounds nothing: `eDiff` is over ℕ in both layers and the exponent
matrix is copied, so the two layers relax by the same width. At `ξ_E ≤ 1` that
column folds against `zero` alone, which no format moves and only the axioms
leave open; the paper's graph selects exactly those pairs.

The centre is untouched, `ξ_c` being zero at `ξ_G = ξ_E`, so this operation adds
nothing to the box beyond the two gaps.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}

/-- `ξ_E`, read off the exponent matrix and so the exact layer's own width. -/
def PolyZonotope.relaxWidth (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : ℕ :=
  Real.PolyZonotope.eDiff (PZ.E k₀ (part.right 0)) (PZ.E k₀ (part.right 1))

/-- The two merged generators as stored: their sum, rounded down. -/
def PolyZonotope.mergedGen (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) : Vec 𝕋 n :=
  fun i => addDown (PZ.G i (part.right 1)) (PZ.G i (part.right 0))

/-- The new independent generator as stored: `ξ_E` copies of the relaxed
generator, rounded down. -/
def PolyZonotope.relaxGen (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => nsmulDown (PZ.relaxWidth part k₀) (PZ.G i (part.right 0))

/-- What the two stored columns can be off by, each the gap to the other
rounding direction of the same sum. -/
def PolyZonotope.relaxGap (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Mat 𝕋 n 2 :=
  fun i =>
    ![subUp (addUp (PZ.G i (part.right 1)) (PZ.G i (part.right 0))) (PZ.mergedGen part i),
      subUp (nsmulUp (PZ.relaxWidth part k₀) (PZ.G i (part.right 0))) (PZ.relaxGen part k₀ i)]

/-- The two generators `part.right` names merged into one, at the exponent
column of the second, the first scaled by `ξ_E` becoming independent. -/
def PolyZonotope.relaxExp (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : PolyZonotope 𝕋 n where
  p := PZ.p
  h := d + 1
  q := PZ.q + 1
  c := PZ.c
  G := fun i => Fin.append (fun l => PZ.G i (part.left l)) (fun _ => PZ.mergedGen part i)
  E := fun k => Fin.append (fun l => PZ.E k (part.left l)) (fun _ => PZ.E k (part.right 1))
  GI := fun i => Fin.append (PZ.GI i) (fun _ => PZ.relaxGen part k₀ i)
  err := PZ.err.plus (PolyZonotope.generatorError (PZ.relaxGap part k₀))

end CORALean.Float
