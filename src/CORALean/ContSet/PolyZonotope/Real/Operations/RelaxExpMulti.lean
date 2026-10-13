module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthMulti

@[expose] public section

/-!
# `PolyZonotope.relaxExpMulti`

`[1, Prop. 4]`: `relaxExp` with the drift read at every factor rather than at
one. The construction is unchanged — two dependent generators become one and
what the merge costs becomes one independent generator — and only the width
grows, from a single `eDiff` to their sum.

`[1]` sums over the indices where the two columns differ; this sums over all of
them, which is the same number since `eDiff a a = 0`, and is the reason the
operation takes no index and its guarantee no hypothesis. Any two dependent
generators may be merged, so the similarity of `[1, Def. 4]` is left to whatever
chooses the pair, where it belongs: it decides how wide the new generator is,
never whether the result encloses.

Kept beside `relaxExp` rather than replacing it. The two compute different
widths, so neither is the other's instance without a hypothesis carried into a
structure equality, and `relaxExpEven` halves the single-index width on a
one-sidedness that the multi-index drift does not have.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two generators `part.right` names merged into one, at the exponent
column of the second, the first scaled by the summed `ξ_E` becoming
independent. -/
def PolyZonotope.relaxExpMulti (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) : PolyZonotope α where
  p := pZ.p
  h := d + 1
  q := pZ.q + 1
  c := pZ.c
  G := Fin.append (fun l => pZ.G (part.left l))
    (fun _ => pZ.G (part.right 1) + pZ.G (part.right 0))
  E := fun k => Fin.append (fun l => pZ.E k (part.left l)) (fun _ => pZ.E k (part.right 1))
  GI := Fin.append pZ.GI
    (fun _ => (pZ.relaxWidthMulti part : ℝ) • pZ.G (part.right 0))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
