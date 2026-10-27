module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxDrift

@[expose] public section

/-!
# `PolyZonotope.relaxExpMid`

`[1, Thm. 1]` with the drift taken as an interval rather than as a radius: the center moves
by its midpoint and the new independent generator carries its half-width. `[1]` shifts only
when every exponent of column `i` is even, and CORA's other branch not at all; the identity
`mid + [-rad, rad] = [lo, hi]` holds whatever the exponents. At a symmetric drift this is
`relaxExp`, at an all-even one `relaxExpEven`. It goes past both at an edge of `[1, Def. 5]`
through its second disjunct, `E_{k₀,j} = 0`, one-sided at any parity of `E_{k₀,i}`. Otherwise
`relaxExp`'s construction: one dependent generator traded for one independent one.

## Inputs
* `pZ` – polynomial zonotope
* `part` – split with two selected generators
* `k₀` – factor index

## Output
* relaxed polynomial zonotope with midpoint center shift

## References

* [1] [T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications
      in Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.](../../../../../../references/2024/ladner-aaai-exponent-relaxation.md)
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two generators `part.right` names merged into one, the drift's midpoint
moved into the center and its half-width into a new independent generator. -/
noncomputable def PolyZonotope.relaxExpMid (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : PolyZonotope α where
  p := pZ.p
  h := d + 1
  q := pZ.q + 1
  c := pZ.c + (pZ.relaxDrift part k₀).1 • pZ.G (part.right 0)
  G := Fin.append (fun l => pZ.G (part.left l))
    (fun _ => pZ.G (part.right 1) + pZ.G (part.right 0))
  E := fun k => Fin.append (fun l => pZ.E k (part.left l)) (fun _ => pZ.E k (part.right 1))
  GI := Fin.append pZ.GI (fun _ => (pZ.relaxDrift part k₀).2 • pZ.G (part.right 0))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
