import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxDrift

/-!
# `PolyZonotope.relaxExpMid`

`[1, Thm. 1]` with the drift taken as an interval rather than as a radius: the
centre moves by its midpoint and the new independent generator carries its
half-width. `[1]` shifts only when every exponent of column `i` is even, and
CORA's other branch shifts not at all and pays the full width; the identity
`mid + [-rad, rad] = [lo, hi]` holds whatever the exponents, so there is nothing
for the evenness test to gate but tightness.

At a symmetric drift the midpoint is zero and this is `relaxExp`; at an all-even
one it is `-ξ_E/2` and this is `relaxExpEven`. Where it goes past both is an
edge of `[1, Def. 5]` taken through its second disjunct, `E_{k₀,j} = 0`, which
is one-sided at any parity of `E_{k₀,i}` and which the all-even test rejects.

The construction is otherwise `relaxExp`'s: one dependent generator traded for
one independent one, at the exponent column of the second of the pair.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two generators `part.right` names merged into one, the drift's midpoint
moved into the centre and its half-width into a new independent generator. -/
noncomputable def PolyZonotope.relaxExpMid (PZ : PolyZonotope α)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : PolyZonotope α where
  p := PZ.p
  h := d + 1
  q := PZ.q + 1
  c := PZ.c + (PZ.relaxDrift part k₀).1 • PZ.G (part.right 0)
  G := Fin.append (fun l => PZ.G (part.left l))
    (fun _ => PZ.G (part.right 1) + PZ.G (part.right 0))
  E := fun k => Fin.append (fun l => PZ.E k (part.left l)) (fun _ => PZ.E k (part.right 1))
  GI := Fin.append PZ.GI (fun _ => (PZ.relaxDrift part k₀).2 • PZ.G (part.right 0))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
