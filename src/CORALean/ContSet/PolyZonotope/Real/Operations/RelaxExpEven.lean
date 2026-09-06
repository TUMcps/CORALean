import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExp

/-!
# `PolyZonotope.relaxExpEven`

`relaxExp` with the recentring of `[1, Thm. 1]`. `sub_monomial_nonpos` makes the
drift between the two monomials one-sided, `[-ξ_E, 0]` rather than
`[-ξ_E, ξ_E]`, so half of it is a constant the centre absorbs and only the other
half is paid into the new independent generator.

The shift is `-ξ_E/2` where `[1]` prints `+ξ_E/2`: at both exponents even and
`E_{k₀,j} ≤ E_{k₀,i}`, `α^A - α^B = (α²)^{A/2} - (α²)^{B/2} ≤ 0`. Both even also
forces equal parity, so `eDiff` is `0` or `1` and the halving is exact.

Separate from `relaxExp` rather than a branch in it: what makes the shift sound
is `relaxExpEven_outer`'s hypotheses, which no definition can read.

The evenness is about tightness, not soundness — a midpoint and a radius
describe any drift interval, so CORA's unshifted branch is looser than it need
be. It buys nothing here: `eDiff` is integral, so a mixed-parity drift is
bounded by the symmetric `[-2, 2]` and has no midpoint to move.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}

/-- `relaxExp` with the drift's midpoint taken off the centre, so the new
independent generator carries only its radius. -/
noncomputable def PolyZonotope.relaxExpEven (PZ : PolyZonotope α)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : PolyZonotope α where
  p := PZ.p
  h := d + 1
  q := PZ.q + 1
  c := PZ.c - ((PZ.relaxWidth part k₀ : ℝ) / 2) • PZ.G (part.right 0)
  G := Fin.append (fun l => PZ.G (part.left l))
    (fun _ => PZ.G (part.right 1) + PZ.G (part.right 0))
  E := fun k => Fin.append (fun l => PZ.E k (part.left l)) (fun _ => PZ.E k (part.right 1))
  GI := Fin.append PZ.GI
    (fun _ => ((PZ.relaxWidth part k₀ : ℝ) / 2) • PZ.G (part.right 0))

end CORALean.Real
