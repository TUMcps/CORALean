import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
import CORALean.Global.Partition

/-!
# `PolyZonotope.relaxExp`

`[1, Thm. 2]`: two dependent generators whose exponent columns agree everywhere
but at one index are merged into one, and what the merge costs is absorbed into
a single new independent generator. One dependent generator is traded for one
independent one, so no count grows and the set moves closer to a zonotope.

Which two are merged is a `Split` rather than a pair of indices, `reduceBy`'s
idiom: the partition names the two and the `d` that stay as one object. The
index `k₀` where the columns may differ is an argument, not an existential;
`relaxExp_outer` asks that they agree off it, so a wrong `k₀` costs the theorem
and not the definition.

`ξ_G = ξ_E` throughout, where `[1]` halves it and shifts the centre by the other
half when every exponent of column `i` is even. That recentring is not done here,
and `[1]` states it with two faults: the shift is `-ξ_E/2`, not `+ξ_E/2`, since
`α^A - α^B ≤ 0` for even `A > B`; and it omits the evenness of `E_{k₀,j}`,
without which the range is symmetric and the shift is zero. CORA is unaffected.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}

/-- `ξ_E`: how far the two monomials can drift apart, read at the one index
where their exponent columns may differ. -/
def PolyZonotope.relaxWidth (PZ : PolyZonotope α)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : ℕ :=
  PolyZonotope.eDiff (PZ.E k₀ (part.right 0)) (PZ.E k₀ (part.right 1))

/-- The two generators `part.right` names merged into one, at the exponent
column of the second, the first scaled by `ξ_E` becoming independent. -/
def PolyZonotope.relaxExp (PZ : PolyZonotope α)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : PolyZonotope α where
  p := PZ.p
  h := d + 1
  q := PZ.q + 1
  c := PZ.c
  G := Fin.append (fun l => PZ.G (part.left l))
    (fun _ => PZ.G (part.right 1) + PZ.G (part.right 0))
  E := fun k => Fin.append (fun l => PZ.E k (part.left l)) (fun _ => PZ.E k (part.right 1))
  GI := Fin.append PZ.GI
    (fun _ => (PZ.relaxWidth part k₀ : ℝ) • PZ.G (part.right 0))

end CORALean.Real
