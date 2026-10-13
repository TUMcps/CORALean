import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidth

/-!
# `PolyZonotope.relaxExp`

`[1, Thm. 1]`: two dependent generators whose exponent columns agree everywhere
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

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two generators `part.right` names merged into one, at the exponent
column of the second, the first scaled by `ξ_E` becoming independent. -/
def PolyZonotope.relaxExp (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : PolyZonotope α where
  p := pZ.p
  h := d + 1
  q := pZ.q + 1
  c := pZ.c
  G := Fin.append (fun l => pZ.G (part.left l))
    (fun _ => pZ.G (part.right 1) + pZ.G (part.right 0))
  E := fun k => Fin.append (fun l => pZ.E k (part.left l)) (fun _ => pZ.E k (part.right 1))
  GI := Fin.append pZ.GI
    (fun _ => (pZ.relaxWidth part k₀ : ℝ) • pZ.G (part.right 0))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
