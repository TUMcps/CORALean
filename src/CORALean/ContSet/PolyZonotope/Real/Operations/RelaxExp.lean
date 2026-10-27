module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidth

@[expose] public section

/-!
# `PolyZonotope.relaxExp`

`[1, Thm. 1]`: two dependent generators whose exponent columns agree everywhere but at one
index are merged into one, and the cost is absorbed into one new independent generator of width
`ξ_E = relaxWidth`, the maximum of `|x^a - x^b|` as CORA's `minMaxDiffPoly` computes it. The
partition (a `Split`, `reduceBy`'s idiom) names the two; the index `k₀` is an argument, and
`relaxExp_outer` asks that the columns agree off it. `ξ_G = ξ_E` throughout, where `[1]` halves
it and shifts the center when every exponent of column `i` is even. That recentering is not done
here, and `[1]` states it with two faults: the shift is `-ξ_E/2`, not `+ξ_E/2`, and it omits
the evenness of `E_{k₀,j}`. CORA is unaffected.

## Inputs
* `pZ` – polynomial zonotope
* `part` – split with two selected generators
* `k₀` – factor index

## Output
* polynomial zonotope with the two generators relaxed into one

## References

* [1] [T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications
      in Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.](../../../../../../references/2024/ladner-aaai-exponent-relaxation.md)
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two generators `part.right` names merged into one, at the exponent
column of the second, the first scaled by `ξ_E` becoming independent. -/
noncomputable def PolyZonotope.relaxExp (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : PolyZonotope α where
  p := pZ.p
  h := d + 1
  q := pZ.q + 1
  c := pZ.c
  G := Fin.append (fun l => pZ.G (part.left l))
    (fun _ => pZ.G (part.right 1) + pZ.G (part.right 0))
  E := fun k => Fin.append (fun l => pZ.E k (part.left l)) (fun _ => pZ.E k (part.right 1))
  GI := Fin.append pZ.GI
    (fun _ => pZ.relaxWidth part k₀ • pZ.G (part.right 0))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
