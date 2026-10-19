module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# `ConZonotope.liftEq`

The zonotope CORA's `@conZonotope/reduce` reduces: the equality rows of `P` move into
the generators and the center, `Z⁺ = [G; Aₑ]` with center `[c; -bₑ]` in `ℝ^{n + mₑ}`
[1, Sec. 4.3]. Row `i` of the lower block holds `Aₑ i` read at the unit vector of
each generator, so the lifted generator `j` is `[G j; (Aₑ i e_j)ᵢ]`.

The inequality rows are not lifted, CORA's representation having none; they stay on `P`, whose
equalities `HPolytope.dropEqs` removes (`HPolytope.construct_subset_dropEqs`),
which is why the result is a constrained zonotope, with `mₑ = 0` equalities, and not a
zonotope. Its set holds the points of `cZ` with the equalities forgotten (see
`mem_liftEq_of_mem`), which `Aₑ β = bₑ` then cuts back to.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[c; -bₑ]` with generators `[G j; Aₑ e_j]`, the inequality rows of `P` kept. -/
noncomputable def ConZonotope.liftEq (cZ : ConZonotope (Vec ℝ n)) :
    ConZonotope (Vec ℝ (n + cZ.P.me)) where
  h := cZ.h
  c := Fin.append cZ.c (-cZ.P.be)
  G := fun j => Fin.append (cZ.G j) fun i => cZ.P.Ae i (Pi.single j (1 : ℝ) : Vec ℝ cZ.h)
  P := cZ.P.dropEqs

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
