import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.quadTaylor`

[1, Prop. 3]'s `W_Z(t)`, at `η = 2`: the second-order Taylor sum `I + At + ½(At)²` of the
matrix exponential, evaluated over a whole matrix zonotope `A_Z` rather than one matrix, by
the same closed-form generator construction the proposition itself derives, corrected by a
factor of two the source's own printed coefficients drop — see the page's `## Findings`.

Three blocks, `κ + κ + κ²` generators wide: the linear-cross block at `p i`, exactly [1]'s
`L^(j)`; the diagonal block at `q i := 2(p i)² - 1`, exactly [1]'s `L^(κ+j)`; and a *sparse*
`κ × κ` block, zero except at `i < j`, where it carries `p i * p j` on the single symmetrized
generator `(G^(i)G^(j) + G^(j)G^(i))` — [1]'s own `L^(2κ+l)`, one generator per *unordered*
pair rather than one independent generator per ordered pair. The padding at `i ≥ j` changes
nothing about the set the zonotope denotes — a generator that is always `0` carries no
coefficient anywhere — so `κ + κ + κ²` generators denote exactly what [1]'s own
`κ + κ + κ(κ-1)/2` do; only the index type differs, not the reach.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.quadTaylor (A_Z : Zonotope (Mat ℝ n n)) (t : ℝ) :
    Zonotope (Mat ℝ n n) where
  h := A_Z.h + A_Z.h + A_Z.h * A_Z.h
  c := (1 : Mat ℝ n n) + t • A_Z.c + (t ^ 2 / 2) • (A_Z.c * A_Z.c)
    + (t ^ 2 / 4) • ∑ i, A_Z.G i * A_Z.G i
  G := Fin.append
    (Fin.append
      (fun i => t • A_Z.G i + (t ^ 2 / 2) • (A_Z.c * A_Z.G i + A_Z.G i * A_Z.c))
      (fun j => (t ^ 2 / 4) • (A_Z.G j * A_Z.G j)))
    (fun k =>
      let ij := finProdFinEquiv.symm k
      if ij.1 < ij.2 then (t ^ 2 / 2) • (A_Z.G ij.1 * A_Z.G ij.2 + A_Z.G ij.2 * A_Z.G ij.1)
      else 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
