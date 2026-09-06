import CORALean.ContSet.PolyZonotope.Float.Theorems.RelaxExpGreedyOuter
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpGreedySel
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpGreedyOuter

/-!
# Relaxing exponents along a selection that runs

What this records is that the selection costs the guarantee nothing.
`relaxExpGreedy_outer` is stated at an arbitrary `sel`, and `expGreedySel` is
one — so the enclosure is `:=` and the heuristic carries no hypothesis, no
threshold condition and no proof that the edge it found is an edge. Replacing
it by a better rule cannot break either line.

One selection serves both layers because it reads only the exponent matrix,
which is the same ℕ-valued field in each. That is also why it *runs*: the graph
of `[1, Def. 5]` decides, so the search is a fold over pairs and not a choice
function.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

-- Anonymous, since their content is that they elaborate.

/-- The exact layer's loop, driven by the lightest-edge rule at threshold `η`. -/
example {α : Type} [AddCommGroup α] [Module ℝ α] (PZ : Real.PolyZonotope α) (η n : ℕ) :
    PZ.construct ⊆ (Real.PolyZonotope.relaxExpGreedy
      (fun PZ' => Real.PolyZonotope.expGreedySel PZ'.E η) n PZ).construct :=
  Real.PolyZonotope.relaxExpGreedy_outer _ n PZ

/-- The same rule at a float representation, whose exponents are the same
naturals; it needs no float counterpart of its own. -/
example {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}
    (PZ : Float.PolyZonotope 𝕋 n) (η m : ℕ) :
    PZ.construct ⊆ (Float.PolyZonotope.relaxExpGreedy
      (fun PZ' => Real.PolyZonotope.expGreedySel PZ'.E η) m PZ).construct :=
  Float.PolyZonotope.relaxExpGreedy_outer _ m PZ

end CORALean
