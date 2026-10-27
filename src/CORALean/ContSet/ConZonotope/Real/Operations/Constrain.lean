module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs

@[expose] public section

/-!
# `Zonotope.constrain`

[1, Def. 3]: the zonotope `Z = ⟨c, G⟩_Z` with the inequality constraints `C β ≤ d` on its
factors, `Z|_{C≤d} := {c + G β | β ∈ [-1, 1]^q, C β ≤ d}`. Inequalities, where [2, Def. 3] has
equalities; a `ConZonotope` holds its constraints as an `HPolytope` on the factor space, which
carries either, so this is that constrained zonotope with the polytope `⟨C, d⟩_H`.

## Inputs
* `Z` – zonotope
* `C` – constraint matrix on the factors
* `d` – constraint offset

## Output
* the constrained zonotope `Z|_{C≤d}`

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations,
      2026.](../../../../../../references/2026/koller-iclr-latent-space.md)
* [2] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Z|_{C≤d} := {c + G β | β ∈ [-1, 1]^q, C β ≤ d}`, [1, Def. 3]. -/
def Zonotope.constrain (Z : Zonotope α) (C : Mat ℝ p Z.h) (d : Vec ℝ p) : ConZonotope α :=
  ⟨Z.h, Z.c, Z.G, HPolytope.ineqs C d⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
