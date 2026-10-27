module

public import CORALean.ContSet.ConZonotope.Real.Operations.OfMat
public import CORALean.Global.DropIdx

@[expose] public section

/-!
# `ConZonotope.eliminate`

[1, Thm. 2]'s own construction: row `r` of `Aξ = b` is solved for coefficient `j`, and that solution
is substituted into every generator, every row and the center. `Λ_G` and `Λ_A` are the paper's
rank-one correction matrices, kept to their one nonzero column, the `r`-th, since every other column
is zero by construction.

Column `j` of `G − Λ_G A` and of `A − Λ_A A`, and row `r` of `A − Λ_A A`, come out zero this way
(`eliminate_exact_of_dependClosed`'s proof); `dropIdx`, in place of the paper's "remove the zero row
and column", gives a system with one fewer generator and constraint.

## Inputs
* `ng` – number of generators
* `nc` – number of constraints
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `r` – constraint row to solve
* `j` – coefficient to eliminate

## Output
* the constrained zonotope without that coefficient

## References

* [1] [V. Raghuraman and J. P. Koeln. "Set operations and order reductions for constrained
      zonotopes". Automatica,
      2022.](../../../../../../references/2022/raghuraman-koeln-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Thm. 2]: row `r` of `Aξ = b` solved for coefficient `j` and substituted into the
generators, the constraints and the center, then generator `j` and constraint `r` —
both zero once substituted — dropped. -/
noncomputable def ConZonotope.eliminate {ng nc : ℕ} (c : α) (G : Fin ng → α)
    (A : Mat ℝ nc ng) (b : Vec ℝ nc) (r : Fin nc) (j : Fin ng) : ConZonotope α :=
  let ΛG : α := (A r j)⁻¹ • G j                          -- Λ_G, its only nonzero column
  let ΛA : Fin nc → ℝ := fun i => A i j * (A r j)⁻¹       -- Λ_A, its only nonzero column
  let G' : Fin ng → α := fun l => G l - A r l • ΛG        -- G − Λ_G A
  let A' : Fin nc → Fin ng → ℝ := fun i l => A i l - ΛA i * A r l  -- A − Λ_A A
  let b' : Fin nc → ℝ := fun i => b i - ΛA i * b r        -- b − Λ_A b
  let c' : α := c + b r • ΛG                              -- c + Λ_G b
  ConZonotope.ofMat c' (G' ∘ dropIdx j) (fun i k => A' (dropIdx r i) (dropIdx j k))
    (b' ∘ dropIdx r)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
