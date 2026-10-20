module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.DependentTermsMatZono
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `MatExp.dependentTermsMatZono`

CORA's `@matZonotope/dependentTerms`: the square of `C + Σ βᵢ Gᵢ` is `C² + Σ βᵢ (C Gᵢ + Gᵢ C) + Σ
βᵢ² Gᵢ² + Σ_{i<j} βᵢβⱼ (Gᵢ Gⱼ + Gⱼ Gᵢ)`, and each `βᵢ² ∈ [0, 1]` is `½ + ½ (2βᵢ² - 1)` with the last
factor in `[-1, 1]`; `zSq` carries the three generator blocks, `zH` the second-order terms `I + M r
+ ½ M² r²` built from them. The pairs `i < j` are listed once each, in an arbitrary order (CORA's
`combinator(gens, 2, 'c')` is lexicographic); the set does not depend on it.

## Inputs
* `Z` – matrix zonotope
* `r` – step length

## Output
* squared and linear dependent terms of the matrix zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[zSq, zH] = dependentTerms(matZ, r)`. -/
noncomputable def MatExp.dependentTermsMatZono (Z : Zonotope (Mat ℝ n n)) (r : ℝ) :
    MatExp.DependentTermsMatZono n :=
  -- 1. the pairs `i < j` of `combinator(gens, 2, 'c')`
  let ind := Finset.univ.filter fun p : Fin Z.h × Fin Z.h => p.1 < p.2
  -- 2. `sqC = C² r² + ½ Σ Gᵢ² r²`
  let sqC := r ^ 2 • (Z.c * Z.c + (1 / 2 : ℝ) • ∑ i, Z.G i * Z.G i)
  -- 3. `sqG`: `(C Gᵢ + Gᵢ C) r²`, then `½ Gᵢ² r²`, then `(Gᵢ Gⱼ + Gⱼ Gᵢ) r²` for each pair
  let sqG₁ := fun i => r ^ 2 • (Z.c * Z.G i + Z.G i * Z.c)
  let sqG₂ := fun i => (r ^ 2 / 2) • (Z.G i * Z.G i)
  let sqG₃ := fun k : Fin ind.card =>
    r ^ 2 • (Z.G (ind.equivFin.symm k).1.1 * Z.G (ind.equivFin.symm k).1.2
      + Z.G (ind.equivFin.symm k).1.2 * Z.G (ind.equivFin.symm k).1.1)
  -- 4. `HC = I + C r + ½ sqC` and `HG = ½ sqG`, with `G r` added to the first block
  { zSq := ⟨Z.h + Z.h + ind.card, sqC, Fin.append (Fin.append sqG₁ sqG₂) sqG₃⟩
    zH := ⟨Z.h + Z.h + ind.card, 1 + r • Z.c + (1 / 2 : ℝ) • sqC,
      Fin.append (Fin.append (fun i => (1 / 2 : ℝ) • sqG₁ i + r • Z.G i)
        (fun i => (1 / 2 : ℝ) • sqG₂ i)) (fun k => (1 / 2 : ℝ) • sqG₃ k)⟩ }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
