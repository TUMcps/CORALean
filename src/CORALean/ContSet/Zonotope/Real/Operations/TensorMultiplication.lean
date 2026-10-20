module

public import CORALean.Global.Tensor
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Operations.TensorLists
public import CORALean.ContSet.Zonotope.Real.Operations.TensorEval

@[expose] public section

/-!
# `Zonotope.tensorMultiplication`

CORA's `@zonotope/tensorMultiplication.m` for a third-order tensor `M = {M₁, ..., Mₙ}`, `Mᵢ` an
`n × n × n` array: an enclosure of `{ Mᵢⱼₖₗ xⱼ xₖ xₗ | x ∈ Z }` by a zonotope, when the center of
`Z` is the origin (otherwise CORA leaves `H` undefined and errors; the theorem assumes `Z.c = 0`).
For every permutation `p` of generator indices the product of the three generators through `M` is
`tildeH`, added to the column `map p` of the generator matrix `H`; the result is `(0, H)`. CORA's
`options.list.perm`, `.comb` and `.map` are arguments (no CORA code builds them); `comb` is only
read for its row count. The second-order branch indexes the cell array `M` as `M(iDim, ind1, ind2)`
while the order is read from `size(M{1})`, so it errors for every input and is not modelled.

## Inputs
* `Z` – zonotope
* `M` – third-order tensor
* `L` – term lists

## Output
* zonotope enclosing the tensor products
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `tensorMultiplication(Z, M, options)` for a third-order tensor and a centered zonotope. -/
noncomputable def Zonotope.tensorMultiplication (Z : Zonotope (Vec ℝ n)) (M : Tensor3 ℝ n)
    (L : Zonotope.TensorLists Z.h) : Zonotope (Vec ℝ n) :=
  let G := Z.G
  -- `tildeH = aux_generatorMultiplication_3d(M, genComb)` with `genComb = G(:, perm(p, :))`
  let tildeH := fun p : Fin L.P => fun iDim : Fin n =>
    ∑ ind1, ∑ ind2, ∑ ind3, M iDim ind1 ind2 ind3 * G (L.perm p 0) ind1 *
      G (L.perm p 1) ind2 * G (L.perm p 2) ind3
  -- `H(:, map(p)) = H(:, map(p)) + tildeH`
  let H := fun cInd : Fin L.C => ∑ p ∈ Finset.univ.filter (fun p => L.map p = cInd), tildeH p
  ⟨L.C, 0, H⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
