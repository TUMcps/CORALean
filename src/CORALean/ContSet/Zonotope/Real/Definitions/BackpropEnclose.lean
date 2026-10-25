module

public import CORALean.ContSet.Zonotope.Real.Definitions.Gradient
public import CORALean.ContSet.Zonotope.Real.Operations.Row

@[expose] public section

/-!
# `Zonotope.backpropEnclose`

[1, Prop. 12]: the gradient set of an image enclosure (`Zonotope.imageEnclosure`), from the
input set `H = ⟨c, G⟩` with `p` generators and the output's gradient set `⟨c', G'⟩` with
`p + n`, per dimension `i`:
`m(i) ⟨c'(i), G'(i, [p])⟩ + (c'(i) c(i) + G'(i, [p]) G(i, ·)ᵀ) ∇_{H(i)} m(i)
  + ½(c'(i) + G'(i, p + i)) ∇_{H(i)} ē(i) + ½(c'(i) - G'(i, p + i)) ∇_{H(i)} e(i)`,
`∇_{H(i)}` the gradient set (`Zonotope.gradient`) with respect to the row `H(i)`
(`Zonotope.row`). The printed first term is `m(i) 𝒢(i)`, whose `p + n` generators the gradient
set of `H` does not have; the first `p` are meant, which is how the proof's Eq. 25 reads.

## Inputs
* `m` – neuron slope function
* `eLo` – lower error function
* `eUp` – upper error function
* `H` – input zonotope
* `c'` – center of the output gradient set
* `G'` – generators of the output gradient set

## Output
* gradient set of the input zonotope

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Prop. 12's gradient set of `H`, from the output's gradient set `⟨c', G'⟩`. -/
noncomputable def Zonotope.backpropEnclose (m eLo eUp : Zonotope (Vec ℝ 1) → ℝ)
    (H : Zonotope (Vec ℝ n)) (c' : Vec ℝ n) (G' : Fin (H.h + n) → Vec ℝ n) :
    Zonotope (Vec ℝ n) where
  h := H.h
  c := fun i =>
    let s := c' i * H.c i + ∑ j, G' (Fin.castAdd n j) i * H.G j i
    let g := G' (Fin.natAdd H.h i) i
    m (H.row i) * c' i + s * ((H.row i).gradient m).c 0 +
      (c' i + g) / 2 * ((H.row i).gradient eUp).c 0 +
      (c' i - g) / 2 * ((H.row i).gradient eLo).c 0
  G := fun j i =>
    let s := c' i * H.c i + ∑ j, G' (Fin.castAdd n j) i * H.G j i
    let g := G' (Fin.natAdd H.h i) i
    m (H.row i) * G' (Fin.castAdd n j) i + s * ((H.row i).gradient m).G j 0 +
      (c' i + g) / 2 * ((H.row i).gradient eUp).G j 0 +
      (c' i - g) / 2 * ((H.row i).gradient eLo).G j 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
