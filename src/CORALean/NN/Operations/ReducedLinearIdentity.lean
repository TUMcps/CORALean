module

public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.NN.Definitions.ReducibleNetwork

@[expose] public section

/-!
# The identity kernel as a layer of [1, Eq. 2]

[1, Cor. 1]'s compression network opens and closes with the kernel `K(k,l,1,1) = [k = l]`,
which leaves every pixel where it is. In [1, Eq. 2]'s form it is the identity matrix, a zero
bias and a zero error box, all placed rather than computed, so stored exactly.

## Inputs
* `n` – layer width

## Output
* identity as a linear layer with no error

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The identity as a layer of [1, Eq. 2]: [1, Cor. 1]'s kernel `K(k,l,1,1) = [k = l]`, which
leaves every pixel where it is, with no error. -/
def ReducedLinear.identity (n : ℕ) : ReducedLinear 𝕋 n n :=
  ⟨diagonalBlock fun _ => one, fun _ => zero, Interval.point fun _ => zero⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
