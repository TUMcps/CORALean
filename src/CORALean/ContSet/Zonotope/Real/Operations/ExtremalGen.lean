module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Sign

@[expose] public section

/-!
# The extremal offset of a zonotope in a direction

[1, Sec. 5.1]: the extremal points of `Z = (u, ⟨v₁, …, v_m⟩)` in the direction `sᵢ` are
`u - gᵢ` and `u + gᵢ`, with `gᵢ = Σⱼ sign(sᵢ·vⱼ) vⱼ`, read off the proof of
[1, Prop. 2]. `sign` is `Real.sign`, zero at zero, so a generator orthogonal to `sᵢ`
contributes nothing; either choice of its sign gives an extremal point.

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 5.1]: `gᵢ = Σⱼ sign(sᵢ·vⱼ) vⱼ`, so that `u ± gᵢ` are extremal along `sᵢ`. -/
noncomputable def Zonotope.extremalGen (Z : Zonotope (Vec ℝ n)) (s : Vec ℝ n) : Vec ℝ n :=
  ∑ j, Real.sign (s ⬝ᵥ Z.G j) • Z.G j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
