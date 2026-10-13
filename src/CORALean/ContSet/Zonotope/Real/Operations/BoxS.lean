module

public import CORALean.ContSet.ContSet.Definitions.HyperplanePolyhedron
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Box_S`: the `S`-band intersection of a zonotope

[1, Prop. 2]: for a zonotope `Z = (u, ⟨v₁, …, v_m⟩)` and a finite set `S` of directions,
`Box_S(Z) = [m, M]_S` ([1, Def. 2], `ContSet.hyperplanePolyhedron`) with
`m_s = s·u - Σⱼ |s·vⱼ|` and `M_s = s·u + Σⱼ |s·vⱼ|`, the least and greatest values of
`s·x` over `Z`. At the coordinate vectors it is the interval hull, `Zonotope.interval`.
The dot products are written `u ⬝ᵥ s`, the order `hyperplanePolyhedron` uses.

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

/-- [1, Prop. 2]: `[m, M]_S`, `m_s = s·u - Σⱼ |s·vⱼ|`, `M_s = s·u + Σⱼ |s·vⱼ|`. -/
def Zonotope.boxS (Z : Zonotope (Vec ℝ n)) (S : Finset (Vec ℝ n)) : Set (Vec ℝ n) :=
  let m := fun s => Z.c ⬝ᵥ s - ∑ j, |Z.G j ⬝ᵥ s|                    -- mᵢ = sᵢ·u - Σⱼ |sᵢ·vⱼ|
  let M := fun s => Z.c ⬝ᵥ s + ∑ j, |Z.G j ⬝ᵥ s|                    -- Mᵢ = sᵢ·u + Σⱼ |sᵢ·vⱼ|
  ContSet.hyperplanePolyhedron S m M                                -- [m, M]_S

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
