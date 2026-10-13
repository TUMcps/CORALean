module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `NonlinDASys.jointReachSet`

[1, Prop. 2]: the reachable set of the differential and algebraic variables together,

`R(τₖ) = ([c_d; c_a], [G_d 0 0; -F⁻¹D G_d  -F⁻¹E G_u  -F⁻¹G_l])`,
`c_a = y* - F⁻¹(g(z*) + D(c_d - x*) + E(c_u - u*) + c_l)`,

from `Rᵈ(τₖ) = (c_d, G_d)`, `U = (c_u, G_u)` and the algebraic linearization errors
`L̄ᵃ = (c_l, G_l)`. The algebraic part is [1, Eq. 19], `Rᵃ(τₖ)`, kept correlated with the
differential part through the shared generators `G_d`: tighter than `Rᵈ(τₖ) × Rᵃ(τₖ)`, which
would repeat them. CORA builds the same zonotope as `R_xy` in `nonlinDASys`'s
`priv_linError_mixed_noInt`.

Over the product `Vec ℝ n × Vec ℝ p` rather than the stacked `ℝ^{n+p}`; a generator column
`[a; b]` is the pair `(a, b)`. `F⁻¹` is a parameter.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 2]: `R(τₖ) = ([c_d; c_a], [G_d 0 0; -F⁻¹D G_d -F⁻¹E G_u -F⁻¹G_l])`. -/
def NonlinDASys.jointReachSet (xs : Vec ℝ n) (ys : Vec ℝ p) (us : Vec ℝ m) (g₀ : Vec ℝ p)
    (D : Mat ℝ p n) (E : Mat ℝ p m) (F_inv : Mat ℝ p p) (R_d : Zonotope (Vec ℝ n))
    (U : Zonotope (Vec ℝ m)) (L_a : Zonotope (Vec ℝ p)) : Zonotope (Vec ℝ n × Vec ℝ p) :=
  let c_d : Vec ℝ n := R_d.c                                                    -- c_d
  let c_a : Vec ℝ p :=                                                          -- c_a
    ys - F_inv *ᵥ (g₀ + D *ᵥ (R_d.c - xs) + E *ᵥ (U.c - us) + L_a.c)
  let G_d : Fin R_d.h → Vec ℝ n × Vec ℝ p := fun j => (R_d.G j, -((F_inv * D) *ᵥ R_d.G j))
  let G_u : Fin U.h → Vec ℝ n × Vec ℝ p := fun j => (0, -((F_inv * E) *ᵥ U.G j))
  let G_l : Fin L_a.h → Vec ℝ n × Vec ℝ p := fun j => (0, -(F_inv *ᵥ L_a.G j))
  ⟨R_d.h + U.h + L_a.h, (c_d, c_a), Fin.append (Fin.append G_d G_u) G_l⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
