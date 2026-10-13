import CORALean.ContDynamics.NonlinDASys.NonlinDASys
import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope

/-!
# `NonlinDASys.linErrorCora`

The set of linearization errors as CORA's `nonlinDASys` computes it, in
`private/priv_linError_mixed_noInt.m` (and alike in `priv_linError`, `priv_linError_thirdOrder`,
`priv_abstractionError_adaptive`): `error_mid = error_x_mid + CF_inv*error_y_mid` and
`error_rad = error_x_rad_zono + CF_inv*error_y_rad_zono`, that is

`½ (d + CF⁻¹e, H + CF⁻¹V) ⊕ ½ ([-ζ, ζ] ⊕ CF⁻¹[-ϱ, ϱ])`

where [1, Cor. 1] (`NonlinDASys.linError`) has `d - CF⁻¹e`, `H - CF⁻¹V` and `-CF⁻¹`. The
algebraic error enters the dynamics as `-C F⁻¹ ℓᵃ` ([1, Eq. 13]), and CORA's own algebraic set
`R_y = p.y + (-F_inv)*(f0_con + D*R + E*U + error_y)` has the minus; only the dynamics' error
flips it. On the symmetric radius part the sign makes no difference; on the midpoint part it
does (`NonlinDASys.linErrorCora_counterexample`). The radius `|R^z_Δ|` stands for CORA's
`dz_abs`, the absolute bound of the box of the deviations; the reduction CORA applies before
`quadMap` is left out.

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

variable {n p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `nonlinDASys` linearization error,
`½ (d + CF⁻¹e, H + CF⁻¹V) ⊕ ½ ([-ζ, ζ] ⊕ CF⁻¹[-ϱ, ϱ])`: [1, Cor. 1] with `CF⁻¹`'s sign flipped. -/
noncomputable def NonlinDASys.linErrorCora (Hd_c Hd_Δ : Fin n → Mat ℝ q q)
    (Ha_c Ha_Δ : Fin p → Mat ℝ q q) (CF_inv : Mat ℝ n p) (R_Δ : Zonotope (Vec ℝ q)) :
    Zonotope (Vec ℝ n) :=
  let L_dc : Zonotope (Vec ℝ n) := R_Δ.quadMap Hd_c                     -- (d, H)
  let L_ac : Zonotope (Vec ℝ p) := R_Δ.quadMap Ha_c                     -- (e, V)
  let L_c : Zonotope (Vec ℝ n) :=                                       -- error_mid, with `+`
    ⟨L_dc.h, (1 / 2 : ℝ) • (L_dc.c + CF_inv *ᵥ L_ac.c),
      fun j => (1 / 2 : ℝ) • (L_dc.G j + CF_inv *ᵥ L_ac.G j)⟩
  let ζ : Vec ℝ n := fun i => R_Δ.absBound ⬝ᵥ (Hd_Δ i *ᵥ R_Δ.absBound)  -- ζ = |R|ᵀ Hᵈ_Δ |R|
  let ϱ : Vec ℝ p := fun j => R_Δ.absBound ⬝ᵥ (Ha_Δ j *ᵥ R_Δ.absBound)  -- ϱ = |R|ᵀ Hᵃ_Δ |R|
  let L_Δ : Zonotope (Vec ℝ n) :=                                       -- error_rad, with `+`
    ((Interval.zonotope ⟨-ζ, ζ⟩).plus ((Interval.zonotope ⟨-ϱ, ϱ⟩).mtimes CF_inv)).mtimes
      ((1 / 2 : ℝ) • (1 : Mat ℝ n n))
  L_c.plus L_Δ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
