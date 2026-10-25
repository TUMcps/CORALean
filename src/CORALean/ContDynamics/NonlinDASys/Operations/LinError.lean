module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `NonlinDASys.linError`

[1, Cor. 1]: the set of linearization errors `L` of [1, Eq. 15] over the zonotope `R^z_Δ` of
deviations `ν = z - z*`, the Hessians bounded by interval matrices `Hᵈ = Hᵈ_c ⊕ [-Hᵈ_Δ, Hᵈ_Δ]`
and `Hᵃ = Hᵃ_c ⊕ [-Hᵃ_Δ, Hᵃ_Δ]`: `L = ½ (d - CF⁻¹e, H - CF⁻¹V) ⊕ ½ ([-ζ, ζ] ⊕ (-CF⁻¹)[-ϱ, ϱ])`,
with `(d, H) = quad(Hᵈ_c, R^z_Δ)`, `(e, V) = quad(Hᵃ_c, R^z_Δ)` ([1, Lemma 1]) and
`ζ`, `ϱ` the radius terms ([1, Thm. 1]). The first part `L_c` subtracts `CF⁻¹` times the algebraic
quadratic map generator by generator, which keeps `σ` and `φ` correlated; the second part `L_Δ` is
symmetric. `CF⁻¹` is the matrix `C F⁻¹` of [1, Eq. 14], a parameter. CORA's `nonlinDASys` adds
`CF_inv` times the algebraic part where this subtracts it (`NonlinDASys.linErrorCora`).

## Inputs
* `Hd_c` – dynamics Hessian midpoints
* `Hd_Δ` – dynamics Hessian radii
* `Ha_c` – constraint Hessian midpoints
* `Ha_Δ` – constraint Hessian radii
* `CF_inv` – the matrix `C F⁻¹`
* `R_Δ` – deviation zonotope

## Output
* the zonotope of linearization errors

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 2014.
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

/-- [1, Cor. 1]: `L = L_c ⊕ L_Δ`, `L_c = ½ (d - CF⁻¹e, H - CF⁻¹V)`,
`L_Δ = ½ ([-ζ, ζ] ⊕ (-CF⁻¹)[-ϱ, ϱ])`. -/
noncomputable def NonlinDASys.linError (Hd_c Hd_Δ : Fin n → Mat ℝ q q)
    (Ha_c Ha_Δ : Fin p → Mat ℝ q q) (CF_inv : Mat ℝ n p) (R_Δ : Zonotope (Vec ℝ q)) :
    Zonotope (Vec ℝ n) :=
  let L_dc : Zonotope (Vec ℝ n) := R_Δ.quadMap Hd_c                     -- (d, H)
  let L_ac : Zonotope (Vec ℝ p) := R_Δ.quadMap Ha_c                     -- (e, V)
  let L_c : Zonotope (Vec ℝ n) :=                                       -- ½ (d - CF⁻¹e, H - CF⁻¹V)
    ⟨L_dc.h, (1 / 2 : ℝ) • (L_dc.c - CF_inv *ᵥ L_ac.c),
      fun j => (1 / 2 : ℝ) • (L_dc.G j - CF_inv *ᵥ L_ac.G j)⟩
  let ζ : Vec ℝ n := fun i => R_Δ.absBound ⬝ᵥ (Hd_Δ i *ᵥ R_Δ.absBound)  -- ζ = |R|ᵀ Hᵈ_Δ |R|
  let ϱ : Vec ℝ p := fun j => R_Δ.absBound ⬝ᵥ (Ha_Δ j *ᵥ R_Δ.absBound)  -- ϱ = |R|ᵀ Hᵃ_Δ |R|
  let L_Δ : Zonotope (Vec ℝ n) :=                             -- ½ ([-ζ, ζ] ⊕ (-CF⁻¹)[-ϱ, ϱ])
    ((Interval.zonotope ⟨-ζ, ζ⟩).plus ((Interval.zonotope ⟨-ϱ, ϱ⟩).mtimes (-CF_inv))).mtimes
      ((1 / 2 : ℝ) • (1 : Mat ℝ n n))
  L_c.plus L_Δ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
