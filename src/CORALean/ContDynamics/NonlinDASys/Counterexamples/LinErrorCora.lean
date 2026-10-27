module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinErrorOuter

@[expose] public section

/-!
# `NonlinDASys.linErrorCora`

The set of linearization errors as CORA's `nonlinDASys` computes it, in
`private/priv_linError_mixed_noInt.m` (and alike in `priv_linError`, `priv_linError_thirdOrder`,
`priv_abstractionError_adaptive`): `error_mid = error_x_mid + CF_inv*error_y_mid` and
`error_rad = error_x_rad_zono + CF_inv*error_y_rad_zono`, where [1, Cor. 1]
(`NonlinDASys.linError`) has `d - CF⁻¹e`, `H - CF⁻¹V` and `-CF⁻¹`. The algebraic error enters the
dynamics as `-C F⁻¹ ℓᵃ` ([1, Eq. 13]); only the dynamics' error flips it. On the symmetric radius
part the sign makes no difference; on the midpoint part it does
(`NonlinDASys.linErrorCora_counterexample`). The reduction before `quadMap` is left out.

# CORA's `nonlinDASys` linearization error misses the error

`NonlinDASys.linErrorCora`, CORA's `error_mid + error_rad` with `+ CF_inv` on the algebraic part,
against [1, Cor. 1] with `- CF⁻¹`. The system `ẋ = y`, `0 = y - x²` (index 1, `F = 1`), linearized
at `z* = 0`: `A = 0`, `C = 1`, `D = 0`, so `C F⁻¹ = 1`, and the Hessians are `Hᵈ = 0` and `Hᵃ = -2`
in the `x` direction (`R^z_Δ = [-1, 1]`). On the constraint `y = x²`, so `ẋ = x²` while the
linearization gives `0`: the error at `x = 1` is `1`. [1, Cor. 1] holds it,
`½ (σ - CF⁻¹φ) = ½ (0 - (-2)) = 1`; CORA's set is `½ (0 + (-2) [0, 1]) = [-1, 0]` and does not.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the true error lies in the paper's set but not in CORA's

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n p q : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
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

namespace CORALean

open CORALean.Real Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The linearization error `½ (σ - CF⁻¹φ) = 1` of `ẋ = y`, `0 = y - x²` at `z* = 0`, `ν = 1`,
lies in [1, Cor. 1]'s set and not in CORA's. -/
theorem NonlinDASys.linErrorCora_counterexample : -- --- CONCL ---
    let w := (fun _ : Fin 1 => (![1] : Vec ℝ 1) ⬝ᵥ ((0 : Mat ℝ 1 1) *ᵥ ![1])) -
        (1 : Mat ℝ 1 1) *ᵥ (fun _ : Fin 1 => (![1] : Vec ℝ 1) ⬝ᵥ (!![-2] *ᵥ ![1]))
    (1 / 2 : ℝ) • w
      ∈ (NonlinDASys.linError (p := 1) (q := 1) 0 0 (fun _ => !![-2]) 0 1
          ⟨1, 0, fun _ => ![1]⟩).construct ∧
    (1 / 2 : ℝ) • w
      ∉ (NonlinDASys.linErrorCora (p := 1) (q := 1) 0 0 (fun _ => !![-2]) 0 1
          ⟨1, 0, fun _ => ![1]⟩).construct := by -- --- PROOF ---
  intro w
  refine ⟨NonlinDASys.linError_outer _ _ _ _ _ _ (by simp) (by simp)
    ⟨fun _ => 1, fun _ => by simp, by funext i; fin_cases i; simp⟩, ?_⟩
  -- the error is `1`
  have hP : (1 / 2 : ℝ) • w
      = fun _ => 1 := by
    funext i
    simp [w, dotProduct, mulVec]
  rw [hP]
  -- every point of CORA's set has its coordinate at most `0`
  rintro ⟨β, hβ, hx⟩
  change _ = _ + ∑ j : Fin 5, β j • _ at hx
  have h0 := congrFun hx 0
  simp [NonlinDASys.linErrorCora, Zonotope.quadMap, Zonotope.plus, Zonotope.mtimes,
    Interval.zonotope, Zonotope.absBound, Fin.sum_univ_succ, dotProduct, mulVec, Fin.append,
    Fin.addCases] at h0
  have hb := abs_le.mp (hβ (1 : Fin 5))
  -- the pair generator of a one-generator zonotope is `0`
  split_ifs at h0 with hc
  · exact absurd hc (by
      rw [Subsingleton.elim (finProdFinEquiv.symm (0 : Fin (1 * 1))).2
        (finProdFinEquiv.symm (0 : Fin (1 * 1))).1]
      exact lt_irrefl _)
  · linarith [hb.1, hb.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
