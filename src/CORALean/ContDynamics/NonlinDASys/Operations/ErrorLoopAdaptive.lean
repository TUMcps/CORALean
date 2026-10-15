module

public import CORALean.ContDynamics.NonlinDASys.Operations.LinReachAt
public import CORALean.ContDynamics.NonlinDASys.Operations.AbstractionErrorAdaptive
public import CORALean.ContDynamics.NonlinDASys.Definitions.AdaptTuning
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `NonlinDASys.errorLoopAdaptive`

[1, Alg. 1] lines 4-10, `repeat … until L ⊆ L̄`, as CORA's `linReach_adaptive` runs it (the
tuning of [2] applied to [1]); each step carries its line number. Line 3's `taylor` is the
argument. Where it departs from the listing, it follows CORA. Line 5: the guess is not
`ĉ ⊕ λ(L̃ ⊕ (-ĉ))` (17) but the origin-centred boxes `L̄ᵈ`, `L̄ᵃ` of `expFactor` (`λ`) times the
last error's size `errorInt`, joined through `-CF⁻¹` as (15) joins `σ` and `φ`; the first pass
starts from the caller's `adm_x`, `adm_y`, not line 1's `{0}`. Lines 6-7 are one `linReachAt`
at `Ū`. Line 10: `L ⊆ L̄` part by part, `errorInt ≤ adm` — CORA's `perfInd <= 1` without the
division, which in Lean (`x/0 = 0`) would accept any error where `adm` is `0`; there is no
`L_max` exit and no split (lines 11-16), `fuel` replacing both with `none`. `L̄ᵃ` enters with
`-CF⁻¹` where CORA adds it (`references/coverage/contDynamics/nonlinDASys.md`, row
`linReach_adaptive`).

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
* [2] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for Reachability
      Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

variable {n p m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] lines 4-10 at line 3's `taylor`, from `Rd_tk = Rᵈ(t_k)` with step `r`: the error
`L` of the first pass with `L ⊆ L̄`, `L̄` growing to `expFactor` times `L`; `none` after `fuel`. -/
noncomputable def NonlinDASys.errorLoopAdaptive (sys : NonlinDASys n p m)
    (T : NonlinDASys.AdaptTuning n p m q) (taylor : NonlinDASys.LinPoint n p m)
    (Rd_tk : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m)) (r : ℝ) (η : ℕ) :
    ℕ → Vec ℝ n → Vec ℝ p → Option (NonlinDASys.AbstractionError n p)
  | 0, _, _ => none
  -- 4. `repeat`
  | fuel + 1, adm_x, adm_y =>
    -- 5. `L̄ᵈ`
    let Lbar_d : Zonotope (Vec ℝ n) := Interval.zonotope ⟨-adm_x, adm_x⟩
    -- 5. `L̄ᵃ`
    let Lbar_a : Zonotope (Vec ℝ p) := Interval.zonotope ⟨-adm_y, adm_y⟩
    -- 5. `L̄ = L̄ᵈ ⊕ (-CF⁻¹)L̄ᵃ`
    let Lbar : Zonotope (Vec ℝ n) :=
      Lbar_d.plus (Lbar_a.mtimes (-(taylor.C * taylor.F_inv)))
    -- 6. `Ū`, 7. `Rᵈ(τ_k)`
    let R := NonlinDASys.linReachAt sys { taylor with Verror := Lbar, Verror_y := Lbar_a }
      Rd_tk U r η
    -- 8. `R(τ_k)`, Prop. 2
    let R_τk := R.2.2
    -- 9. `L`, Cor. 1
    let L := NonlinDASys.abstractionErrorAdaptive (taylor.C * taylor.F_inv)
      (T.hess R_τk)
    -- 10. `until L ⊆ L̄`
    if (List.finRange n).all (fun i => T.le (L.errorInt_x i) (adm_x i)) &&
        (List.finRange p).all (fun j => T.le (L.errorInt_y j) (adm_y j)) then
      some L
    else
      -- 5. the next `L̄` from `L`
      sys.errorLoopAdaptive T taylor Rd_tk U r η fuel
        (T.expFactor • L.errorInt_x) (T.expFactor • L.errorInt_y)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
