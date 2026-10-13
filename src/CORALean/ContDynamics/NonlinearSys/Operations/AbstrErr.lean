module

public import CORALean.ContDynamics.LinearSys.Operations.PostDelta
public import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.VarInputs
public import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Instances
public import CORALean.Global.Block

@[expose] public section

/-!
# `abstrErr`, the abstraction error of one step

`[2, Alg. 2]` assembled out of the three operations `[2]` says are `[1, Sec. 4.1]`'s
and `[1, Eq. 7]`'s: the state differences a step spans, the values its varying
input part takes over them, and the remainder the third-order term leaves. Alg. 2's `×U` is a
Cartesian product taken inside `Vec ℝ (n + m)` rather than in a pair type,
`blockPadLeft`/`blockPadRight` embedding each half.

`Z` is the region the remainder is taken over, supplied rather than computed, as
`lagrangeRemainder` and `abstrErrLin` already take theirs. Alg. 2 computes it in
its lines 3, 5 and 6, and line 5 as printed adds a set of `ℝⁿ` to one of
`ℝⁿ⁺ᵐ`; more to the point, the `zono` it goes through is the one step of Alg. 2
whose property (6) its *implementation* does not have, `zonotope_not_mono`.
Supplying it is what keeps `[2, Lemma 3]`'s proof here, `abstrErr_mono`, from
resting on an assumption this tree can refute.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
* [2] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

open Matrix Scalar

variable {n m : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The abstraction error one step leaves, from the reachable set `R` and the
applied error `Ψ` it is run at, over the region `Z`. -/
noncomputable def abstrErr (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ) (B : Mat ℝ n m)
    (D : Fin n → Mat ℝ (n + m) (n + m)) (E : Fin n → Fin (n + m) → Mat ℝ (n + m) (n + m))
    (U UΔ : PolyZonotope (Vec ℝ m)) (Z : Zonotope (Vec ℝ (n + m))) (zs : Vec ℝ (n + m))
    (R Ψ : PolyZonotope (Vec ℝ n)) : PolyZonotope (Vec ℝ n) :=
  (varInputs B D ((R.map (blockPadLeft n m)).plus (U.map (blockPadRight n m)))
      (((sys.postDelta (S := 𝒫𝒵) r η R Ψ).map (blockPadLeft n m)).plus
        (UΔ.map (blockPadRight n m))) UΔ).plus (lagrangeRemainder E Z zs).polyZonotope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
