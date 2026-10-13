module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import CORALean.ContSet.Interval.Real.Operations.Tanh
public import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact

@[expose] public section

/-!
# `Interval.tanh` is exactly the image under `Real.tanh`

The hyperbolic tangent is strictly increasing and continuous on all of `ℝ`, so
`Interval.monotoneImage_exact` applies. No domain condition.

[1, Eq. 7].

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_tanh_strictMono : StrictMono Real.tanh := by -- --- PROOF ---
  intro a b hab
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_lt_div_iff₀ (Real.cosh_pos a) (Real.cosh_pos b)]
  have h : 0 < Real.sinh (b - a) := Real.sinh_pos_iff.2 (sub_pos.2 hab)
  rw [Real.sinh_sub] at h
  linarith

theorem aux_tanh_continuous : Continuous Real.tanh := by
  have : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [this]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.tanh_exact (I : Interval (Vec ℝ n)) :
    I.tanh.construct = (fun x i => Real.tanh (x i)) '' I.construct := by
  exact Interval.monotoneImage_exact Real.tanh (Set.univ) Set.ordConnected_univ
    (fun a _ b _ h => aux_tanh_strictMono h) (aux_tanh_continuous.continuousOn)
    I (fun i => ⟨trivial, trivial⟩)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
