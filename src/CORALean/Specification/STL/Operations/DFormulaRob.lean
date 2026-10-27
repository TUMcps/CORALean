module

public import CORALean.Specification.STL.Definitions.DiscreteFormula

@[expose] public section

/-!
# `STL.DFormula.rob`

[1, Sec. II-C]: the robustness `ρ` of a discrete-time formula, by `min` and `max` along the
recursion of its satisfaction; the paper prints no `ρ` of `◇`, which is taken as the `max` dual to
`□`.

Real-only, a specification: the robustness is a real number ranking the run against the formula,
and the formulas it is stated for have no float version.

## Inputs
* none

## Output
* the robustness of `φ` along `x` at step `t`

## References

* [1] [V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and S. A. Seshia.
      "Model Predictive Control with Signal Temporal Logic Specifications". 53rd IEEE Conference on
      Decision and Control, 2014.](../../../../../references/2014/raman-cdc-mpc-stl.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ρ^φ(x, t)`, [1, Sec. II-C]. -/
noncomputable def STL.DFormula.rob : STL.DFormula X → (ℕ → X) → ℕ → ℝ
  | .pred μ, x, t => μ (x t)
  | .npred μ, x, t => -μ (x t)
  | .and φ ψ, x, t => min (φ.rob x t) (ψ.rob x t)
  | .or φ ψ, x, t => max (φ.rob x t) (ψ.rob x t)
  | .always a b hab φ, x, t =>
      (Finset.Icc (t + a) (t + b)).inf' (Finset.nonempty_Icc.mpr (by omega)) fun t' => φ.rob x t'
  | .eventually a b hab φ, x, t =>
      (Finset.Icc (t + a) (t + b)).sup' (Finset.nonempty_Icc.mpr (by omega)) fun t' => φ.rob x t'
  | .until a b hab φ ψ, x, t =>
      (Finset.Icc (t + a) (t + b)).attach.sup'
        (Finset.attach_nonempty_iff.mpr (Finset.nonempty_Icc.mpr (by omega))) fun t' =>
          min (ψ.rob x t'.1) ((Finset.Icc t t'.1).inf'
            (Finset.nonempty_Icc.mpr (by have := (Finset.mem_Icc.mp t'.2).1; omega))
            fun t'' => φ.rob x t'')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
