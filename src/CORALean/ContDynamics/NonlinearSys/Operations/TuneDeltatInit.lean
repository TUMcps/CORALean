module

public import CORALean.ContDynamics.NonlinearSys.Definitions.TunedStep
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `Alg. 2` lines 3-7: the first step's search for `Δ`

`tuneDeltatInit`: [1, Alg. 2] lines 3-7, shrink `Δ` by `ζ_δ` until the gain it yields reaches `ζ_Δ`,
and `none` once `fuel` shrinkings have not.

Line 3 is printed as a `while`, testing `φ₁` before lines 5-6 have ever
computed one; read as the `repeat … until` the prose describes, which is the
only reading under which the first step has a `φ₁` to test. See the
reference page.

## Inputs
* `le` – comparison of reals
* `dabs` – box diameter of the abstraction error
* `ζδ` – limit gain
* `ζΔ` – gain threshold

## Output
* the first step's horizon and gain, or none

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for Reachability
      Analysis of Nonlinear Systems". Proceedings of the 24th International Conference on Hybrid
      Systems: Computation and Control,
      2021.](../../../../../references/2021/wetzlinger-hscc-adaptive-tuning-nonlinear.md)
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5
-- Written:       18-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `φ(Δt)` of eq. (25): the worst dimension's ratio of the two error widths,
picked out by the caller's `le`. -/
noncomputable def aux_gainMax (le : ℝ → ℝ → Bool) (d dδ : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl (fun φ i => if le φ (dδ i / d i) then dδ i / d i else φ) 0


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-7: shrink `Δ` by `ζ_δ` until the gain it yields reaches `ζ_Δ`, and
`none` once `fuel` shrinkings have not. -/
noncomputable def tuneDeltatInit (le : ℝ → ℝ → Bool) (dabs : ℝ → Fin n → ℝ) (ζδ ζΔ : ℝ) :
    ℝ → ℕ → Option (NonlinearSys.TunedStep ℝ)
  | _, 0 => none
  | Δ, k + 1 =>
    let Δnext := ζδ * Δ                                        -- 4. Δ ← ζ_δ Δ
    let dΔ := dabs Δnext                                       -- 5. d(box(R_abs(Δ)))
    let dδΔ := dabs (ζδ * Δnext)                               -- 5. d(box(R_abs(ζ_δ Δ)))
    let φ1 := aux_gainMax le dΔ dδΔ                                -- 6. φ₁ by (25)
    if le ζΔ φ1 then some ⟨Δnext, φ1⟩                          -- 3. while φ₁ < ζ_Δ
    else tuneDeltatInit le dabs ζδ ζΔ Δnext k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
