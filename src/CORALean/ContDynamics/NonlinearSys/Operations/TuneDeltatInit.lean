import CORALean.ContDynamics.NonlinearSys.Operations.GainMax

/-!
# `Alg. 2` lines 3-7: the first step's search for `Δ`

`tuneDeltatInit`: [1, Alg. 2] lines 3-7, shrink `Δ` by `ζ_δ` until the gain it yields reaches `ζ_Δ`,
and `none` once `fuel` shrinkings have not.

Line 3 is printed as a `while`, testing `φ₁` before lines 5-6 have ever
computed one; read as the `repeat … until` the prose describes, which is the
only reading under which the first step has a `φ₁` to test. See the
reference page.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-7: shrink `Δ` by `ζ_δ` until the gain it yields reaches `ζ_Δ`, and
`none` once `fuel` shrinkings have not. -/
noncomputable def tuneDeltatInit (le : ℝ → ℝ → Bool) (dabs : ℝ → Fin n → ℝ) (ζδ ζΔ : ℝ) :
    ℝ → ℕ → Option (ℝ × ℝ)
  | _, 0 => none
  | Δ, k + 1 =>
    let Δnext := ζδ * Δ                                        -- 4. Δ ← ζ_δ Δ
    let dΔ := dabs Δnext                                       -- 5. d(box(R_abs(Δ)))
    let dδΔ := dabs (ζδ * Δnext)                               -- 5. d(box(R_abs(ζ_δ Δ)))
    let φ1 := gainMax le dΔ dδΔ                                -- 6. φ₁ by (25)
    if le ζΔ φ1 then some (Δnext, φ1)                          -- 3. while φ₁ < ζ_Δ
    else tuneDeltatInit le dabs ζδ ζΔ Δnext k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
