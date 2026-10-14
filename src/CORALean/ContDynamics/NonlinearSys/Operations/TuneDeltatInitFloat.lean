module

public import CORALean.ContDynamics.NonlinearSys.Definitions.TunedStep
public import CORALean.ContDynamics.NonlinearSys.Operations.GainMaxFloat

@[expose] public section

/-!
# `Alg. 2` lines 3-7: the first step's search for `Δ`, in floats

`tuneDeltatInit` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no
soundness statement reads it, so every rounding is upward and no theorem is owed. What a run
guarantees holds for whatever this returns. See [1].

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-7: shrink `Δ` by `ζ_δ` until the gain it yields reaches `ζ_Δ`, and
`none` once `fuel` shrinkings have not. -/
def tuneDeltatInitFloat {n : ℕ} (dabs : 𝕋 → Fin n → 𝕋) (ζδ ζΔ : 𝕋) :
    𝕋 → ℕ → Option (NonlinearSys.TunedStep 𝕋)
  | _, 0 => none
  | Δ, k + 1 =>
    let Δnext := mulUp ζδ Δ                                      -- 4. Δ ← ζ_δ Δ
    let dΔ := dabs Δnext                                         -- 5. d(box(R_abs(Δ)))
    let dδΔ := dabs (mulUp ζδ Δnext)                             -- 5. d(box(R_abs(ζ_δ Δ)))
    let φ1 := gainMaxFloat dΔ dδΔ                                -- 6. φ₁ by (25)
    if le ζΔ φ1 then some ⟨Δnext, φ1⟩                            -- 3. while φ₁ < ζ_Δ
    else tuneDeltatInitFloat dabs ζδ ζΔ Δnext k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
