module

public import CORALean.ContSet.Ellipsoid.Real.Operations.NormExact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsGreatestRadius

@[expose] public section

/-!
# `norm_` of an ellipsoid centered at the origin is its largest Euclidean norm

CORA's `norm_(E, 2)` for `q = 0` is `sqrt(max(eig(Q)))`. It is exact: the greatest Euclidean
norm of a point of the ellipsoid, attained. This is `Ellipsoid.isGreatest_radius` read at the
center `0`. The upper bound `Ellipsoid.normUb` is the float-capable counterpart; it is not this
value.

## Inputs
* `E` – ellipsoid

## Hypotheses
* `hn` – `1 ≤ n`
* `hq` – the center is the origin

## Conclusion
* `normExact` is the greatest norm on `E`
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isGreatest_normExact (E : Ellipsoid n) (hn : 1 ≤ n) (hq : E.q = 0) :
    IsGreatest ((fun x => ‖x‖₂) '' E.construct) (E.normExact hn) := by
  have h := Ellipsoid.isGreatest_radius E hn
  have hf : (fun x : Vec ℝ n => ‖x‖₂) = fun x => ‖x - E.q‖₂ := by simp [hq]
  rw [hf]
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
