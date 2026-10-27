module

public import CORALean.ContSet.Zonotope.Real.Operations.ContainsST
public import CORALean.ContSet.Zonotope.Real.Theorems.SubsetOfCert

@[expose] public section

/-!
# `containsST` is sound

Whatever the solver returns: `true` means the checked candidate meets `[1, Thm. 3]`,
and that theorem gives the containment.

## Inputs
* `lp` – linear-program solver
* `Zy` – outer zonotope
* `Zx` – inner zonotope

## Hypotheses
* `h` – the test returns true

## Conclusion
* the inner zonotope lies in the outer one

## References

* [1] [S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". 2019 IEEE
      58th Conference on Decision and Control (CDC),
      2019.](../../../../../../references/2019/sadraddini-cdc-polytope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] [DecidableEq α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.containsST_sound
    (lp : (Zy Zx : Zonotope α) → Option (Mat ℝ Zy.h Zx.h × Vec ℝ Zy.h)) (Zy Zx : Zonotope α)
    (h : Zonotope.containsST lp Zy Zx = true) : -- --- CONCL ---
    Zx.construct ⊆ Zy.construct := by -- --- PROOF ---
  unfold Zonotope.containsST at h
  split at h
  · exact absurd h Bool.false_ne_true
  · split_ifs at h with hc
    exact Zonotope.construct_subset_of_cert Zx Zy _ _ hc.1 hc.2.1 hc.2.2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
