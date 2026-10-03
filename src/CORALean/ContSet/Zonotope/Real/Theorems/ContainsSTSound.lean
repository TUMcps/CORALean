import CORALean.ContSet.Zonotope.Real.Operations.ContainsST
import CORALean.ContSet.Zonotope.Real.Theorems.SubsetOfCert

/-!
# `containsST` is sound

Whatever the solver returns: `true` means the checked candidate meets `[1, Thm. 3]`,
and that theorem gives the containment.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] [DecidableEq α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.containsST_sound
    (lp : (Zy Zx : Zonotope α) → Option (Mat ℝ Zy.h Zx.h × Vec ℝ Zy.h)) (Zy Zx : Zonotope α)
    (h : Zonotope.containsST lp Zy Zx = true) :
    Zx.construct ⊆ Zy.construct := by -- --- PROOF ---
  unfold Zonotope.containsST at h
  split at h
  · exact absurd h Bool.false_ne_true
  · split_ifs at h with hc
    exact Zonotope.construct_subset_of_cert Zx Zy _ _ hc.1 hc.2.1 hc.2.2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
