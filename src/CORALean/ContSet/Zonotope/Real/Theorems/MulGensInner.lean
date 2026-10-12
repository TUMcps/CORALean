import CORALean.ContSet.Zonotope.Real.Operations.MulGens
import CORALean.ContSet.Zonotope.Real.Theorems.SubsetOfCert

/-!
# `mulGens` with `‖T‖∞ ≤ 1` is an inner-approximation

[1, Eq. (1)], the sufficient containment condition of [2, Thm. 3]: if `Ĝ = G T` and every
row of `T` has absolute sum at most `1` (`‖T‖∞ ≤ 1`), then `⟨c, Ĝ⟩ ⊆ ⟨c, G⟩`. It is [2, Thm. 3]
at `β = 0` (`construct_subset_of_cert`).

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
* [2] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. (1)]: `‖T‖∞ ≤ 1` gives `⟨c, G T⟩ ⊆ ⟨c, G⟩`. -/
theorem Zonotope.mulGens_inner (Z : Zonotope α) {r : ℕ} (T : Mat ℝ Z.h r)
    (hT : ∀ i, ∑ j, |T i j| ≤ 1) : (Z.mulGens T).construct ⊆ Z.construct := by -- --- PROOF ---
  -- [2, Thm. 3] at `Γ := T`, `β := 0`: the centres agree
  refine Zonotope.construct_subset_of_cert (Z.mulGens T) Z T 0 (fun j => ?_) ?_ (fun k => ?_)
  · simp [Zonotope.mulGens]
  · simp [Zonotope.mulGens]
  · simp only [Pi.zero_apply, abs_zero, add_zero]
    exact hT k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
