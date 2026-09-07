import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachForallInner
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffRepInner

/-!
# `backReachForall` at `Zonotope`, with both operation hypotheses discharged

The representation that can run a backward step today: `mtimes_exact` gives
`hinv`, which `mtimes_outer` alone never could, and `minkDiffRep_inner` gives
`hdiff` at any family `M` of generator representations — a wrong `M` yields
`none` and the run stops there. So a caller is left with `hA`, and with
choosing `M`.

`M` is a family and not one matrix: which sets the steps produce is not known
before the run, and `minkDiffRep`'s argument is indexed by the generator counts
of the particular pair it is handed.

`Interval` cannot take this place. It has the `MinkDiff` instance, so `hdiff`
is free there, but its `mtimes` is an enclosure and carries no exactness
theorem to read `hinv` off.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Mtimes

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.backReachForall_inner_zonotope (sys : LinearSysDT ℝ n) {Ainv : Mat ℝ n n}
    (hA : sys.A * Ainv = 1) (M : (Z₁ Z₂ : Zonotope (Vec ℝ n)) → Fin Z₁.h → Fin Z₂.h → ℝ)
    (T U : Zonotope (Vec ℝ n)) (k : ℕ) (R : Zonotope (Vec ℝ n))
    (hR : sys.backReachForall (S := 𝒵) Ainv (fun Z₁ Z₂ => Z₁.minkDiffRep Z₂ (M Z₁ Z₂))
      T U k = some R) :
    construct R ⊆ sys.backReachSetForall (S := 𝒵) T U k := by -- --- PROOF ---
  refine sys.backReachForall_inner (S := 𝒵) ?_ ?_ ?_ T U k R hR
  · simpa using hA
  -- the difference: sound at whatever `M` the caller picked, or `none`
  · exact fun B V D hD => Zonotope.minkDiffRep_inner B V (M B V) hD
  -- the preimage: the inner half of an exact `mtimes`, which is the one at risk
  · intro s
    rw [Scalar.toRealMat_real]
    exact (Zonotope.mtimes_exact Ainv s).symm.subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
