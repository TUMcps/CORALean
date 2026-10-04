import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStep
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.Zonotope.Real.Theorems.IntersectStripOuter
import CORALean.ContSet.Zonotope.Real.Theorems.IntersectStripSeqOuter

/-!
# One observer step encloses the states the measurement allows

[1, Alg. 1]: if `X̂` holds every state `S` might be in, the step's result holds every
`A x + u + ω` with `x ∈ S`, `ω ∈ W`, that lies in the measurement strips. The prediction
is exact ([1, Eq. 2], `mtimes_exact` and `plus_exact`), the update outer
(`intersectStripSeq_outer`, [1, Eq. 3], or `intersectStrip_outer` all at once), for every gain.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real

variable {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observeStep_outer (sys : LinearSysDT ℝ n) (C : Mat ℝ p n) (σ : Vec ℝ p)
    (W : Zonotope (Vec ℝ n)) (options : LinearSysDT.ObserveStripOptions n p) (u : Vec ℝ n)
    (y : Vec ℝ p) (Xhat : Zonotope (Vec ℝ n)) {S : Set (Vec ℝ n)} (hS : S ⊆ Xhat.construct) :
    ((fun x => sys.A *ᵥ x + u) '' S + W.construct) ∩ {x | ∀ i, |(C *ᵥ x - y) i| ≤ σ i} ⊆
      (sys.observeStep C σ W options u y Xhat).construct := by -- --- PROOF ---
  -- the prediction holds every predicted state
  have hpred : (fun x => sys.A *ᵥ x + u) '' S + W.construct ⊆
      (((Xhat.mtimes sys.A).plus (Zonotope.ofPoint u)).plus W).construct := by
    rw [← Zonotope.plus_exact, ← Zonotope.plus_exact, ← Zonotope.mtimes_exact]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, w, hw, rfl⟩
    exact ⟨_, ⟨_, ⟨x, hS hx, rfl⟩, u, Zonotope.mem_ofPoint u, rfl⟩, w, hw, rfl⟩
  intro x hx
  unfold LinearSysDT.observeStep
  split
  · exact Zonotope.intersectStripSeq_outer _ _ _ _ _ ⟨hpred hx.1, hx.2⟩
  · exact Zonotope.intersectStrip_outer _ _ _ _ _ ⟨hpred hx.1, hx.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
