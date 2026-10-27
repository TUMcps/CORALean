module

public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachCZ
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.SupportBoundAttained
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeConZonotopeExact

@[expose] public section

/-!
# The difference of a polytope and a zonotope is inside the exact `CZ(P ⊖ Ẑ_W)`

The exact layer's `maxBackReachCZ` offsets each row by the zonotope's support bound, attained
(`Zonotope.supportBound_attained`): a point of `P ⊖ Ẑ_W` meets each row with the support taken
off, because the attaining point of `Ẑ_W` is added into `P`, and an equality row is blind to the
subtrahend.
The lines are those of [1, Alg. 3].

## Inputs
* `ρ` – support oracle for bounded exact polytopes
* `Pr` – exact polytope
* `ZWr` – exact disturbance zonotope

## Hypotheses
* `hPrb` – the inequality rows of the exact polytope bound it
* `hker` – equality rows of the polytope vanish

## Conclusion
* the difference lies in the exact eroded polytope's conversion
## References

* [1] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exact eroded polytope holds every point of the difference, a subtrahend point attaining
each row's support. -/
theorem LinearSys.minkowskiDiff_subset_maxBackReachCZ
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (_ : Bornology.IsBounded P.construct)
      (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (Pr : HPolytope (Vec ℝ n)) (ZWr : Zonotope (Vec ℝ n))
    (hPrb : Bornology.IsBounded Pr.dropEqs.construct)
    (hker : ∀ (i : Fin Pr.me) (y : Vec ℝ n), Pr.Ae i y = 0) : -- --- CONCL ---
    minkowskiDiff Pr.construct ZWr.construct ⊆
      (LinearSys.maxBackReachCZ ρ Pr hPrb ZWr).construct := by -- --- PROOF ---
  intro x hx
  unfold LinearSys.maxBackReachCZ
  rw [Real.HPolytope.conZonotope_exact]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · -- the point attaining the row's support, added into `P`
    obtain ⟨z, hz, hzeq⟩ := ZWr.supportBound_attained (Pr.A i)
    have h := (hx z hz).1 i
    rw [map_add] at h
    show Pr.A i x ≤ Pr.b i - (ZWr.supportBound (Pr.A i)).val
    linarith
  · -- an equality row is blind to the subtrahend
    have h := (hx _ (Real.Zonotope.center_mem_construct ZWr)).2 i
    rw [map_add, hker i ZWr.c] at h
    exact (add_zero _).symm.trans h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
