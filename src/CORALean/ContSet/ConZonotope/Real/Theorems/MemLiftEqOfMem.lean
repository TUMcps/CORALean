module

public import CORALean.ContSet.ConZonotope.Real.Operations.LiftEq
public import CORALean.ContSet.ConZonotope.Real.Theorems.MemConstruct

@[expose] public section

/-!
# A point of `cZ` lifts to a point of `liftEq`

[1, Prop. 3] in the direction `reduceLift` needs: `x ∈ cZ` gives `[x; 0] ∈ Z⁺`, the same
coefficients with the equality rows read as the lower coordinates. Each lower coordinate is
`-bₑ i + Σⱼ Aₑ i e_j βⱼ = -bₑ i + Aₑ i β = 0`.

## Inputs
* `cZ` – constrained zonotope
* `x` – point

## Hypotheses
* `hx` – the point lies in the set

## Conclusion
* its padding lies in the lifted set

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mem_liftEq_of_mem (cZ : ConZonotope (Vec ℝ n)) {x : Vec ℝ n}
    (hx : x ∈ cZ.construct) : -- --- CONCL ---
    (Fin.append x (0 : Vec ℝ cZ.P.me) : Vec ℝ (n + cZ.P.me)) ∈
      cZ.liftEq.construct := by -- --- PROOF ---
  obtain ⟨β, hβ, hP, hxi⟩ := ConZonotope.mem_construct_iff.mp hx
  -- a linear functional is the sum of its values at the unit vectors
  have hlin : ∀ f : Vec ℝ cZ.h →ₗ[ℝ] ℝ,
      f β = ∑ j, f (Pi.single j (1 : ℝ) : Vec ℝ cZ.h) * β j := by
    intro f
    conv_lhs => rw [← Finset.univ_sum_single β]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (β j) : Vec ℝ cZ.h) = β j • (Pi.single j (1 : ℝ) : Vec ℝ cZ.h) by
      ext k; by_cases hk : k = j <;> simp [hk], map_smul, smul_eq_mul, mul_comm]
  refine ConZonotope.mem_construct_iff.mpr ⟨β, hβ, ⟨hP.1, fun i => i.elim0⟩, fun k => ?_⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp only [ConZonotope.liftEq, Fin.append_left]
    exact hxi i
  · have h1 := hP.2 i
    rw [hlin] at h1
    simp only [ConZonotope.liftEq, Fin.append_right, Pi.neg_apply, Pi.zero_apply]
    show (0 : ℝ) = -cZ.P.be i + ∑ j : Fin cZ.h, cZ.P.Ae i (Pi.single j (1 : ℝ) : Vec ℝ cZ.h) * β j
    rw [h1]
    exact (neg_add_cancel _).symm
end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
