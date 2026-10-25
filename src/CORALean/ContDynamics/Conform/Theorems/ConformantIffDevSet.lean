module

public import CORALean.ContDynamics.Conform.Definitions.IsConformant
public import CORALean.ContDynamics.Conform.Theorems.MemReachOutExactIff

@[expose] public section

/-!
# Conformance is one inclusion per step

[1, Eq. 16]: the model is reachset conformant on the test cases exactly when, at every
step, the union over the test cases of the deviations `y_a = y - y_*` lies in the one
deviation set `R_a(k)` — `mem_reachOutExact_iff` once per measurement.

## Inputs
* `M` – test case index type
* `sys` – plant
* `X0` – initial set
* `W` – disturbance set
* `V` – noise set
* `T` – test cases
* `K` – horizon

## Hypotheses
* none

## Conclusion
* conformance holds iff the deviations lie in the deviation set at every step

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 16]: conformance is `⋃ₘ {y_a⁽ᵐ⁾(k)} ⊆ R_a(k)` at every step. -/
theorem Conform.Plant.conformant_iff_devSet {M : Type} (sys : Conform.Plant n p q)
    (X0 W : Set (Vec ℝ n)) (V : Set (Vec ℝ q)) (T : M → Conform.TestCase n p q)
    (K : ℕ) : -- --- CONCL ---
    sys.IsConformant X0 W V T K ↔
      ∀ k ≤ K, (⋃ m, {(T m).y k - sys.nominal (T m).x0 (T m).u k}) ⊆
        sys.devSet X0 W V k := by -- --- PROOF ---
  simp only [Conform.Plant.IsConformant, Set.iUnion_subset_iff, Set.singleton_subset_iff]
  exact ⟨fun h k hk m => (sys.mem_reachOutExact_iff _ _ _ _ _ _ _).mp (h m k hk),
    fun h m k hk => (sys.mem_reachOutExact_iff _ _ _ _ _ _ _).mpr (h k hk m)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
