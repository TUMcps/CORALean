import CORALean.ContDynamics.Conform.Definitions.DevSet
import CORALean.ContDynamics.Conform.Theorems.ImageTemplateZono
import CORALean.ContDynamics.Conform.Theorems.SumTemplateZono
import CORALean.ContDynamics.Conform.Theorems.TemplateZonoAdd

/-!
# The deviation set of stretched templates is a stretched template

With `X̃₀`, `W` and `V` stretched templates, the deviation set at `t_k` is the
zonotope [2, Thm. 1] calls `⟨Γ(t_k) c, G(t_k)⟩`: centre `Λ_k c_X + ∑_{i<k} Λᵢ c_W + c_V`,
generators `[Λ_k G_X, Λ₀ G_W, …, Λ_{k-1} G_W, G_V]` stretched by `α_X`, `α_W` once per step,
and `α_V`, `Λᵢ = C Aⁱ`. An equality: Minkowski sums and linear maps of zonotopes are
exact. [1, Eq. 17] and [1, Eq. 18] are the case `X̃₀ = {0}`, `DevSetZeroTemplateZono`.

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
* [2] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [2, Thm. 1]'s `⟨Γ(t_k) c, G(t_k)⟩`: the deviation set as one stretched template. -/
theorem Conform.Plant.devSet_templateZono (sys : Conform.Plant n p q) {ιX ιW ιV : Type}
    [Fintype ιX] [Fintype ιW] [Fintype ιV] (cX : Vec ℝ n) (GX : ιX → Vec ℝ n) (αX : ιX → ℝ)
    (cW : Vec ℝ n) (GW : ιW → Vec ℝ n) (αW : ιW → ℝ) (cV : Vec ℝ q) (GV : ιV → Vec ℝ q)
    (αV : ιV → ℝ) (k : ℕ) :
    sys.devSet (Conform.templateZono cX GX αX) (Conform.templateZono cW GW αW)
        (Conform.templateZono cV GV αV) k
      = Conform.templateZono
          ((sys.C * sys.A ^ k) *ᵥ cX + ∑ i : Fin k, (sys.C * sys.A ^ (i : ℕ)) *ᵥ cW + cV)
          (Sum.elim (Sum.elim (fun j => (sys.C * sys.A ^ k) *ᵥ GX j)
            (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2)) GV)
          (Sum.elim (Sum.elim αX fun r => αW r.2) αV) := by
  unfold Conform.Plant.devSet
  simp only [Conform.image_templateZono]
  rw [Conform.sum_templateZono, Conform.templateZono_add, Conform.templateZono_add]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
