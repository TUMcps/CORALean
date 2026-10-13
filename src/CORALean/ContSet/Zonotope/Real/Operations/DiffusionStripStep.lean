import CORALean.ContSet.Zonotope.Real.Operations.DiffusionStripMeasurement
import CORALean.ContSet.Zonotope.Real.Operations.DiffusionTimeUpdate
import CORALean.ContSet.Zonotope.Real.Operations.DiffusionUpdate

/-!
# `Zonotope.diffusionStripStep`

One time instant of [1, Alg. 1], for all nodes: from the predicted zonotopes `Ẑⁱ`, Step 1, the
measurement update at every node (`diffusionStripMeasurement`), Step 2, the diffusion update of
each node over its neighbourhood `N_i` (`diffusionUpdate`, the zonotopes shared by the `m_i`
neighbours `nb i a`, node `i` among them), and Step 3, the time update (`diffusionTimeUpdate`).

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nq N : ℕ} {p m : Fin N → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.diffusionStripStep (F : Mat ℝ n n) (Q : Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ∀ i, Vec ℝ (p i)) (nb : ∀ i, Fin (m i) → Fin N) (o : ℕ)
    (Zh : Fin N → Zonotope (Vec ℝ n)) : Fin N → Zonotope (Vec ℝ n) :=
  let Zb : Fin N → Zonotope (Vec ℝ n) :=                                    -- Step 1, Z̄ⁱ
    Zonotope.diffusionStripMeasurement Γ r yb Zh
  fun i =>
    let Zt : Zonotope (Vec ℝ n) := Zonotope.diffusionUpdate o (fun a => Zb (nb i a))   -- Step 2
    Zonotope.diffusionTimeUpdate F Q Zt                                                -- Step 3

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
