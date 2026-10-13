import CORALean.ContSet.Zonotope.Real.Operations.DiffusionPropLuenberger
import CORALean.ContSet.Zonotope.Real.Operations.DiffusionUpdate

/-!
# `Zonotope.diffusionPropStep`

One time instant of [1, Alg. 2], for all nodes: from the zonotopes `Ẑⁱ` of the previous instant,
Step 1, the Luenberger update at every node (`diffusionPropLuenberger`), and Step 2, the
diffusion update of each node over its neighbourhood `N_i` (`diffusionUpdate`, as in
[1, Alg. 1]), the zonotopes shared by the `m_i` neighbours `nb i a`, node `i` among them.

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

noncomputable def Zonotope.diffusionPropStep (F : Mat ℝ n n) (Q : Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ∀ i, Vec ℝ (p i)) (nb : ∀ i, Fin (m i) → Fin N) (o : ℕ)
    (Zh : Fin N → Zonotope (Vec ℝ n)) : Fin N → Zonotope (Vec ℝ n) :=
  let Zb : Fin N → Zonotope (Vec ℝ n) :=                                    -- Step 1, Z̄ⁱ
    Zonotope.diffusionPropLuenberger F Q Γ r yb Zh
  fun i =>
    Zonotope.diffusionUpdate o (fun a => Zb (nb i a))                       -- Step 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
