module

public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionStripMeasurement
public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionTimeUpdate
public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionUpdate

@[expose] public section

/-!
# `Zonotope.diffusionStripStep`

One time instant of [1, Alg. 1], for all nodes: from the predicted zonotopes `Ẑⁱ`, Step 1, the
measurement update at every node (`diffusionStripMeasurement`), Step 2, the diffusion update of
each node over its neighbourhood `N_i` (`diffusionUpdate`, the zonotopes shared by the `m_i`
neighbours `nb i a`, node `i` among them), and Step 3, the time update (`diffusionTimeUpdate`).

## Inputs
* `F` – dynamics matrix
* `Q` – process-noise generators
* `Γ` – stacked measurement matrices
* `r` – noise radii
* `yb` – outputs
* `nb` – neighbour indices of each node
* `o` – reduction order
* `Zh` – predicted zonotope of each node

## Output
* predicted zonotope of each node after one instant

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute, 2023.
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
