module

public import CORALean.ContSet.Zonotope.Real.Operations.LuenbergerGain
public import CORALean.ContSet.Zonotope.Real.Operations.LuenbergerUpdate
public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionUpdate
public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionPropStep
public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionPropLuenberger

@[expose] public section

/-!
# `Zonotope.diffusionProp`

[1, Alg. 2], the distributed set-propagation diffusion observer: every node starts at `Z₀`, and at
each instant `k = 1, 2, …` the nodes run Steps 1-2 (`diffusionPropStep`) with the noise `Q_k`,
the radii `r_k` and the outputs `ȳ_k` of that instant. The value at `k` is `Ẑ_{v,k}`, and at `0` it
is `Z₀`; the instant-`k` data are the arguments at `k`, those at `0` unused.

## Inputs
* `F` – dynamics matrix
* `Q` – process-noise generators per instant
* `Γ` – stacked measurement matrices
* `r` – noise radii per instant
* `yb` – outputs per instant
* `nb` – neighbour indices of each node
* `o` – reduction order
* `Z₀` – initial zonotope

## Output
* zonotope of each node at each instant

## References

* [1] [A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      2023.](../../../../../../references/2023/alanwar-jfi-diffusion-observers.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nq N : ℕ} {p m : Fin N → ℕ}


section
variable {n nq N : ℕ} {p : Fin N → ℕ}


end


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.diffusionProp (F : Mat ℝ n n) (Q : ℕ → Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ℕ → ∀ i, Vec ℝ (p i)) (nb : ∀ i, Fin (m i) → Fin N) (o : ℕ)
    (Z₀ : Zonotope (Vec ℝ n)) : ℕ → Fin N → Zonotope (Vec ℝ n)
  | 0 => fun _ => Z₀
  | k + 1 => Zonotope.diffusionPropStep F (Q (k + 1)) Γ (r (k + 1)) (yb (k + 1)) nb o
      (Zonotope.diffusionProp F Q Γ r yb nb o Z₀ k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
