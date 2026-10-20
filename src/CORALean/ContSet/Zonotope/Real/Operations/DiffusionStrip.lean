module

public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionStripStep

@[expose] public section

/-!
# `Zonotope.diffusionStrip`

[1, Alg. 1], the distributed strip-based diffusion observer: every node starts at `Z₀`, and at each
instant `k` the nodes run Steps 1-3 (`diffusionStripStep`) with the noise `Q_k`, the radii `r_k` and
the outputs `ȳ_k` of that instant. The value at `k` is the predicted set the instant-`k`
measurement update starts from, `Ẑ_{s,k-1}` in the notation of [1]; at `0` it is `Z₀`.

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
* predicted zonotope of each node at each instant

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

noncomputable def Zonotope.diffusionStrip (F : Mat ℝ n n) (Q : ℕ → Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ℕ → ∀ i, Vec ℝ (p i)) (nb : ∀ i, Fin (m i) → Fin N) (o : ℕ)
    (Z₀ : Zonotope (Vec ℝ n)) : ℕ → Fin N → Zonotope (Vec ℝ n)
  | 0 => fun _ => Z₀
  | k + 1 => Zonotope.diffusionStripStep F (Q k) Γ (r k) (yb k) nb o
      (Zonotope.diffusionStrip F Q Γ r yb nb o Z₀ k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
