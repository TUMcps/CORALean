import CORALean.ContDynamics.LinearARX.Operations.Btilde
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

/-!
# Alg. 1, its loop state

[1, Alg. 1] after `m` passes of its loop: the time step `k`, the set `S`, and the stored
`B̃ᵢ`. Lines 3–4 compute `B̃₀` by (9b) and the rest by (16), which gives the same matrices
(`Btilde_succ_index`), so both read `Btilde`. Lines 10–11 refresh `B̃_p … B̃_{2p-1}` only
while `k < 3p`, and the stored values are kept otherwise, as the listing has it.

Over plain sets, `⊕` the pointwise sum: the algorithm as exact set arithmetic, which is
what [1, Thm. 2] is about; any representation closed under the two operations runs it.

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.alg1State (sys : LinearARX 𝕋 dy du p) (yinit : Vec ℝ (p * dy))
    (U : ℕ → Set (Vec ℝ du)) (kinit : ℕ) :
    ℕ → ℕ × Set (Vec ℝ (p * dy)) × (ℕ → Mat ℝ (p * dy) du)
  | 0 =>
    -- lines 1–5
    let k := kinit
    let kplus := kinit + p - 1
    let Atilde := sys.Aext ^ k
    let Btilde : ℕ → Mat ℝ (p * dy) du := fun i => sys.Btilde k i
    let S := {Atilde *ᵥ yinit} + ∑ i ∈ Finset.Icc p kplus, (Btilde i *ᵥ ·) '' U (kplus - i)
    (k, S, Btilde)
  | m + 1 =>
    -- line 8, lines 9–12, then line 13
    let prev := sys.alg1State yinit U kinit m
    let k := prev.1 + p
    let kplus := k + p - 1
    let Btilde : ℕ → Mat ℝ (p * dy) du :=
      if k < 3 * p then fun i => if p ≤ i ∧ i ≤ 2 * p - 1 then sys.Btilde k i else prev.2.2 i
      else prev.2.2
    let S := (sys.Aext ^ p *ᵥ ·) '' prev.2.1
      + ∑ i ∈ Finset.Icc p (2 * p - 1), (Btilde i *ᵥ ·) '' U (kplus - i)
    (k, S, Btilde)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
