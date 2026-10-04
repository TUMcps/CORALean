import CORALean.ContDynamics.LinearARX.Operations.Btilde
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

/-!
# Alg. 2, its loop state

[1, Alg. 2] after `m` passes of its loop, for inputs `Ũ(i) = Ũ_c + ũ_v(i)`: the step `k`,
the sets `S_c`, `T_c1`, `T_c2`, the vector `s_v`, and the stored `B̃ᵢ`. Line 18 assigns
`T_c2` in the first pass only, from the parameters stored at that point — for indices
`k_init … k_init + p - 1`, of which lines 14–15 refresh only those below `2p`. `T_c2` holds
`{0}` before it. As for Alg. 1, (16) and (9b) are both `Btilde`.

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.alg2State (sys : LinearARX 𝕋 dy du p) (yinit : Vec ℝ (p * dy))
    (Uc : Set (Vec ℝ du)) (uv : ℕ → Vec ℝ du) (kinit : ℕ) :
    ℕ → ℕ × Set (Vec ℝ (p * dy)) × Set (Vec ℝ (p * dy)) × Set (Vec ℝ (p * dy))
      × Vec ℝ (p * dy) × (ℕ → Mat ℝ (p * dy) du)
  | 0 =>
    -- lines 1–7
    let k := kinit
    let kplus := kinit + p - 1
    let Atilde := sys.Aext ^ k
    let Btilde : ℕ → Mat ℝ (p * dy) du := fun i => sys.Btilde k i
    let Sc := ∑ i ∈ Finset.range k, (Btilde i *ᵥ ·) '' Uc
    let Tc1 := ∑ i ∈ Finset.Icc k kplus, (Btilde i *ᵥ ·) '' Uc
    let sv := Atilde *ᵥ yinit + ∑ i ∈ Finset.Icc p kplus, Btilde i *ᵥ uv (kplus - i)
    (k, Sc, Tc1, {0}, sv, Btilde)
  | m + 1 =>
    -- line 12, then lines 13–16
    let prev := sys.alg2State yinit Uc uv kinit m
    let k := prev.1 + p
    let kplus := k + p - 1
    let Btilde : ℕ → Mat ℝ (p * dy) du :=
      if k < 3 * p then fun i => if p ≤ i ∧ i ≤ 2 * p - 1 then sys.Btilde k i else prev.2.2.2.2.2 i
      else prev.2.2.2.2.2
    -- lines 17–19, then lines 20–23
    let Tc2 := if k = kinit + p then ∑ i ∈ Finset.Icc (k - p) (kplus - p), (Btilde i *ᵥ ·) '' Uc
      else prev.2.2.2.1
    let Sc := prev.2.1 + Tc2
    let Tc1 := (sys.Aext ^ p *ᵥ ·) '' prev.2.2.1
    let Tc2 := (sys.Aext ^ p *ᵥ ·) '' Tc2
    let sv := sys.Aext ^ p *ᵥ prev.2.2.2.2.1
      + ∑ i ∈ Finset.Icc p (2 * p - 1), Btilde i *ᵥ uv (kplus - i)
    (k, Sc, Tc1, Tc2, sv, Btilde)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
