module

public import CORALean.ContDynamics.LinearARX.Operations.Btilde
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

@[expose] public section

/-!
# Alg. 2: efficient reachability analysis

[1, Alg. 2], lines 9–11 of the `m`-th pass: `Ỹ_c ← S_c ⊕ T_c1`, `ỹ_v ← s_v + ∑_{i=0}^{p-1}
B̃ᵢ ũ_v(k₊ - i)`, `Ỹ(k:k₊) ← ỹ_v ⊕ Ỹ_c`. The constant part is only ever added to or moved
by `Ā_ext^p`, which is what keeps its cost linear in the horizon.

## Inputs
* `sys` – ARX system
* `yinit` – measured first output window
* `Uc` – constant input set
* `uv` – varying input
* `kinit` – initial step
* `m` – pass index

## Output
* the window of reachable sets of the `m`-th pass

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def LinearARX.aux_alg2State (sys : LinearARX 𝕋 dy du p) (yinit : Vec ℝ (p * dy))
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
    let prev := sys.aux_alg2State yinit Uc uv kinit m
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


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.alg2 (sys : LinearARX 𝕋 dy du p) (yinit : Vec ℝ (p * dy))
    (Uc : Set (Vec ℝ du)) (uv : ℕ → Vec ℝ du) (kinit m : ℕ) : Set (Vec ℝ (p * dy)) :=
  let state := sys.aux_alg2State yinit Uc uv kinit m
  let k := state.1
  let kplus := k + p - 1
  let Sc := state.2.1
  let Tc1 := state.2.2.1
  let sv := state.2.2.2.2.1
  let Btilde := state.2.2.2.2.2
  let Yc := Sc + Tc1
  let yv := sv + ∑ i ∈ Finset.range p, Btilde i *ᵥ uv (kplus - i)
  {yv} + Yc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
