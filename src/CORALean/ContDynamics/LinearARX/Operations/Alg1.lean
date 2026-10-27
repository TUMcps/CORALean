module

public import CORALean.ContDynamics.LinearARX.Operations.Btilde
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import CORALean.Global.StepOf

@[expose] public section

/-!
# Alg. 1: reachability analysis with arbitrary sets

[1, Alg. 1], line 7 of the `m`-th pass: `Ỹ(k:k₊) ← S ⊕ ⊕_{i=0}^{p-1} B̃ᵢ Ũ(k₊ - i)`, the
window of reachable sets at `k = k_init + m p`. The loop bound `k ≤ p + k_h` only says
when to stop, so every pass is defined; `step_alg1State` carries the rest of the listing.

## Inputs
* `sys` – ARX system
* `yinit` – measured first output window
* `U` – input sets per step
* `kinit` – initial step
* `m` – pass index

## Output
* the window of reachable sets of the `m`-th pass

## References

* [1] [L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". 2023 62nd IEEE Conference
      on Decision and Control (CDC), 2023.](../../../../../references/2023/luetzow-cdc-armax.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

@[step_of LinearARX.alg1]
def LinearARX.step_alg1State (sys : LinearARX 𝕋 dy du p) (yinit : Vec ℝ (p * dy))
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
    let prev := sys.step_alg1State yinit U kinit m
    let k := prev.1 + p
    let kplus := k + p - 1
    let Btilde : ℕ → Mat ℝ (p * dy) du :=
      if k < 3 * p then fun i => if p ≤ i ∧ i ≤ 2 * p - 1 then sys.Btilde k i else prev.2.2 i
      else prev.2.2
    let S := (sys.Aext ^ p *ᵥ ·) '' prev.2.1
      + ∑ i ∈ Finset.Icc p (2 * p - 1), (Btilde i *ᵥ ·) '' U (kplus - i)
    (k, S, Btilde)


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.alg1 (sys : LinearARX 𝕋 dy du p) (yinit : Vec ℝ (p * dy))
    (U : ℕ → Set (Vec ℝ du)) (kinit m : ℕ) : Set (Vec ℝ (p * dy)) :=
  let state := sys.step_alg1State yinit U kinit m
  let k := state.1
  let kplus := k + p - 1
  let S := state.2.1
  let Btilde := state.2.2
  S + ∑ i ∈ Finset.range p, (Btilde i *ᵥ ·) '' U (kplus - i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
