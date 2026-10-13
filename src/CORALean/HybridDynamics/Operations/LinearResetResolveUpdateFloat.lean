import CORALean.ContSet.Interval.Float.Interval
import CORALean.HybridDynamics.Definitions.ResolveSource
import Mathlib.Algebra.BigOperators.Fin

/-!
# `LinearReset.resolveUpdate` in directed rounding

The three updates `(BC_j, BD_j, Bq_j)` of the loop body of CORA's `linearReset/resolve`
(`LinearReset.resolveUpdate`) at a float scalar, as lower and upper entry bounds. An entry of
`B_part C(l,:)` is the product of two scattered entries, each a sum over the coordinates it was
scattered to; it is written as the sum of the products of the stored entries, each product
rounded down and up (`mulDown`, `mulUp`) and each sum in its own direction (`sumDown`, `sumUp`).
Zero, exactly, for a globally bound input.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {N g k : ℕ} {n m p : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearReset.resolveUpdateFloat (B : Mat 𝕋 N (∑ i, m i))
    (C : ∀ i, Mat 𝕋 (p i) (n i)) (D : ∀ i, Mat 𝕋 (p i) (m i)) (q : ∀ i, Vec 𝕋 (p i))
    (stateBinds : ∀ i, Fin (n i) → Fin N) (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g)
    (ij : Σ i, Fin (m i)) :
    Interval (Mat 𝕋 N N) × Interval (Mat 𝕋 N (∑ i, m i)) × Interval (Vec 𝕋 N) :=
  -- `idxCompInput{i}(j)`: the column of `u` that is input `j` of component `i`
  let idxCompInput : ∀ i, Fin (m i) → Fin (∑ i, m i) := fun i j => finSigmaFinEquiv ⟨i, j⟩
  match inputBinds ij.1 ij.2 with
  | .global _ => (⟨fun _ _ => zero, fun _ _ => zero⟩, ⟨fun _ _ => zero, fun _ _ => zero⟩,
      ⟨fun _ => zero, fun _ => zero⟩)
  | .output c' l =>
    -- `B_part(r) = B(stateBinds{i}(r), idxCompInput{i}(j))`, scattered to `stateBinds{i}(r)`
    let Bpart : Fin (n ij.1) → 𝕋 := fun r => B (stateBinds ij.1 r) (idxCompInput ij.1 ij.2)
    -- `BC_j = B_part * C(l,:)`, added at `A(stateBinds{i}, stateBinds{c})`
    let BCj : Interval (Mat 𝕋 N N) :=
      ⟨fun a b => sumDown fun r => sumDown fun s =>
          if stateBinds ij.1 r = a ∧ stateBinds c' s = b then mulDown (Bpart r) (C c' l s)
          else zero,
       fun a b => sumUp fun r => sumUp fun s =>
          if stateBinds ij.1 r = a ∧ stateBinds c' s = b then mulUp (Bpart r) (C c' l s)
          else zero⟩
    -- `BD_j = B_part * D(l,:)`, added at `B(stateBinds{i}, idxCompInput{c})`
    let BDj : Interval (Mat 𝕋 N (∑ i, m i)) :=
      ⟨fun a col => sumDown fun r => sumDown fun jj =>
          if stateBinds ij.1 r = a ∧ col = idxCompInput c' jj then mulDown (Bpart r) (D c' l jj)
          else zero,
       fun a col => sumUp fun r => sumUp fun jj =>
          if stateBinds ij.1 r = a ∧ col = idxCompInput c' jj then mulUp (Bpart r) (D c' l jj)
          else zero⟩
    -- `Bq_j = B_part * q(l)`, added at `c(stateBinds{i})`
    let Bqj : Interval (Vec 𝕋 N) :=
      ⟨fun a => sumDown fun r => if stateBinds ij.1 r = a then mulDown (Bpart r) (q c' l) else zero,
       fun a => sumUp fun r => if stateBinds ij.1 r = a then mulUp (Bpart r) (q c' l) else zero⟩
    (BCj, BDj, Bqj)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
