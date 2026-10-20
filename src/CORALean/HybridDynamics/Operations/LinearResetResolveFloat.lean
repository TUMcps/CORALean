module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.HybridDynamics.Definitions.ResolveSource
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `LinearReset.resolve` in directed rounding

CORA's `linearReset/resolve` (`LinearReset.resolve`) at a float scalar. The updates
`A += B_part C(l,:)`, `B += B_part D(l,:)`, `c += B_part q(l)` multiply and add, which is not exact
at a float, so the resolved `A`, `B` and `c` are returned as interval matrices and an interval
vector: the bounds of the updates (`aux_resolveUpdateFloat`) summed in their own directions, and the
columns of one global index summed from the bounds of the updated `B`. Soundness is
`LinearReset.resolveFloat_outer`.

## Inputs
* `A` – state matrix
* `B` – stacked input matrix
* `c` – offset
* `C` – output matrices
* `D` – feedthrough matrices
* `q` – output offsets
* `stateBinds` – state index maps
* `inputBinds` – input bindings

## Output
* resolved interval matrices and offset
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {N g k : ℕ} {n m p : Fin k → ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def LinearReset.aux_resolveUpdateFloat (B : Mat 𝕋 N (∑ i, m i))
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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The resolved reset's `(A, B, c)`, each as lower and upper entry bounds. -/
def LinearReset.resolveFloat (A : Mat 𝕋 N N) (B : Mat 𝕋 N (∑ i, m i)) (c : Vec 𝕋 N)
    (C : ∀ i, Mat 𝕋 (p i) (n i)) (D : ∀ i, Mat 𝕋 (p i) (m i)) (q : ∀ i, Vec 𝕋 (p i))
    (stateBinds : ∀ i, Fin (n i) → Fin N) (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g) :
    Interval (Mat 𝕋 N N) × Interval (Mat 𝕋 N g) × Interval (Vec 𝕋 N) :=
  -- `idxCompInput{i}(j)`: the column of `u` that is input `j` of component `i`
  let idxCompInput : ∀ i, Fin (m i) → Fin (∑ i, m i) := fun i j => finSigmaFinEquiv ⟨i, j⟩
  -- the loop over the bound inputs
  let update := LinearReset.aux_resolveUpdateFloat B C D q stateBinds inputBinds
  let A' : Interval (Mat 𝕋 N N) :=
    ⟨fun a b => addDown (A a b) (sumDown fun i => sumDown fun j => (update ⟨i, j⟩).1.inf a b),
     fun a b => addUp (A a b) (sumUp fun i => sumUp fun j => (update ⟨i, j⟩).1.sup a b)⟩
  let B' : Interval (Mat 𝕋 N (∑ i, m i)) :=
    ⟨fun a col => addDown (B a col)
        (sumDown fun i => sumDown fun j => (update ⟨i, j⟩).2.1.inf a col),
     fun a col => addUp (B a col) (sumUp fun i => sumUp fun j => (update ⟨i, j⟩).2.1.sup a col)⟩
  let c' : Interval (Vec 𝕋 N) :=
    ⟨fun a => addDown (c a) (sumDown fun i => sumDown fun j => (update ⟨i, j⟩).2.2.inf a),
     fun a => addUp (c a) (sumUp fun i => sumUp fun j => (update ⟨i, j⟩).2.2.sup a)⟩
  -- `B(:,i) = sum(B(:,idx),2)` for the columns bound to global input `i`
  let Bglobal : Interval (Mat 𝕋 N g) :=
    ⟨fun a u => sumDown fun i => sumDown fun j =>
        if inputBinds i j = .global u then B'.inf a (idxCompInput i j) else zero,
     fun a u => sumUp fun i => sumUp fun j =>
        if inputBinds i j = .global u then B'.sup a (idxCompInput i j) else zero⟩
  (A', Bglobal, c')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
