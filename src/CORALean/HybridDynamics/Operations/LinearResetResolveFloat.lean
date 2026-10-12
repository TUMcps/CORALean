import CORALean.HybridDynamics.Operations.LinearResetResolveUpdateFloat

/-!
# `LinearReset.resolve` in directed rounding

CORA's `linearReset/resolve` (`LinearReset.resolve`) at a float scalar. The updates
`A += B_part C(l,:)`, `B += B_part D(l,:)`, `c += B_part q(l)` multiply and add, which is not exact
at a float, so the resolved `A`, `B` and `c` are returned as interval matrices and an interval
vector: the bounds of the updates (`resolveUpdateFloat`) summed in their own directions, and the
columns of one global index summed from the bounds of the updated `B`. Soundness is
`LinearReset.resolveFloat_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {N g k : ℕ} {n m p : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The resolved reset's `(A, B, c)`, each as lower and upper entry bounds. -/
def LinearReset.resolveFloat (A : Mat 𝕋 N N) (B : Mat 𝕋 N (∑ i, m i)) (c : Vec 𝕋 N)
    (C : ∀ i, Mat 𝕋 (p i) (n i)) (D : ∀ i, Mat 𝕋 (p i) (m i)) (q : ∀ i, Vec 𝕋 (p i))
    (stateBinds : ∀ i, Fin (n i) → Fin N) (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g) :
    Interval (Mat 𝕋 N N) × Interval (Mat 𝕋 N g) × Interval (Vec 𝕋 N) :=
  -- `idxCompInput{i}(j)`: the column of `u` that is input `j` of component `i`
  let idxCompInput : ∀ i, Fin (m i) → Fin (∑ i, m i) := fun i j => finSigmaFinEquiv ⟨i, j⟩
  -- the loop over the bound inputs
  let update := LinearReset.resolveUpdateFloat B C D q stateBinds inputBinds
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
