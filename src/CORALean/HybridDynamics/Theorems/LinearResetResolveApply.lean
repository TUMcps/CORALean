module

public import CORALean.HybridDynamics.Operations.LinearResetResolve
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `LinearReset.resolve` applies to the closed-loop input

The reset `LinearReset.resolve` returns, at the state `x` and the global input `u`, is the
original reset `A x + B w + c` at the input `w` of all components in which every bound input is
the output `C_c x_c + D_c w_c + q_c` of the component it is bound to and every global one is its
entry of `u`: exact. Hypotheses are what CORA's own checks and the synchronization guarantee:
`stateBinds{i}` is injective, `B` has only the rows of component `i` in the columns of `i` (the
reset is a synchronization of component resets) and `D(l,:)` points only at global inputs
(otherwise `resolve` throws).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {N g k : ℕ} {n m p : Fin k → ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Dotting a scattered vector with `x` reads `x` at the coordinates. -/
theorem aux_scatter_dot {n : ℕ} (σ : Fin n → Fin N) (v : Fin n → ℝ) (x : Fin N → ℝ) :
    ∑ b, scatter σ v b * x b = ∑ r, v r * x (σ r) := by
  simp only [scatter, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [ite_mul]

/-- Scattering the entries of a vector read at the coordinates gives the vector back, if it
vanishes off the coordinates. -/
theorem aux_scatter_apply {n : ℕ} (σ : Fin n → Fin N) (hσ : Function.Injective σ) (f : Fin N → ℝ)
    (hf : ∀ a, f a ≠ 0 → ∃ r, σ r = a) (a : Fin N) :
    scatter σ (fun r => f (σ r)) a = f a := by -- --- PROOF ---
  unfold scatter
  by_cases h : ∃ r, σ r = a
  · obtain ⟨r0, rfl⟩ := h
    rw [Finset.sum_eq_single r0]
    · simp
    · intro r _ hr; simp [hσ.ne hr]
    · simp
  · have h : ∀ r, σ r ≠ a := fun r hr => h ⟨r, hr⟩
    have : f a = 0 := by by_contra h'; obtain ⟨r, hr⟩ := hf a h'; exact h r hr
    simp [this, h]

/-- A matrix summing the columns bound to global input `u'`, applied to `u`. -/
theorem aux_resolveGlobal_mulVec (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g)
    (X : Fin N → (Σ i, Fin (m i)) → ℝ) (u : Vec ℝ g) (a : Fin N) : -- --- STMT ---
    ((Matrix.of fun a u' => ∑ ij : (Σ i, Fin (m i)),
        if inputBinds ij.1 ij.2 = .global u' then X a ij else 0) *ᵥ u) a =
      ∑ ij : (Σ i, Fin (m i)), match inputBinds ij.1 ij.2 with
        | .global u'' => X a ij * u u''
        | .output _ _ => 0 := by -- --- PROOF ---
  simp only [mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rcases h : inputBinds ij.1 ij.2 with a' | ⟨c₂, l₂⟩
  · simp
  · simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearReset.resolve_apply (A : Mat ℝ N N) (B : Mat ℝ N (∑ i, m i)) (c : Vec ℝ N)
    (C : ∀ i, Mat ℝ (p i) (n i)) (D : ∀ i, Mat ℝ (p i) (m i)) (q : ∀ i, Vec ℝ (p i))
    (stateBinds : ∀ i, Fin (n i) → Fin N) (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g)
    (hinj : ∀ i, Function.Injective (stateBinds i))
    (hblock : ∀ i j a, B a (finSigmaFinEquiv ⟨i, j⟩) ≠ 0 → ∃ r, stateBinds i r = a)
    (hD : ∀ i l j, D i l j ≠ 0 → ∃ a, inputBinds i j = .global a)
    (x : Vec ℝ N) (u : Vec ℝ g) (w : Vec ℝ (∑ i, m i))
    (hg : ∀ i j a, inputBinds i j = .global a → w (finSigmaFinEquiv ⟨i, j⟩) = u a)
    (ho : ∀ i j c' l, inputBinds i j = .output c' l →
      w (finSigmaFinEquiv ⟨i, j⟩) = (C c' *ᵥ (fun s => x (stateBinds c' s)) +
        D c' *ᵥ (fun jj => w (finSigmaFinEquiv ⟨c', jj⟩)) + q c') l) (a : Fin N) : -- --- STMT ---
    ((LinearReset.resolve A B c C D q stateBinds inputBinds).1 *ᵥ x +
      (LinearReset.resolve A B c C D q stateBinds inputBinds).2.1 *ᵥ u +
      (LinearReset.resolve A B c C D q stateBinds inputBinds).2.2) a =
      (A *ᵥ x + B *ᵥ w + c) a := by -- --- PROOF ---
  -- the scattered columns of `B` are the columns of `B`
  have hscat : ∀ i j,
      (scatter (stateBinds i) fun r => B (stateBinds i r) (finSigmaFinEquiv ⟨i, j⟩)) =
        fun a => B a (finSigmaFinEquiv ⟨i, j⟩) := fun i j =>
    funext fun a => aux_scatter_apply (stateBinds i) (hinj i)
      (fun a => B a (finSigmaFinEquiv ⟨i, j⟩)) (hblock i j) a
  -- the sums over the columns of `u` are sums over the inputs of the components
  have hsumS : ∀ f : Fin (∑ i, m i) → ℝ,
      ∑ col, f col = ∑ ij : (Σ i, Fin (m i)), f (finSigmaFinEquiv ij) :=
    fun f => (Equiv.sum_comp finSigmaFinEquiv f).symm
  -- the `D` columns of a bound input pick the global inputs: the key identity
  have hK : ∀ (c'' : Fin k) (l'' : Fin (p c'')),
      ∑ ij : (Σ i, Fin (m i)), (match inputBinds ij.1 ij.2 with
        | .global u' => (∑ jj, if finSigmaFinEquiv ij = finSigmaFinEquiv ⟨c'', jj⟩ then
            D c'' l'' jj else 0) * u u'
        | .output _ _ => 0) = (D c'' *ᵥ fun jj => w (finSigmaFinEquiv ⟨c'', jj⟩)) l'' := by
    intro c'' l''
    simp only [mulVec, dotProduct, Equiv.apply_eq_iff_eq]
    -- each term is the `D` entry of its own column, if it is one
    have : ∀ ij : (Σ i, Fin (m i)), (match inputBinds ij.1 ij.2 with
        | .global u' => (∑ jj, if ij = ⟨c'', jj⟩ then D c'' l'' jj else 0) * u u'
        | .output _ _ => 0) =
          ∑ jj, if ij = ⟨c'', jj⟩ then D c'' l'' jj * w (finSigmaFinEquiv ij) else 0 := by
      intro ij
      -- a global column holds the global input, an output column has a zero `D` entry
      rcases h : inputBinds ij.1 ij.2 with a' | ⟨c₂, l₂⟩
      · rw [hg _ _ _ h]
        simp [Finset.sum_mul, ite_mul]
      · simp only
        refine (Finset.sum_eq_zero fun jj _ => ?_).symm
        by_cases hij : ij = ⟨c'', jj⟩
        · subst hij
          have : D c'' l'' jj = 0 := by
            by_contra hne
            obtain ⟨a', ha'⟩ := hD c'' l'' jj hne
            rw [h] at ha'; cases ha'
          simp [this]
        · simp [hij]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun jj _ => ?_
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
  -- shorthand for the per-input updates
  set U := LinearReset.resolveUpdate B C D q stateBinds inputBinds with hUdef
  -- the three updates of one input, entry by entry
  have hU1 : ∀ ij : (Σ i, Fin (m i)), ((U ij).1 *ᵥ x) a = match inputBinds ij.1 ij.2 with
      | .global _ => 0
      | .output c' l => B a (finSigmaFinEquiv ij) * (C c' *ᵥ fun s => x (stateBinds c' s)) l := by
    intro ij
    rcases h : inputBinds ij.1 ij.2 with a' | ⟨c₂, l₂⟩
    · simp [hUdef, LinearReset.resolveUpdate, h]
    · simp only [hUdef, LinearReset.resolveUpdate, h]
      rw [vecMulVec_mulVec, hscat ij.1 ij.2]
      simp only [Sigma.eta, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.smul_apply,
        dotProduct]
      rw [aux_scatter_dot]
      simp only [mulVec, dotProduct]
  -- the update of `B`, entry by entry
  have hU2 : ∀ (ij : Σ i, Fin (m i)) (col : Fin (∑ i, m i)), (U ij).2.1 a col =
      match inputBinds ij.1 ij.2 with
      | .global _ => 0
      | .output c' l => B a (finSigmaFinEquiv ij) *
          ∑ jj, if col = finSigmaFinEquiv ⟨c', jj⟩ then D c' l jj else 0 := by
    intro ij col
    rcases h : inputBinds ij.1 ij.2 with a' | ⟨c₂, l₂⟩
    · simp [hUdef, LinearReset.resolveUpdate, h]
    · simp only [hUdef, LinearReset.resolveUpdate, h, hscat ij.1 ij.2, Sigma.eta,
        Matrix.vecMulVec_apply]
  -- the update of `c`, entry by entry
  have hU3 : ∀ ij : (Σ i, Fin (m i)), (U ij).2.2 a = match inputBinds ij.1 ij.2 with
      | .global _ => 0
      | .output c' l => B a (finSigmaFinEquiv ij) * q c' l := by
    intro ij
    rcases h : inputBinds ij.1 ij.2 with a' | ⟨c₂, l₂⟩
    · simp [hUdef, LinearReset.resolveUpdate, h]
    · simp only [hUdef, LinearReset.resolveUpdate, h, hscat ij.1 ij.2, Sigma.eta]
  unfold LinearReset.resolve
  simp only [Pi.add_apply, add_mulVec, Matrix.sum_mulVec, Finset.sum_apply, ← hUdef]
  -- the per-input terms, as opaque functions with their defining equations
  obtain ⟨At, hAt⟩ : ∃ f : (Σ i, Fin (m i)) → ℝ, ∀ ij, f ij = match inputBinds ij.1 ij.2 with
      | .global _ => 0
      | .output c' l => B a (finSigmaFinEquiv ij) * (C c' *ᵥ fun s => x (stateBinds c' s)) l :=
    ⟨_, fun _ => rfl⟩
  -- the global input's own terms, and the terms the `D` updates add to them
  obtain ⟨Gm, hGm⟩ : ∃ f : (Σ i, Fin (m i)) → ℝ, ∀ ij, f ij = match inputBinds ij.1 ij.2 with
      | .global u' => B a (finSigmaFinEquiv ij) * u u'
      | .output _ _ => 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨Gx, hGx⟩ : ∃ f : (Σ i, Fin (m i)) → ℝ, ∀ ij, f ij = match inputBinds ij.1 ij.2 with
      | .global _ => 0
      | .output c' l =>
          B a (finSigmaFinEquiv ij) * (D c' *ᵥ fun jj => w (finSigmaFinEquiv ⟨c', jj⟩)) l :=
    ⟨_, fun _ => rfl⟩
  -- the `q` terms, and the right side's terms
  obtain ⟨Ct, hCt⟩ : ∃ f : (Σ i, Fin (m i)) → ℝ, ∀ ij, f ij = match inputBinds ij.1 ij.2 with
      | .global _ => 0
      | .output c' l => B a (finSigmaFinEquiv ij) * q c' l := ⟨_, fun _ => rfl⟩
  obtain ⟨Rt, hRt⟩ : ∃ f : (Σ i, Fin (m i)) → ℝ,
      ∀ ij, f ij = B a (finSigmaFinEquiv ij) * w (finSigmaFinEquiv ij) :=
    ⟨_, fun _ => rfl⟩
  have hA : ∑ ij, ((U ij).1 *ᵥ x) a = ∑ ij, At ij := by simp only [hU1, hAt]
  have hc : ∑ ij, (U ij).2.2 a = ∑ ij, Ct ij := by simp only [hU3, hCt]
  simp only [Sigma.eta, aux_resolveGlobal_mulVec, Matrix.add_apply, Matrix.sum_apply, hU2]
  -- the global columns of the updated `B` split into `B` and the `D` updates
  have hsplit : ∀ x : (Σ i, Fin (m i)), (match inputBinds x.1 x.2 with
      | ResolveSource.global u'' => (B a (finSigmaFinEquiv x) + ∑ x_1 : (Σ i, Fin (m i)),
          match inputBinds x_1.1 x_1.2 with
          | ResolveSource.global _ => 0
          | ResolveSource.output c' l => B a (finSigmaFinEquiv x_1) *
              ∑ jj, if finSigmaFinEquiv x = finSigmaFinEquiv ⟨c', jj⟩ then
                D c' l jj else 0) * u u''
      | ResolveSource.output _ _ => 0) = Gm x + ∑ x_1 : (Σ i, Fin (m i)),
        match inputBinds x_1.1 x_1.2 with
        | ResolveSource.global _ => 0
        | ResolveSource.output c' l => B a (finSigmaFinEquiv x_1) * (match inputBinds x.1 x.2 with
          | ResolveSource.global u'' =>
            (∑ jj, if finSigmaFinEquiv x = finSigmaFinEquiv ⟨c', jj⟩ then D c' l jj else 0) * u u''
          | ResolveSource.output _ _ => 0) := by
    intro x
    -- a global input distributes over the sum, an output input contributes nothing
    rw [hGm]
    rcases h : inputBinds x.1 x.2 with a' | ⟨c₂, l₂⟩
    · simp only [add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun x1 _ => ?_
      -- only an output input `x1` adds a `D` term
      rcases inputBinds x1.1 x1.2 with a'' | ⟨c₃, l₃⟩
      · simp
      · simp only [mul_assoc]
        congr 1
        rw [Finset.sum_mul]
    · simp only [zero_add]
      symm
      refine Finset.sum_eq_zero fun x1 _ => ?_
      rcases inputBinds x1.1 x1.2 with a'' | ⟨c₃, l₃⟩ <;> simp
  rw [Finset.sum_congr rfl fun x _ => hsplit x, Finset.sum_add_distrib, Finset.sum_comm]
  -- the `D` updates feed the outputs' `D` terms, by the key identity
  have hGx' : ∀ y : (Σ i, Fin (m i)), ∑ x : (Σ i, Fin (m i)), (match inputBinds y.1 y.2 with
      | ResolveSource.global _ => 0
      | ResolveSource.output c' l => B a (finSigmaFinEquiv y) *
          match inputBinds x.1 x.2 with
          | ResolveSource.global u'' =>
            (∑ jj, if finSigmaFinEquiv x = finSigmaFinEquiv ⟨c', jj⟩ then D c' l jj else 0) * u u''
          | ResolveSource.output _ _ => 0) = Gx y := by
    intro y
    rw [hGx]
    rcases h : inputBinds y.1 y.2 with a' | ⟨c₂, l₂⟩
    · simp
    · simp only [← Finset.mul_sum]
      rw [hK]
  rw [Finset.sum_congr rfl fun y _ => hGx' y]
  -- the right side splits into the same four kinds of terms
  have hR : (B *ᵥ w) a = ∑ ij, Rt ij := by
    simp only [hRt, mulVec, dotProduct]
    exact hsumS fun col => B a col * w col
  have hRt' : ∀ ij, Rt ij = At ij + Gm ij + Gx ij + Ct ij := by
    intro ij
    rw [hRt, hAt, hGm, hGx, hCt]
    rcases h : inputBinds ij.1 ij.2 with a' | ⟨c₂, l₂⟩
    · have := hg ij.1 ij.2 a' h
      rw [Sigma.eta] at this
      simp [this]
    · have := ho ij.1 ij.2 c₂ l₂ h
      rw [Sigma.eta] at this
      simp only [this, Pi.add_apply]
      ring
  rw [hR, Finset.sum_congr rfl fun ij _ => hRt' ij]
  simp only [Finset.sum_add_distrib, hA, hc]
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
