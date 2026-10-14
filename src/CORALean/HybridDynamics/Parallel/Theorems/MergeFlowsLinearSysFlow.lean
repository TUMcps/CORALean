module

public import CORALean.HybridDynamics.Parallel.Operations.MergeFlowsLinearSys
public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# The merged full equation is the components' equations, bound

For the components' states `xᵢ`, disturbances `wᵢ` and inputs `uᵢ` that obey the bindings — an
input bound to global input `a` is `g a`, one bound to output `s` of component `c` is that
output, `(C_c x_c + D_c u_c + k_c)(s)`, noise-free — the right-hand side of the merged state
equation, `A x + B g + c + E w` at the stacked state, is at every coordinate `⟨i, a⟩` component
`i`'s own right-hand side `Aᵢ xᵢ + Bᵢ uᵢ + cᵢ + Eᵢ wᵢ` at `a`: the identity that makes a stack
of the components' runs a run of `mergeFlowsLinearSys`. Assumed as CORA checks it: an output
that feeds another component has no feedthrough from inputs that are themselves bound to
outputs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {k m : ℕ} {n : Fin k → ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- the coordinate `⟨c, b⟩` of a stack is coordinate `b` of block `c`
theorem aux_stack_apply {d : Fin k → ℕ} (z : ∀ i, Vec ℝ (d i)) (c : Fin k) (b : Fin (d c)) :
    stack z (finSigmaFinEquiv ⟨c, b⟩) = z c b := by
  unfold stack
  rw [Equiv.symm_apply_apply]

-- a matrix over the stacked coordinates, applied to a stack, as a double sum over the blocks
theorem aux_reindex_mulVec_stack {d e : Fin k → ℕ}
    (M : Matrix (Σ i, Fin (d i)) (Σ i, Fin (e i)) ℝ) (z : ∀ i, Vec ℝ (e i))
    (p : Σ i, Fin (d i)) :
    (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv M *ᵥ stack z) (finSigmaFinEquiv p) =
      ∑ c, ∑ b, M p ⟨c, b⟩ * z c b := by
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
  simp only [Equiv.symm_apply_apply, aux_stack_apply]

-- a matrix over the stacked rows, applied to a vector
theorem aux_reindex_mulVec {d : Fin k → ℕ} (M : Matrix (Σ i, Fin (d i)) (Fin m) ℝ)
    (g : Vec ℝ m) (p : Σ i, Fin (d i)) :
    (Matrix.reindex finSigmaFinEquiv (Equiv.refl _) M *ᵥ g) (finSigmaFinEquiv p) =
      ∑ a, M p a * g a := by
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.refl_symm, Equiv.refl_apply]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.mergeFlowsLinearSys_flow (sys : ∀ i, LinearSys ℝ (n i))
    (binds : ∀ i, Fin (sys i).m → OutputSource k (fun i => (sys i).q) m)
    (hD : ∀ i j c s, binds i j = .output c s →
      ∀ j' c' s', binds c j' = .output c' s' → (sys c).D s j' = 0)
    (x : ∀ i, Vec ℝ (n i)) (g : Vec ℝ m) (w : ∀ i, Vec ℝ (sys i).r)
    (u : ∀ i, Vec ℝ (sys i).m)
    (hu : ∀ i j, u i j = match binds i j with
      | .global a => g a
      | .output c s => ((sys c).C *ᵥ x c + (sys c).D *ᵥ u c + (sys c).k) s)
    (i : Fin k) (a : Fin (n i)) :
    ((mergeFlowsLinearSys sys binds).A *ᵥ stack x) (finSigmaFinEquiv ⟨i, a⟩) +
        ((mergeFlowsLinearSys sys binds).B *ᵥ g) (finSigmaFinEquiv ⟨i, a⟩) +
        (mergeFlowsLinearSys sys binds).c (finSigmaFinEquiv ⟨i, a⟩) +
        ((mergeFlowsLinearSys sys binds).E *ᵥ stack w) (finSigmaFinEquiv ⟨i, a⟩) =
      ((sys i).A *ᵥ x i) a + ((sys i).B *ᵥ u i) a + (sys i).c a +
        ((sys i).E *ᵥ w i) a := by -- --- PROOF ---
  classical
  -- the state part: `Aᵢ xᵢ`, and `B(:,j) C_c x_c` for each input bound to an output
  have hA : ((mergeFlowsLinearSys sys binds).A *ᵥ stack x) (finSigmaFinEquiv ⟨i, a⟩) =
      ((sys i).A *ᵥ x i) a + ∑ j, match binds i j with
        | .global _ => 0
        | .output c s => (sys i).B a j * ((sys c).C *ᵥ x c) s := by
    simp only [mergeFlowsLinearSys]
    rw [aux_reindex_mulVec_stack]
    simp only [Matrix.of_apply, add_mul, Finset.sum_add_distrib]
    congr 1
    -- the block-diagonal part: only block `i` survives
    · rw [Finset.sum_eq_single i]
      · simp [Matrix.mulVec, dotProduct]
      · intro c _ hc
        exact Finset.sum_eq_zero fun b _ => by simp [dif_neg (Ne.symm hc)]
      · simp
    -- the bound part: bring the sum over inputs outside, then only block `c₀` survives
    · simp only [Finset.sum_mul]
      refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
      refine Finset.sum_comm.trans ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      cases hb : binds i j with
      | global a' => simp
      | output c₀ s₀ =>
        rw [Finset.sum_eq_single c₀]
        · simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
        · intro c _ hc
          exact Finset.sum_eq_zero fun b _ => by simp [dif_neg hc.symm]
        · simp
  -- the inputs: `B(:,j) g(a)` for a global binding, `B(:,j) D_c(s,:)` through the globals
  have hB : ((mergeFlowsLinearSys sys binds).B *ᵥ g) (finSigmaFinEquiv ⟨i, a⟩) =
      ∑ j, match binds i j with
        | .global a' => (sys i).B a j * g a'
        | .output c s => (sys i).B a j * ∑ j', match binds c j' with
            | .global a' => (sys c).D s j' * g a'
            | .output _ _ => 0 := by
    simp only [mergeFlowsLinearSys]
    refine (aux_reindex_mulVec _ g ⟨i, a⟩).trans ?_
    simp only [Matrix.of_apply, Finset.sum_mul]
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    cases hb : binds i j with
    | global a' => simp
    | output c₀ s₀ =>
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_comm.trans ?_
      refine Finset.sum_congr rfl fun j' _ => ?_
      cases binds c₀ j' with
      | global a'' => simp [mul_assoc]
      | output _ _ => simp
  -- the constant: `cᵢ`, and `B(:,j) k_c(s)`
  have hc : (mergeFlowsLinearSys sys binds).c (finSigmaFinEquiv ⟨i, a⟩) =
      (sys i).c a + ∑ j, match binds i j with
        | .global _ => 0
        | .output c s => (sys i).B a j * (sys c).k s := by
    simp only [mergeFlowsLinearSys]
    rw [Equiv.symm_apply_apply]
    simp only [add_right_inj]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases binds i j <;> simp
  -- the disturbances: `Eᵢ wᵢ`, block diagonal
  have hE : ((mergeFlowsLinearSys sys binds).E *ᵥ stack w) (finSigmaFinEquiv ⟨i, a⟩) =
      ((sys i).E *ᵥ w i) a := by
    simp only [mergeFlowsLinearSys]
    refine (aux_reindex_mulVec_stack _ w ⟨i, a⟩).trans ?_
    simp only [Matrix.of_apply]
    rw [Finset.sum_eq_single i]
    · simp [Matrix.mulVec, dotProduct]
    · intro c _ hc
      exact Finset.sum_eq_zero fun b _ => by simp [dif_neg (Ne.symm hc)]
    · simp
  -- every input term of component `i`, through its binding
  have hBu : ((sys i).B *ᵥ u i) a = ∑ j, match binds i j with
      | .global a' => (sys i).B a j * g a'
      | .output c s => (sys i).B a j * (((sys c).C *ᵥ x c) s + ∑ j', match binds c j' with
            | .global a' => (sys c).D s j' * g a'
            | .output _ _ => 0) + (sys i).B a j * (sys c).k s := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hu i j]
    cases hb : binds i j with
    | global a' => simp
    | output c₀ s₀ =>
      simp only [Pi.add_apply, mul_add]
      congr 2
      congr 1
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j' _ => ?_
      cases hb' : binds c₀ j' with
      | global a'' => rw [hu c₀ j', hb']
      | output c' s' => simp [hD i j c₀ s₀ hb j' c' s' hb']
  -- each input term splits into its state, global-input and constant parts
  have hsplit : ∀ j, (match binds i j with
      | .global a' => (sys i).B a j * g a'
      | .output c s => (sys i).B a j * (((sys c).C *ᵥ x c) s + ∑ j', match binds c j' with
            | .global a' => (sys c).D s j' * g a'
            | .output _ _ => 0) + (sys i).B a j * (sys c).k s) =
      (match binds i j with
        | .global _ => 0
        | .output c s => (sys i).B a j * ((sys c).C *ᵥ x c) s) +
      (match binds i j with
        | .global a' => (sys i).B a j * g a'
        | .output c s => (sys i).B a j * ∑ j', match binds c j' with
            | .global a' => (sys c).D s j' * g a'
            | .output _ _ => 0) +
      (match binds i j with
        | .global _ => 0
        | .output c s => (sys i).B a j * (sys c).k s) := fun j => by
    cases binds i j with
    | global a' => simp
    | output c s => ring
  -- and so does their sum
  have hsum : ∑ j, (match binds i j with
      | .global a' => (sys i).B a j * g a'
      | .output c s => (sys i).B a j * (((sys c).C *ᵥ x c) s + ∑ j', match binds c j' with
            | .global a' => (sys c).D s j' * g a'
            | .output _ _ => 0) + (sys i).B a j * (sys c).k s) =
      (∑ j, (match binds i j with
        | .global _ => 0
        | .output c s => (sys i).B a j * ((sys c).C *ᵥ x c) s)) + (∑ j, (match binds i j with
        | .global a' => (sys i).B a j * g a'
        | .output c s => (sys i).B a j * ∑ j', match binds c j' with
            | .global a' => (sys c).D s j' * g a'
            | .output _ _ => 0)) +
      ∑ j, (match binds i j with
        | .global _ => 0
        | .output c s => (sys i).B a j * (sys c).k s) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hsplit j
  rw [hA, hB, hc, hE, hBu, hsum]
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
