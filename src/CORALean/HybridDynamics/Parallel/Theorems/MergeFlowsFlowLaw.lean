module

public import CORALean.HybridDynamics.Parallel.Operations.MergeFlows
public import CORALean.HybridDynamics.Parallel.Operations.MergeInputSets
public import CORALean.HybridDynamics.Parallel.Operations.MergeDistSets
public import CORALean.HybridDynamics.Parallel.Definitions.FlowLaw
public import CORALean.HybridDynamics.Parallel.Definitions.StateBound
public import CORALean.HybridDynamics.Parallel.Definitions.SelfBindFree
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsLinearSysFlow
public import CORALean.HybridDynamics.Parallel.Theorems.Basic

@[expose] public section

/-!
# `mergeFlows` has the flow law

At state-bound components (`StateBound`) and under `SelfBindFree`, `mergeFlows` with
`mergeInputSets` and `mergeDistSets` has `FlowLaw`, at every scalar with an exact `0` and `1`. The
product's input is the global inputs, zero where nothing reads them, its disturbance the stack.
Row `⟨i, a⟩` of the merged right-hand side is component `i`'s: the block of `A` plus, where state
`a`'s input is bound to output `s` of component `c`, state `s` of `c` (the `1` of `B C`, `C` the
identity), or, where it is bound to global input `a'`, `g a'` (the `1` of `B`); `B u` of the
component reads the same, `B` the identity, `D` and `k` zero. `c` and `E` are copied.

## Inputs
* `P` – parallel automaton
* `lift` – lifting

## Hypotheses
* `hst` – components are state-bound
* `hself` – self-bound inputs meet zero entries

## Conclusion
* the flow assembled without arithmetic has the flow law
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.mergeFlows_flowLaw [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} (hst : P.StateBound) (hself : P.SelfBindFree)
    (lift : ParallelHybridAutomaton.Lifting S G n m) : -- --- CONCL ---
    P.FlowLaw P.mergeFlows (P.mergeInputSets lift) (P.mergeDistSets lift) := by -- --- PROOF ---
  classical
  intro ℓ x u w g hu hin hw
  obtain ⟨hB, hC, hD, hk⟩ := hst ℓ
  -- the product's input: `g`, zero at the global inputs no input reads
  set g' : Vec ℝ m := fun a => if ∃ i j, P.bindsAt ℓ i j = .global a then g a else 0 with hg'
  have hfed : ∀ i j a, P.bindsAt ℓ i j = .global a → g' a = g a := fun i j a h => by
    simp only [hg']
    rw [if_pos ⟨i, j, h⟩]
  refine ⟨g', stack w, lift.mem_input _ _ g' (fun i => ?_) (fun a ha => ?_),
    lift.mem_dist _ w hw, fun i a => ?_⟩
  · obtain ⟨v, hv, hva⟩ := hin i
    exact ⟨v, hv, fun j a h => (hva j a h).trans (hfed i j a h).symm⟩
  · simp only [hg']
    rw [if_neg fun ⟨i, j, h⟩ => ha i j h]
  -- the disturbances: `E` is block diagonal
  have hE : (toRealMat (P.mergeFlows ℓ).E *ᵥ stack w) (finSigmaFinEquiv ⟨i, a⟩) =
      (toRealMat (P.sys ℓ i).E *ᵥ w i) a := by
    show (toRealMat (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv <| Matrix.of fun
      (p : Σ i, Fin (n i)) (q : Σ i, Fin (P.sys ℓ i).r) =>
        if h : p.1 = q.1 then (P.sys ℓ p.1).E p.2 (Fin.cast (by rw [h]) q.2) else (0 : 𝕋)) *ᵥ
          stack w) (finSigmaFinEquiv ⟨i, a⟩) = _
    simp only [Matrix.mulVec, dotProduct, Scalar.toRealMat_apply]
    rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.of_apply, stack_apply]
    -- only component `i`'s block survives
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hc
      exact Finset.sum_eq_zero fun q _ => by simp [dif_neg (Ne.symm hc), ExactScalar.toReal_zero]
    · simp
  -- the constant: `c` copied
  have hc : toRealVec (P.mergeFlows ℓ).c (finSigmaFinEquiv ⟨i, a⟩) = toRealVec (P.sys ℓ i).c a := by
    show toRealVec (fun r => (P.sys ℓ (finSigmaFinEquiv.symm r).1).c (finSigmaFinEquiv.symm r).2)
      (finSigmaFinEquiv ⟨i, a⟩) = _
    simp only [Scalar.toRealVec_apply]
    rw [show finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, a⟩) = ⟨i, a⟩ from
      Equiv.symm_apply_apply _ _]
  -- the component's inputs: `B` the identity, so `B u` at `a` is input `a`, if there is one
  have hBu : (toRealMat (P.sys ℓ i).B *ᵥ u i) a =
      if h : a.val < (P.sys ℓ i).m then u i ⟨a.val, h⟩ else 0 := by
    simp only [Matrix.mulVec, dotProduct, Scalar.toRealMat_apply, hB]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨a.val, h⟩]
      · simp
      · intro j _ hj
        simp [show (a : ℕ) ≠ j from fun h' => hj (Fin.ext h'.symm)]
      · simp
    · exact Finset.sum_eq_zero fun j _ => by
        simp [show (a : ℕ) ≠ j from fun h' => h (h' ▸ j.isLt)]
  -- the merged rows, read at the stack and at `g'`
  set bo : Option (ResolveSource k (fun c => (P.sys ℓ c).q) m) :=
    if h : a.val < (P.sys ℓ i).m then some (P.bindsAt ℓ i ⟨a.val, h⟩) else none with hbo
  have hA : (toRealMat (P.mergeFlows ℓ).A *ᵥ stack x) (finSigmaFinEquiv ⟨i, a⟩) =
      ∑ c, ∑ q : Fin (n c), toReal (match bo with
        | some (.output c₀ s₀) => if c₀ = c ∧ s₀.val = q.val then (1 : 𝕋) else
            (if h : i = c then (P.sys ℓ i).A a (Fin.cast (congrArg n h.symm) q) else 0)
        | _ => if h : i = c then (P.sys ℓ i).A a (Fin.cast (congrArg n h.symm) q) else 0) *
        x c q := by
    simp only [Matrix.mulVec, dotProduct, Scalar.toRealMat_apply]
    rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
    simp only [ParallelHybridAutomaton.mergeFlows, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.of_apply, stack_apply]
    rfl
  -- and `B`'s row: a `1` at the global input state `a`'s input is bound to
  have hBm : (toRealMat (P.mergeFlows ℓ).B *ᵥ g') (finSigmaFinEquiv ⟨i, a⟩) =
      ∑ a', toReal (match bo with
        | some (.global a₀) => if a₀ = a' then (1 : 𝕋) else 0
        | _ => 0) * g' a' := by
    simp only [Matrix.mulVec, dotProduct, Scalar.toRealMat_apply,
      ParallelHybridAutomaton.mergeFlows,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.of_apply,
      Equiv.refl_symm, Equiv.refl_apply]
    rfl
  -- the block of `A`: only component `i` survives
  have hblock : ∑ c, ∑ q : Fin (n c), toReal (if h : i = c then
      (P.sys ℓ i).A a (Fin.cast (congrArg n h.symm) q) else (0 : 𝕋)) * x c q =
      (toRealMat (P.sys ℓ i).A *ᵥ x i) a := by
    rw [Finset.sum_eq_single i]
    · simp [Matrix.mulVec, dotProduct, Scalar.toRealMat_apply]
    · intro c _ hc
      exact Finset.sum_eq_zero fun q _ => by simp [dif_neg (Ne.symm hc), ExactScalar.toReal_zero]
    · simp
  have h01 : ∀ (Q : Prop) [Decidable Q], toReal (if Q then (1 : 𝕋) else 0) = if Q then 1 else 0 :=
    fun Q _ => by split_ifs <;> simp [ExactScalar.toReal_one, ExactScalar.toReal_zero]
  simp only [Pi.add_apply]
  rw [hE, hc, hBu, hA, hBm]
  congr 1
  congr 1
  by_cases h : a.val < (P.sys ℓ i).m
  · rw [show bo = some (P.bindsAt ℓ i ⟨a.val, h⟩) from dif_pos h, dif_pos h, hu i]
    unfold ParallelHybridAutomaton.boundInput
    cases hb : P.bindsAt ℓ i ⟨a.val, h⟩ with
    | global a₀ =>
      -- a global input: `A`'s block, and the `1` of `B` at `a₀`
      simp only [hblock, h01, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, add_right_inj]
      exact hfed i _ a₀ hb
    | output c₀ s₀ =>
      -- an output: `A`'s block plus the `1` of `B C` at state `s₀` of `c₀`, which `C` reads
      have hent : ∀ c (q : Fin (n c)), toReal (if c₀ = c ∧ s₀.val = q.val then (1 : 𝕋) else
          (if h : i = c then (P.sys ℓ i).A a (Fin.cast (congrArg n h.symm) q) else 0)) =
          toReal (if h : i = c then (P.sys ℓ i).A a (Fin.cast (congrArg n h.symm) q)
            else (0 : 𝕋)) + (if c₀ = c ∧ s₀.val = q.val then 1 else 0) := by
        intro c q
        by_cases he : c₀ = c ∧ s₀.val = q.val
        · obtain ⟨rfl, hq⟩ := he
          rw [if_pos ⟨rfl, hq⟩, if_pos ⟨rfl, hq⟩, ExactScalar.toReal_one]
          by_cases hi : i = c₀
          · subst hi
            rw [dif_pos rfl, Fin.cast_eq_self,
              hself ℓ i ⟨a.val, h⟩ s₀ a q hb rfl hq.symm, zero_add]
          · rw [dif_neg hi, ExactScalar.toReal_zero, zero_add]
        · rw [if_neg he, if_neg he, add_zero]
      simp only [hent, add_mul, Finset.sum_add_distrib, hblock, ExactScalar.toReal_zero,
        zero_mul, Finset.sum_const_zero, add_zero, ite_mul, one_mul]
      congr 1
      -- the `1`s pick state `s₀` of `c₀`, which is the output `C x` reads; `D`, `k` add nothing
      rw [Finset.sum_eq_single c₀]
      · simp only [true_and, Pi.add_apply, Matrix.mulVec, dotProduct, Scalar.toRealMat_apply,
          Scalar.toRealVec_apply, hC, hD, hk, zero_mul, Finset.sum_const_zero, add_zero, ite_mul,
          one_mul, zero_mul]
      · intro c _ hc
        exact Finset.sum_eq_zero fun q _ => by simp [Ne.symm hc]
      · simp
  · -- no input drives state `a`: `A`'s block alone
    rw [show bo = none from dif_neg h, dif_neg h]
    simp only [hblock, ExactScalar.toReal_zero, zero_mul, Finset.sum_const_zero, add_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
