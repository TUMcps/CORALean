module

public import CORALean.NN.Operations.PgdAttackFloat
public import CORALean.NN.Operations.PgdAttack
public import CORALean.NN.Theorems.FgsmAttackFloatOuter
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# The float PGD attack encloses the real one

For a float interval chain standing for a smooth real one (`IntervalChain.IsSound`) and a float
loss derivative enclosing the real one, the real `Chain.pgdAttack` of the chain of its layers at
the real values of the float arguments lies in the box `IntervalChain.pgdAttack` returns. By
induction on the passes: a pass keeps the real point in the float box and the real step size in
its scalar box, since `IntervalChain.fgsmAttack_outer` encloses the signed gradient step, the
product with the decay lies between the corner products and the clip is monotone in all three of
its arguments, the bounds `x ∓ ε` being rounded outward.

## Inputs
* `c` – float interval chain
* `r` – real interval chain
* `x` – float input point
* `t` – float target
* `ε` – float perturbation radius
* `Q` – number of iterations
* `l` – float lower bounds
* `u` – float upper bounds
* `stepsize` – float initial step size
* `stepsizeDecay` – float decay factor
* `stepsizeDecayIter` – iterations at which the step size decays
* `lossDerF` – float loss derivative
* `lossDer` – real loss derivative

## Hypotheses
* `hc` – the float chain stands for the real chain
* `hs` – the real chain's activations have the stored derivatives
* `hl` – the float loss derivative encloses the real one

## Conclusion
* the real attack lies in the float box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A pass keeps the real point in the float box and the real step size in its box. -/
private theorem aux_pgdStep_mem {c : IntervalChain 𝕋 n m} {r : Real.IntervalChain n m}
    (hc : c.IsSound r) (hs : r.IsSmooth) (t : Vec 𝕋 m) (L U : Interval (Vec 𝕋 n))
    {l u : Vec ℝ n} (hL : l ∈ L.construct) (hU : u ∈ U.construct) (decay : 𝕋)
    (iter : List ℕ) (lossDerF : Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m))
    {lossDer : Vec ℝ m → Vec ℝ m → Vec ℝ m}
    (hl : ∀ (T Y : Interval (Vec 𝕋 m)) (t' y' : Vec ℝ m), t' ∈ T.construct → y' ∈ Y.construct →
      lossDer t' y' ∈ (lossDerF T Y).construct) (q : ℕ) {z : Vec ℝ n} {s : ℝ}
    {Z : Interval (Vec 𝕋 n)} {S : Interval 𝕋} (hz : z ∈ Z.construct)
    (hsS : toReal S.inf ≤ s ∧ s ≤ toReal S.sup) {rs : Vec ℝ n × ℝ}
    (hrs : rs = r.toChain.aux_pgdStep (toRealVec t) l u (toReal decay) iter lossDer q (z, s))
    {fs : Interval (Vec 𝕋 n) × Interval 𝕋}
    (hfs : fs = c.aux_pgdStep t L U decay iter lossDerF q (Z, S)) : -- --- CONCL ---
    rs.1 ∈ fs.1.construct ∧ toReal fs.2.inf ≤ rs.2 ∧ rs.2 ≤ toReal fs.2.sup := by -- --- PROOF ---
  subst hrs hfs
  -- the clipped signed gradient step for any step size in a box `S'`
  have key : ∀ (s' : ℝ) (S' : Interval 𝕋), (toReal S'.inf ≤ s' ∧ s' ≤ toReal S'.sup) →
      (fun i => min (u i) (max (l i) (r.toChain.fgsmAttack z (toRealVec t) s' lossDer i))) ∈
        (⟨fun i => minimum (U.inf i) (maximum (L.inf i) ((c.fgsmAttack Z t S' lossDerF).inf i)),
          fun i => minimum (U.sup i) (maximum (L.sup i) ((c.fgsmAttack Z t S' lossDerF).sup i))⟩ :
          Interval (Vec 𝕋 n)).construct := by
    intro s' S' hs' i
    -- the signed gradient step is in its box, and the bounds are
    have hf : toReal ((c.fgsmAttack Z t S' lossDerF).inf i) ≤
          r.toChain.fgsmAttack z (toRealVec t) s' lossDer i ∧
        r.toChain.fgsmAttack z (toRealVec t) s' lossDer i ≤
          toReal ((c.fgsmAttack Z t S' lossDerF).sup i) :=
      IntervalChain.fgsmAttack_outer hc hs Z hz t S' hs' lossDerF hl i
    have hLi : toReal (L.inf i) ≤ l i ∧ l i ≤ toReal (L.sup i) := hL i
    have hUi : toReal (U.inf i) ≤ u i ∧ u i ≤ toReal (U.sup i) := hU i
    -- the clip is monotone in all three arguments, lower bounds with lower bounds
    constructor
    · show toReal (minimum (U.inf i) (maximum (L.inf i) ((c.fgsmAttack Z t S' lossDerF).inf i)))
        ≤ min (u i) (max (l i) _)
      rw [toReal_minimum, toReal_maximum]
      exact min_le_min hUi.1 (max_le_max hLi.1 hf.1)
    · show min (u i) (max (l i) _) ≤
        toReal (minimum (U.sup i) (maximum (L.sup i) ((c.fgsmAttack Z t S' lossDerF).sup i)))
      rw [toReal_minimum, toReal_maximum]
      exact min_le_min hUi.2 (max_le_max hLi.2 hf.2)
  -- the step size is multiplied by the decay at the listed iterations, else kept
  simp only [Chain.aux_pgdStep, IntervalChain.aux_pgdStep]
  by_cases hq : q ∈ iter
  · have hb := Interval.mul_between_corners hsS.1 hsS.2 (le_refl (toReal decay))
      (le_refl (toReal decay))
    simp only [hq, if_true]
    exact ⟨key _ ⟨_, _⟩ hb, hb⟩
  · simp only [hq, if_false]
    exact ⟨key _ _ hsS, hsS⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem IntervalChain.pgdAttack_outer {c : IntervalChain 𝕋 n m} {r : Real.IntervalChain n m}
    (hc : c.IsSound r) (hs : r.IsSmooth) (x : Vec 𝕋 n) (t : Vec 𝕋 m) (ε : 𝕋) (Q : ℕ)
    (l u : Vec 𝕋 n) (stepsize stepsizeDecay : 𝕋) (stepsizeDecayIter : List ℕ)
    (lossDerF : Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m))
    {lossDer : Vec ℝ m → Vec ℝ m → Vec ℝ m}
    (hl : ∀ (T Y : Interval (Vec 𝕋 m)) (t' y' : Vec ℝ m), t' ∈ T.construct → y' ∈ Y.construct →
      lossDer t' y' ∈ (lossDerF T Y).construct) : -- --- CONCL ---
    r.toChain.pgdAttack (toRealVec x) (toRealVec t) (toReal ε) Q (toRealVec l) (toRealVec u)
        (toReal stepsize) (toReal stepsizeDecay) stepsizeDecayIter lossDer
      ∈ (c.pgdAttack x t ε Q l u stepsize stepsizeDecay stepsizeDecayIter
        lossDerF).construct := by -- --- PROOF ---
  -- the bounds `max(l, x - ε)` and `min(u, x + ε)` lie in their boxes, rounded outward
  set L : Interval (Vec 𝕋 n) :=
    ⟨fun i => maximum (l i) (subDown (x i) ε), fun i => maximum (l i) (subUp (x i) ε)⟩ with hLd
  set U : Interval (Vec 𝕋 n) :=
    ⟨fun i => minimum (u i) (addDown (x i) ε), fun i => minimum (u i) (addUp (x i) ε)⟩ with hUd
  have hL : (fun i => max (toRealVec l i) (toRealVec x i - toReal ε)) ∈ L.construct :=
    fun i => by
    -- the lower bound is rounded down, the upper bound up
    constructor
    · show toReal (maximum (l i) (subDown (x i) ε)) ≤ _
      rw [toReal_maximum]
      exact max_le_max le_rfl (subDown_le_sub _ _)
    · show _ ≤ toReal (maximum (l i) (subUp (x i) ε))
      rw [toReal_maximum]
      exact max_le_max le_rfl (sub_le_subUp _ _)
  have hU : (fun i => min (toRealVec u i) (toRealVec x i + toReal ε)) ∈ U.construct :=
    fun i => by
    -- likewise for `x + ε`
    constructor
    · show toReal (minimum (u i) (addDown (x i) ε)) ≤ _
      rw [toReal_minimum]
      exact min_le_min le_rfl (addDown_le_add _ _)
    · show _ ≤ toReal (minimum (u i) (addUp (x i) ε))
      rw [toReal_minimum]
      exact min_le_min le_rfl (add_le_addUp _ _)
  -- the real state after `q` passes and the float one
  set st : ℕ → Vec ℝ n × ℝ := fun q =>
    Nat.rec (motive := fun _ => Vec ℝ n × ℝ) (toRealVec x, toReal stepsize)
      (fun q zs => r.toChain.aux_pgdStep (toRealVec t)
        (fun i => max (toRealVec l i) (toRealVec x i - toReal ε))
        (fun i => min (toRealVec u i) (toRealVec x i + toReal ε)) (toReal stepsizeDecay)
        stepsizeDecayIter lossDer (q + 1) zs) q with hst
  set F : ℕ → Interval (Vec 𝕋 n) × Interval 𝕋 :=
    c.aux_pgdState x t L U stepsize stepsizeDecay stepsizeDecayIter lossDerF with hF
  -- every pass keeps the real state in the float one
  have hQ : ∀ q : ℕ, (st q).1 ∈ (F q).1.construct ∧
      toReal (F q).2.inf ≤ (st q).2 ∧ (st q).2 ≤ toReal (F q).2.sup := by
    intro q
    induction q with
    | zero => exact ⟨Interval.mem_point x, le_rfl, le_rfl⟩
    | succ q ih =>
      exact aux_pgdStep_mem hc hs t L U hL hU stepsizeDecay stepsizeDecayIter lossDerF hl (q + 1)
        ih.1 ⟨ih.2.1, ih.2.2⟩ rfl rfl
  exact (hQ Q).1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
