module

public import CORALean.NN.Operations.FgsmAttackFloat
public import CORALean.NN.Operations.FgsmAttack
public import CORALean.NN.Theorems.IntervalChainBackpropAtFloatOuter
public import CORALean.NN.Operations.IntervalChainToChain
public import CORALean.NN.Operations.IntervalChainFwd
public import CORALean.NN.Operations.ChainEval
public import CORALean.NN.Theorems.IntervalChainFwdFloatOuter
public import CORALean.ContSet.Interval.Float.Theorems.SignOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The float FGSM attack encloses the real one

For a float interval chain standing for a smooth real one (`IntervalChain.IsSound`) and a float
loss derivative enclosing the real one, the real `Chain.fgsmAttack` of the chain of its layers at a
point `x` of the box `X`, the real value of the float `t` and a step `ε` in its box lies in the box
`IntervalChain.fgsmAttack` returns.
The output of the network lies in the forward box, the loss derivative at the two lies in its
enclosure, the gradient in `IntervalChain.backpropAt`'s box, the sign in `Interval.sign`'s and
the step in the sum of the box products.

## Inputs
* `n` – input width
* `m` – output width
* `c` – float interval chain
* `r` – real interval chain
* `X` – float box of input points
* `x` – real input point
* `t` – float target
* `E` – float box of the step size
* `ε` – real step size
* `lossDerF` – float loss derivative
* `lossDer` – real loss derivative

## Hypotheses
* `hc` – the float chain stands for the real chain
* `hs` – the real chain's activations have the stored derivatives
* `hx` – the input lies in its box
* `hε` – the step lies in its box
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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The interval forward pass at a point is the evaluation: the radius of every linear layer is
zero and an activation applies `σ` to both bounds. -/
private theorem aux_fwd_degenerate : -- --- CONCL ---
    ∀ {n k : ℕ} (c : Real.IntervalChain n k) (x : Vec ℝ n),
    c.fwd (x, x) = (c.toChain.eval x, c.toChain.eval x) := by -- --- PROOF ---
  intro n k c
  induction c with
  | nil => intro x; rfl
  | linear W b rest ih =>
    intro x
    have hx : (1 / 2 : ℝ) • (x + x) = x := by
      rw [← two_smul ℝ x, smul_smul]; norm_num
    simp only [Real.IntervalChain.fwd, Real.IntervalChain.toChain, Chain.eval, hx, sub_self,
      smul_zero, Matrix.mulVec_zero, sub_zero, add_zero]
    exact ih _
  | act σ σ' rest ih =>
    intro x
    simp only [Real.IntervalChain.fwd, Real.IntervalChain.toChain, Chain.eval]
    exact ih _


-- =======================================  MAIN THEOREM  ======================================= --

theorem IntervalChain.fgsmAttack_outer {n m : ℕ} {c : IntervalChain 𝕋 n m}
    {r : Real.IntervalChain n m} (hc : c.IsSound r) (hs : r.IsSmooth) (X : Interval (Vec 𝕋 n))
    {x : Vec ℝ n} (hx : x ∈ X.construct) (t : Vec 𝕋 m) (E : Interval 𝕋) {ε : ℝ}
    (hε : toReal E.inf ≤ ε ∧ ε ≤ toReal E.sup)
    (lossDerF : Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 m))
    {lossDer : Vec ℝ m → Vec ℝ m → Vec ℝ m}
    (hl : ∀ (T Y : Interval (Vec 𝕋 m)) (t' y' : Vec ℝ m), t' ∈ T.construct → y' ∈ Y.construct →
      lossDer t' y' ∈ (lossDerF T Y).construct) : -- --- CONCL ---
    r.toChain.fgsmAttack x (toRealVec t) ε lossDer
      ∈ (c.fgsmAttack X t E lossDerF).construct := by -- --- PROOF ---
  -- the output of the network lies in the forward box
  have hy := (IntervalChain.fwd_outer hc (X, X) (x, x) hx hx).1
  rw [aux_fwd_degenerate] at hy
  -- so does the gradient of the loss in the box of the backpropagation
  have hg := IntervalChain.backpropAt_outer hc hs X hx _
    (hl (Interval.point t) _ (toRealVec t) _ (Interval.mem_point t) hy)
  have hsign := Interval.sign_outer _ ⟨_, hg, rfl⟩
  have hstep : (fun i => ε * Real.sign (r.toChain.backprop x
      (lossDer (toRealVec t) (r.toChain.eval x)) i)) ∈
      (Interval.times (⟨fun _ => E.inf, fun _ => E.sup⟩ : Interval (Vec 𝕋 n))
        (c.backpropAt X (lossDerF (Interval.point t) (c.fwd (X, X)).1)).sign).construct :=
    Interval.times_outer _ _ ⟨fun _ => ε, fun _ => hε, _, hsign, rfl⟩
  exact Interval.plus_outer _ _ (Set.add_mem_add hx hstep)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
