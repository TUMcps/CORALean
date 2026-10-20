module

public import CORALean.NN.Operations.IntervalChainBackprop
public import CORALean.NN.Operations.IntervalChainBackpropFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.NN.Theorems.IntervalChainFwdFloatOuter
public import CORALean.ContSet.Interval.Float.Theorems.MtimesMem

@[expose] public section

/-!
# The float interval backpropagation encloses the real one

For a float chain `c` that stands for the real chain `r` (`IntervalChain.Sound`), an input pair `p`
and an output gradient pair `g` of real vectors inside the boxes `P` and `G`, the pair
`Real.IntervalChain.backprop` returns lies, bound by bound, in the boxes `IntervalChain.backprop`
returns. The forward values the real recursion needs are the ones `IntervalChain.fwd` encloses, so
each layer's rule is enclosed at its own box: the linear layer's `dmu = Wᵀ (gu + gl)/2`, `dr = |W|ᵀ
(gu - gl)/2` by `Interval.mtimes`, the activation's `σ'(l) ⊙ gl` by `Interval.times`. What the real
row proves of the returned value (the adjoint of the tangent propagation) thus holds of a value the
float result encloses.

## Inputs
* `n` – input width
* `k` – output width
* `c` – float interval chain
* `r` – real interval chain

## Hypotheses
* `hc` – the float chain stands for the real chain

## Conclusion
* the real backpropagation lies bound by bound in the float result
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem IntervalChain.backprop_outer {n k : ℕ} {c : IntervalChain 𝕋 n k}
    {r : Real.IntervalChain n k} (hc : c.Sound r) : -- --- CONCL ---
    ∀ (P : Interval (Vec 𝕋 n) × Interval (Vec 𝕋 n)) (p : Vec ℝ n × Vec ℝ n)
      (G : Interval (Vec 𝕋 k) × Interval (Vec 𝕋 k)) (g : Vec ℝ k × Vec ℝ k),
      p.1 ∈ P.1.construct → p.2 ∈ P.2.construct → g.1 ∈ G.1.construct → g.2 ∈ G.2.construct →
      (r.backprop p g).1 ∈ (c.backprop P G).1.construct ∧
        (r.backprop p g).2 ∈ (c.backprop P G).2.construct := by -- --- PROOF ---
  induction hc with
  | nil => intro P p G g _ _ h1 h2; exact ⟨h1, h2⟩
  | @linear n m k W b c r _ ih =>
    intro P p G g h1 h2 hg1 hg2
    -- the box the layer's output interval lives in, as in the forward pass
    have hmu := IntervalChain.linear_mu_mem W b h1 h2
    have hr := IntervalChain.linear_r_mem W h1 h2
    obtain ⟨hl, hu⟩ := ih (Interval.minus (Interval.plus (Interval.mtimes W (Interval.halve
        (Interval.plus P.1 P.2))) ⟨b, b⟩) (Interval.mtimes (W.map absolute)
        (Interval.halve (Interval.minus P.2 P.1))),
      Interval.plus (Interval.plus (Interval.mtimes W (Interval.halve
        (Interval.plus P.1 P.2))) ⟨b, b⟩) (Interval.mtimes (W.map absolute)
        (Interval.halve (Interval.minus P.2 P.1))))
      (toRealMat W *ᵥ ((1 / 2 : ℝ) • (p.1 + p.2)) + toRealVec b
        - (toRealMat W).map abs *ᵥ ((1 / 2 : ℝ) • (p.2 - p.1)),
       toRealMat W *ᵥ ((1 / 2 : ℝ) • (p.1 + p.2)) + toRealVec b
        + (toRealMat W).map abs *ᵥ ((1 / 2 : ℝ) • (p.2 - p.1))) G g
      (Interval.minus_outer _ _ (Set.sub_mem_sub hmu hr))
      (Interval.plus_outer _ _ (Set.add_mem_add hmu hr)) hg1 hg2
    -- then the layer's own transposed rule on the gradient boxes
    have hdmu := Interval.mtimes_mem Wᵀ _ rfl _ (Interval.halve_plus_mem hu hl)
    have hdr := Interval.mtimes_mem (W.map absolute)ᵀ ((toRealMat W).map abs)ᵀ
      (by rw [toRealMat_map_absolute]; rfl) _ (Interval.halve_minus_mem hu hl)
    exact ⟨Interval.minus_outer _ _ (Set.sub_mem_sub hdmu hdr),
      Interval.plus_outer _ _ (Set.add_mem_add hdmu hdr)⟩
  | @act n k σE σ'E σ σ' c r hσ hσ' _ ih =>
    intro P p G g h1 h2 hg1 hg2
    -- the gradient boxes of the rest, at the activation's output boxes
    obtain ⟨hl, hu⟩ := ih
      (⟨fun i => (σE ⟨P.1.inf i, P.1.sup i⟩).inf, fun i => (σE ⟨P.1.inf i, P.1.sup i⟩).sup⟩,
        ⟨fun i => (σE ⟨P.2.inf i, P.2.sup i⟩).inf, fun i => (σE ⟨P.2.inf i, P.2.sup i⟩).sup⟩)
      (fun i => σ (p.1 i), fun i => σ (p.2 i)) G g
      (ScalarEncloses.vec_mem hσ h1) (ScalarEncloses.vec_mem hσ h2) hg1 hg2
    exact ⟨Interval.times_outer _ _ ⟨_, ScalarEncloses.vec_mem hσ' h1, _, hl, rfl⟩,
      Interval.times_outer _ _ ⟨_, ScalarEncloses.vec_mem hσ' h2, _, hu, rfl⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
