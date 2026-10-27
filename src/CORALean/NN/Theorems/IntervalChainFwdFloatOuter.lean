module

public import CORALean.ContSet.Interval.Float.Theorems.MinusOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.NN.Theorems.IntervalChainFloatLinearMuMem
public import CORALean.NN.Theorems.IntervalChainFloatLinearRMem
public import CORALean.NN.Theorems.ScalarEnclosesVecMem
public import CORALean.NN.Definitions.IntervalChainFloatEncloses
public import CORALean.NN.Operations.IntervalChainFwd
public import CORALean.NN.Operations.IntervalChainFwdFloat

@[expose] public section

/-!
# The float forward pass of an interval chain encloses the real one

For a float chain `c` that stands for the real chain `r` (`IntervalChain.Encloses`), and an
input pair of real vectors inside the boxes `P`, the real `Real.IntervalChain.fwd` lies, bound by
bound, in the boxes `IntervalChain.fwd` returns. Layer by layer: the linear layer's
`mu = W (l + u)/2 + b` and `r = |W| (u - l)/2` are enclosed by `Interval.mtimes`, `plus`, `minus`
and the exact `halve`, with `|W|` read as the exact `absolute` of the float entries; the
activation's `[σ l, σ u]` by the stored scalar enclosure.

## Inputs
* `n` – input width
* `k` – output width
* `c` – float interval chain
* `r` – real interval chain

## Hypotheses
* `hc` – the float chain stands for the real chain

## Conclusion
* the real forward pass lies bound by bound in the float result
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

theorem IntervalChain.fwd_outer {n k : ℕ} {c : IntervalChain 𝕋 n k}
    {r : Real.IntervalChain n k} (hc : c.Encloses r) : -- --- CONCL ---
    ∀ (P : Interval (Vec 𝕋 n) × Interval (Vec 𝕋 n)) (p : Vec ℝ n × Vec ℝ n),
      p.1 ∈ P.1.construct → p.2 ∈ P.2.construct →
      (r.fwd p).1 ∈ (c.fwd P).1.construct ∧
        (r.fwd p).2 ∈ (c.fwd P).2.construct := by -- --- PROOF ---
  induction hc with
  | nil => intro P p h1 h2; exact ⟨h1, h2⟩
  | @linear n m k W b c r _ ih =>
    -- the layer's two bounds are the box of `mu - r` and `mu + r`
    intro P p h1 h2
    have hmu := IntervalChain.linear_mu_mem W b h1 h2
    have hr := IntervalChain.linear_r_mem W h1 h2
    exact ih (Interval.minus (Interval.plus (Interval.mtimes W (Interval.halve
        (Interval.plus P.1 P.2))) ⟨b, b⟩) (Interval.mtimes (W.map absolute)
        (Interval.halve (Interval.minus P.2 P.1))),
      Interval.plus (Interval.plus (Interval.mtimes W (Interval.halve
        (Interval.plus P.1 P.2))) ⟨b, b⟩) (Interval.mtimes (W.map absolute)
        (Interval.halve (Interval.minus P.2 P.1))))
      (toRealMat W *ᵥ ((1 / 2 : ℝ) • (p.1 + p.2)) + toRealVec b
        - (toRealMat W).map abs *ᵥ ((1 / 2 : ℝ) • (p.2 - p.1)),
       toRealMat W *ᵥ ((1 / 2 : ℝ) • (p.1 + p.2)) + toRealVec b
        + (toRealMat W).map abs *ᵥ ((1 / 2 : ℝ) • (p.2 - p.1)))
      (Interval.minus_outer _ _ (Set.sub_mem_sub hmu hr))
      (Interval.plus_outer _ _ (Set.add_mem_add hmu hr))
  | act hσ _ _ ih =>
    intro P p h1 h2
    exact ih _ _ (EnclosesScalar.vec_mem hσ h1) (EnclosesScalar.vec_mem hσ h2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
