module

public import CORALean.NN.Operations.IntervalChainJvp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The tangent propagation is the derivative of the forward pass

Along any curve `γ` of intervals with derivative `γ'` at `t`, the forward pass has derivative
`jvp (γ t) γ'`. With `backprop_adjoint`, `backprop` is the transposed derivative of the forward
pass: the gradient of any loss that is a function of the output interval, pulled back.
The interval map of a linear layer is linear in `(l, u)` up to the bias, `|W|` being a fixed
matrix, and the activation's is a diagonal map.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the tangent propagation is the derivative of the forward pass along a curve
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem IntervalChain.fwd_hasDerivAt : -- --- CONCL ---
    ∀ {n k : ℕ} (c : IntervalChain n k), c.IsSmooth →
    ∀ (γ : ℝ → (Fin n → ℝ) × (Fin n → ℝ)) (γ' : (Fin n → ℝ) × (Fin n → ℝ)) (t : ℝ),
      HasDerivAt γ γ' t →
      HasDerivAt (fun s => (c.fwd (γ s) : (Fin k → ℝ) × (Fin k → ℝ)))
        (c.jvp (γ t) γ' : (Fin k → ℝ) × (Fin k → ℝ)) t := by -- --- PROOF ---
  intro n k c
  induction c with
  | nil => intro _ γ γ' t h; exact h
  | linear W b rest ih =>
    intro hs γ γ' t h
    -- the matrix product is linear, so its derivative is the product with the derivative
    have hmv : ∀ {a c : ℕ} (M : Mat ℝ a c) {v : ℝ → Fin c → ℝ} {v' : Fin c → ℝ},
        HasDerivAt v v' t → HasDerivAt (fun s => M *ᵥ v s) (M *ᵥ v') t := fun M v v' hv => by
      have := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)).hasFDerivAt.comp_hasDerivAt
        t hv
      exact this
    have h1 : HasDerivAt (fun s => (γ s).1) γ'.1 t :=
      (hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t h
    have h2 : HasDerivAt (fun s => (γ s).2) γ'.2 t :=
      (hasFDerivAt_snd (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t h
    -- the layer's output curve, with its derivative
    have hmu := (hmv W ((h1.add h2).const_smul (1 / 2 : ℝ))).add_const b
    have hr := hmv (W.map abs) ((h2.sub h1).const_smul (1 / 2 : ℝ))
    have hd := (hmu.sub hr).prodMk (hmu.add hr)
    -- and the rest of the chain by induction
    exact ih hs _ _ t hd
  | act σ σ' rest ih =>
    intro hs γ γ' t h
    have h1 : HasDerivAt (fun s => (γ s).1) γ'.1 t :=
      (hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t h
    have h2 : HasDerivAt (fun s => (γ s).2) γ'.2 t :=
      (hasFDerivAt_snd (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t h
    -- an elementwise `σ` has the diagonal derivative
    have hpi : ∀ {a : ℕ} {v : ℝ → Fin a → ℝ} {v' : Fin a → ℝ}, HasDerivAt v v' t →
        HasDerivAt (fun s i => σ (v s i)) (fun i => σ' (v t i) * v' i) t := fun hv => by
      refine hasDerivAt_pi.2 fun i => ?_
      exact (hs.1 _).comp t (hasDerivAt_pi.1 hv i)
    exact ih hs.2 _ _ t ((hpi h1).prodMk (hpi h2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
