module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# Lie derivatives of the flow and of its Jacobian

[1, Eq. 8]: the Taylor coefficients of a solution of `ż = f(z)` are the Lie derivatives
`f⁽¹⁾ = f`, `f⁽ⁱ⁺¹⁾ = Df⁽ⁱ⁾ · f`, and those of the Jacobian `J` of the flow, which solves the
variational equation `J̇ = Df(z)J` (10), are the Lie derivatives of `∇_z f(z, J) = Df(z)J` along
the augmented field `F(z, J) = (f(z), Df(z)J)`. [1, Eq. 14] is the first Lie derivative along `F`,
`H⁽²⁾ = DH · F`; [1, Sec. 3.3] shows `∇_z(f⁽ⁱ⁾) = (∇_z f)⁽ⁱ⁾`, which is why (17) may take the Lie
derivatives of `f`. Coordinate-free: `H⁽²⁾` is `DH(z, J)(f(z), Df(z)J)`, and `J` is one column `v`
at a time. `f` is smooth, [1]'s "sufficiently smooth".

## Inputs
* `X` – state space
* `V` – vector field
* `g` – observable

## Output
* the Lie derivative of the observable along the field

## References

* [1] E. Goubault and S. Putot. "Forward Inner-Approximated Reachability of Non-Linear Continuous
      Systems". Proceedings of the 20th International Conference on Hybrid Systems: Computation and
      Control, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ContDiff

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Lie derivative of `g` along the vector field `V`: `Dg · V`. -/
noncomputable def lieDeriv {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (V : X → X)
    (g : X → F) : X → F :=
  fun x => fderiv ℝ g x (V x)

/-- [1, Eq. 8]: `f⁽¹⁾ = f`, `f⁽ⁱ⁺¹⁾ = Df⁽ⁱ⁾ · f`, counted from `0`. -/
noncomputable def lieIter (f : E → E) : ℕ → E → E
  | 0 => f
  | i + 1 => lieDeriv f (lieIter f i)

/-- [1, Eq. 10]: `∇_z g(z, v) = Dg(z) v`, for a column `v` of the Jacobian. -/
noncomputable def jacLift (g : E → E) : E × E → E := fun p => fderiv ℝ g p.1 p.2

/-- [1, Eq. 10]: the augmented field `F(z, v) = (f(z), Df(z) v)`. -/
noncomputable def augField (f : E → E) : E × E → E × E := fun p => (f p.1, fderiv ℝ f p.1 p.2)

/-- [1, Eq. 14]: along a solution of `ż = f(z)`, `v̇ = Df(z) v`, the time derivative of
`H(z, v)` is its Lie derivative along `F`. -/
theorem hasDerivAt_lieDeriv_augField {f : E → E} {H : E × E → F} (hH : Differentiable ℝ H)
    {z v : ℝ → E} {t : ℝ} (hz : HasDerivAt z (f (z t)) t)
    (hv : HasDerivAt v (fderiv ℝ f (z t) (v t)) t) :
    HasDerivAt (fun s => H (z s, v s)) (lieDeriv (augField f) H (z t, v t)) t :=
  (hH _).hasFDerivAt.comp_hasDerivAt t (hz.prodMk hv)

/-- The Lie derivatives of a smooth field are smooth. -/
theorem contDiff_lieIter {f : E → E} (hf : ContDiff ℝ ∞ f) (i : ℕ) : -- --- CONCL ---
    ContDiff ℝ ∞ (lieIter f i) := by -- --- PROOF ---
  induction i with
  | zero => exact hf
  | succ i ih =>
    -- `Dg(·)(f(·))`: a smooth family of linear maps applied to a smooth field
    exact (ih.fderiv_right (m := ∞) (by norm_cast)).clm_apply hf

/-- One Lie derivative commutes with the Jacobian lift: `∇_z(Dg · f) = D(∇_z g) · F`, by the
symmetry of `D²g`. -/
theorem jacLift_lieDeriv {f g : E → E} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) : -- --- CONCL ---
    jacLift (lieDeriv f g) = lieDeriv (augField f) (jacLift g) := by -- --- PROOF ---
  have hDg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := ∞) (by norm_cast)).differentiable (by norm_cast)
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_cast)
  funext ⟨z, v⟩
  show fderiv ℝ (fun y => fderiv ℝ g y (f y)) z v
    = fderiv ℝ (fun p : E × E => fderiv ℝ g p.1 p.2) (z, v) (f z, fderiv ℝ f z v)
  -- the left side: `D²g(z)(v)(f z) + Dg(z)(Df(z) v)`
  rw [fderiv_clm_apply (hDg z) (hfd z)]
  -- the right side: `p ↦ Dg(p.1)(p.2)` differentiated at `(z, v)`
  have hc : DifferentiableAt ℝ (fun p : E × E => fderiv ℝ g p.1) (z, v) :=
    (hDg z).comp (z, v) differentiableAt_fst
  have hfst : fderiv ℝ (fun p : E × E => fderiv ℝ g p.1) (z, v)
      = (fderiv ℝ (fderiv ℝ g) z).comp (ContinuousLinearMap.fst ℝ E E) :=
    ((hDg z).hasFDerivAt.comp (z, v) hasFDerivAt_fst).fderiv
  rw [fderiv_clm_apply hc differentiableAt_snd, fderiv_snd, hfst]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  -- `D²g(z)` is symmetric
  rw [(hg.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)) v (f z), add_comm]

/-- [1, Sec. 3.3]: `∇_z(f⁽ⁱ⁾) = (∇_z f)⁽ⁱ⁾`, the Jacobian of the `i`-th Lie derivative of
`f` is the `i`-th Lie derivative of the Jacobian along the augmented field. -/
theorem jacLift_lieIter {f : E → E} (hf : ContDiff ℝ ∞ f) (i : ℕ) : -- --- CONCL ---
    jacLift (lieIter f i) = (lieDeriv (augField f))^[i] (jacLift f) := by -- --- PROOF ---
  induction i with
  | zero => rfl
  | succ i ih =>
    -- one more Lie derivative on each side, commuted through the lift
    rw [Function.iterate_succ_apply', ← ih]
    exact jacLift_lieDeriv hf (contDiff_lieIter hf i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
