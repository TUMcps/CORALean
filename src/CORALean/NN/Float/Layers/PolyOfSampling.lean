import CORALean.NN.Float.Layers.Activation
import CORALean.NN.Float.Layers.PolyEval
import CORALean.NN.Float.Layers.PolyRelaxationOfBracket
import CORALean.NN.Float.Layers.PolySampling

/-!
# The float relaxation a fit and a checked grid buy

`PolyRelaxation.ofSampling` over ℝ, assembled from the float pieces: the grid is
certified rather than computed, the fit is enclosed by `PolyEval`, the
activation by an `Enclosure`, and the recentring pays for its own rounding in
`ofBracket`.

Where the two ends come from is the only new thing. Over ℝ the sampled value is
`σ x - p x`; here neither term is a float operation, so each is bracketed and
the two are subtracted the *crossed* way — the activation's low end against the
fit's high one — which is what keeps the sampled bracket outward.

The fit `c` owes nothing, as over ℝ. It is any array of floats: a least-squares
solve, a Taylor expansion, or a guess. Precision is what it decides, and the
scalar has no linear solve for the layer to prefer one.

`ofSampling` is data and `ofSampling_sound` is what it is worth, which is what
keeps `σ` and its derivative out of the relaxation a layer stores.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ σ' : ℝ → ℝ} {m N : ℕ}

/-- The deviation `σ - p` at one sample, from below: the activation's low end
against the fit's high one. -/
def sampleDevLo (E : Enclosure 𝕋) (c : Fin (m + 1) → 𝕋) (x : 𝕋) : 𝕋 :=
  subDown (E.lo x) (evalPolyUp c x)

/-- And from above, the other crossing. -/
def sampleDevUp (E : Enclosure 𝕋) (c : Fin (m + 1) → 𝕋) (x : 𝕋) : 𝕋 :=
  subUp (E.hi x) (evalPolyDown c x)

theorem sampleDevLo_le {E : Enclosure 𝕋} (hE : E.Sound σ) (c : Fin (m + 1) → 𝕋) (x : 𝕋) :
    toReal (sampleDevLo E c x)
      ≤ σ (toReal x) - Real.evalPoly (fun k => toReal (c k)) (toReal x) := by -- --- PROOF ---
  have h1 := subDown_le_sub (E.lo x) (evalPolyUp c x)
  have h2 := hE.lo_le x
  have h3 := le_evalPolyUp c x
  rw [sampleDevLo]
  linarith

theorem le_sampleDevUp {E : Enclosure 𝕋} (hE : E.Sound σ) (c : Fin (m + 1) → 𝕋) (x : 𝕋) :
    σ (toReal x) - Real.evalPoly (fun k => toReal (c k)) (toReal x)
      ≤ toReal (sampleDevUp E c x) := by -- --- PROOF ---
  have h1 := sub_le_subUp (E.hi x) (evalPolyDown c x)
  have h2 := hE.le_hi x
  have h3 := evalPolyDown_le c x
  rw [sampleDevUp]
  linarith

/-- The bracket a box falls back to when its grid fails its checks: one sample
at the left end, the whole width as the spacing, and no certificate needed. -/
def coarseLo (E : Enclosure 𝕋) (c : Fin (m + 1) → 𝕋) (M l u : 𝕋) : 𝕋 :=
  sampleLo (fun _ : Fin 1 => sampleDevLo E c l) M (subUp u l)

/-- And the same fallback from above. -/
def coarseHi (E : Enclosure 𝕋) (c : Fin (m + 1) → 𝕋) (M l u : 𝕋) : 𝕋 :=
  sampleHi (fun _ : Fin 1 => sampleDevUp E c l) M (subUp u l)

/-- The fallback is sound outright: the left end is in the box and the width
covers it, so neither fact is a check. -/
theorem coarse_bounds {E : Enclosure 𝕋} {c : Fin (m + 1) → 𝕋} {M l u : 𝕋} {t : ℝ}
    (hE : E.Sound σ) (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (hM : ∀ x, toReal l ≤ x → x ≤ toReal u →
      |σ' x - Real.evalPolyDeriv (fun k => toReal (c k)) x| ≤ toReal M)
    (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    toReal (coarseLo E c M l u) ≤ σ t - Real.evalPoly (fun k => toReal (c k)) t
      ∧ σ t - Real.evalPoly (fun k => toReal (c k)) t
        ≤ toReal (coarseHi E c M l u) := by -- --- PROOF ---
  have hg : ∀ x, HasDerivAt (fun y => σ y - Real.evalPoly (fun k => toReal (c k)) y)
      (σ' x - Real.evalPolyDeriv (fun k => toReal (c k)) x) x :=
    fun x => (hd x).sub (Real.hasDerivAt_evalPoly _ x)
  -- the whole width bounds every distance to the left end, rounded up
  have hw := sub_le_subUp u l
  exact sample_bounds_of_cover (g := fun y => σ y - Real.evalPoly (fun k => toReal (c k)) y)
    (t := t) (p := fun _ : Fin 1 => l) hg hM (fun _ => ⟨le_rfl, hl.trans hu⟩)
    (fun y hy hy' => ⟨0, by rw [abs_le]; exact ⟨by linarith, by linarith⟩⟩)
    (fun _ => sampleDevLo_le hE c l) (fun _ => le_sampleDevUp hE c l) hl hu

/-- The sampled bracket of `σ` minus the fit over one box, the checked grid
where it certifies and the fallback where it does not. -/
def fitLo (E : Enclosure 𝕋) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (M dx : 𝕋 → 𝕋 → 𝕋)
    (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) (l u : 𝕋) : 𝕋 :=
  if gridChecked (p l u) l u (dx l u) = true then
    sampleLo (fun i => sampleDevLo E (c l u) (p l u i)) (M l u) (dx l u)
  else coarseLo E (c l u) (M l u) l u

/-- And from above, branching the same way. -/
def fitHi (E : Enclosure 𝕋) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (M dx : 𝕋 → 𝕋 → 𝕋)
    (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) (l u : 𝕋) : 𝕋 :=
  if gridChecked (p l u) l u (dx l u) = true then
    sampleHi (fun i => sampleDevUp E (c l u) (p l u i)) (M l u) (dx l u)
  else coarseHi E (c l u) (M l u) l u


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The relaxation a fit, a derivative bound and a proposed grid buy. All four
arguments are float data: what they are worth is `ofSampling_sound`. -/
def PolyRelaxation.ofSampling (E : Enclosure 𝕋) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋)
    (M dx : 𝕋 → 𝕋 → 𝕋) (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) : PolyRelaxation 𝕋 m :=
  PolyRelaxation.ofBracket c (fitLo E c M dx p) (fitHi E c M dx p)

/-- Only the derivative bound is asked for: a grid that fails its checks costs
precision and not soundness, and the fit owes nothing at all. -/
theorem PolyRelaxation.ofSampling_sound {E : Enclosure 𝕋} {c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋}
    {M dx : 𝕋 → 𝕋 → 𝕋} {p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋} (hE : E.Sound σ)
    (hd : ∀ x, HasDerivAt σ (σ' x) x)
    (hM : ∀ (l u : 𝕋) (x : ℝ), toReal l ≤ x → x ≤ toReal u →
      |σ' x - Real.evalPolyDeriv (fun k => toReal (c l u k)) x| ≤ toReal (M l u)) :
    (PolyRelaxation.ofSampling E c M dx p).Sound σ :=
  PolyRelaxation.ofBracket_sound (c := c) (lo := fitLo E c M dx p)
    (hi := fitHi E c M dx p) fun l u t hl hu => by
      -- the fit is a polynomial, so the deviation differentiates termwise
      have hg : ∀ x, HasDerivAt (fun y => σ y - Real.evalPoly (fun k => toReal (c l u k)) y)
          (σ' x - Real.evalPolyDeriv (fun k => toReal (c l u k)) x) x :=
        fun x => (hd x).sub (Real.hasDerivAt_evalPoly _ x)
      by_cases hchk : gridChecked (p l u) l u (dx l u) = true
      · rw [fitLo, fitHi, if_pos hchk, if_pos hchk]
        exact sample_bounds_of_deriv
          (g := fun y => σ y - Real.evalPoly (fun k => toReal (c l u k)) y)
          (t := t) hg (fun x hx hx' => hM l u x hx hx') hchk
          (fun i => sampleDevLo_le hE (c l u) (p l u i))
          (fun i => le_sampleDevUp hE (c l u) (p l u i)) hl hu
      · rw [fitLo, fitHi, if_neg hchk, if_neg hchk]
        exact coarse_bounds hE hd (fun x hx hx' => hM l u x hx hx') hl hu

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
