import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly
import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulExact

/-!
# `PolyZonotope.evalPoly` is exactly the polynomial, evaluated coordinatewise

`MulExact`'s idiom carried through the recursion: the claim is about `point`, not
`construct`, so no product of sets appears, only the coordinatewise image of the
admissible factors under `a ↦ evalPolyReal coeffs (point S a)`.

`evalPolyReal` is the same recursion over `ℝ` that `evalPoly` runs over the set,
so the induction matches it step for step — `mul_point` turns the multiplied set
into a product of points, and the centre shift matches `evalPolyReal`'s own step.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open PolyZonotope

variable {n : ℕ}

/-- The reference evaluator: Horner's rule over `ℝ`, coefficients lowest degree
first, exactly `evalPoly`'s own recursion carried to a single coordinate. -/
def PolyZonotope.evalPolyReal (coeffs : List ℝ) (x : ℝ) : ℝ :=
  match coeffs with
  | [] => 0
  | a :: rest => a + x * PolyZonotope.evalPolyReal rest x

/-- The result's monomial at a pair of columns, restated here since `MulExact`'s
own copy stays local to that file: the two sets' monomials, multiplied. -/
theorem PolyZonotope.aux_evalPoly_monomial_mulE (S₁ S₂ : PolyZonotope (Vec ℝ n))
    (hp : S₁.p = S₂.p) (a : Fin S₁.p → ℝ) (l₁ : Fin (S₁.h + 1)) (l₂ : Fin (S₂.h + 1)) :
    monomial (mulE S₁ S₂ hp) a (finProdFinEquiv (l₁, l₂))
      = extM S₁ a l₁ * extM S₂ (fun k => a (Fin.cast hp.symm k)) l₂ := by
  have hcast : ∏ k : Fin S₁.p, a k ^ PolyZonotope.extE S₂ (Fin.cast hp k) l₂
      = ∏ k, a (Fin.cast hp.symm k) ^ PolyZonotope.extE S₂ k l₂ :=
    Fintype.prod_equiv (finCongr hp) _ _ fun _ => rfl
  show ∏ k, a k ^ PolyZonotope.mulE S₁ S₂ hp k (finProdFinEquiv (l₁, l₂))
      = (∏ k, a k ^ PolyZonotope.extE S₁ k l₁)
        * ∏ k, a (Fin.cast hp.symm k) ^ PolyZonotope.extE S₂ k l₂
  rw [← hcast, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [PolyZonotope.mulE, Equiv.symm_apply_apply]
  exact pow_add (a k) _ _

/-- The product of the two points, expanded over pairs of extended columns —
restated here since `MulExact`'s own copy stays local to that file. -/
theorem PolyZonotope.aux_evalPoly_mul_point (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p)
    (a : Fin S₁.p → ℝ) :
    S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k))
      = ∑ l, monomial (mulE S₁ S₂ hp) a l • mulG S₁ S₂ l := by
  -- both sides as a double sum over pairs of extended columns, then matched
  funext i
  have h₁ : S₁.point a = ∑ l, extM S₁ a l • extG S₁ l := (PolyZonotope.sum_ext_eq_point S₁ a).symm
  have h₂ : S₂.point (fun k => a (Fin.cast hp.symm k))
      = ∑ l, extM S₂ (fun k => a (Fin.cast hp.symm k)) l • extG S₂ l :=
    (PolyZonotope.sum_ext_eq_point S₂ _).symm
  have hL : (S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k))) i
      = ∑ l₁, ∑ l₂, (extM S₁ a l₁ * extM S₂ (fun k => a (Fin.cast hp.symm k)) l₂)
          * (extG S₁ l₁ i * extG S₂ l₂ i) := by
    show (S₁.point a) i * (S₂.point (fun k => a (Fin.cast hp.symm k))) i = _
    rw [h₁, h₂, Finset.sum_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun l₁ _ => Finset.sum_congr rfl fun l₂ _ => by ring
  have hpair : ∑ pr : Fin (S₁.h + 1) × Fin (S₂.h + 1),
        (monomial (mulE S₁ S₂ hp) a (finProdFinEquiv pr) • mulG S₁ S₂ (finProdFinEquiv pr)) i
      = ∑ l, (monomial (mulE S₁ S₂ hp) a l • mulG S₁ S₂ l) i :=
    Fintype.sum_equiv finProdFinEquiv _ _ fun _ => rfl
  -- the right side, `finProdFinEquiv` matching the pair index to the flat one
  have hR : (∑ l, monomial (mulE S₁ S₂ hp) a l • mulG S₁ S₂ l) i
      = ∑ l₁, ∑ l₂, (extM S₁ a l₁ * extM S₂ (fun k => a (Fin.cast hp.symm k)) l₂)
          * (extG S₁ l₁ i * extG S₂ l₂ i) := by
    rw [Finset.sum_apply, ← hpair, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l₁ _ => Finset.sum_congr rfl fun l₂ _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, PolyZonotope.aux_evalPoly_monomial_mulE S₁ S₂ hp a l₁ l₂]
    refine congrArg _ ?_
    show PolyZonotope.extG S₁ (finProdFinEquiv.symm (finProdFinEquiv (l₁, l₂))).1 i
        * PolyZonotope.extG S₂ (finProdFinEquiv.symm (finProdFinEquiv (l₁, l₂))).2 i
      = extG S₁ l₁ i * extG S₂ l₂ i
    rw [Equiv.symm_apply_apply]
  rw [hL, hR]

/-- `mul`'s point, read off `mul_exact`'s expansion rather than `construct`: a
product of the two points, `S₂` read at `S₁`'s factors through `Fin.cast`. -/
theorem PolyZonotope.mul_point (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p)
    (a : Fin S₁.p → ℝ) :
    (S₁.mul S₂ hp).point a = S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k)) := by
  show (0 : Vec ℝ n) + ∑ l, PolyZonotope.monomial (mulE S₁ S₂ hp) a l • mulG S₁ S₂ l
      = S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k))
  rw [zero_add, PolyZonotope.aux_evalPoly_mul_point S₁ S₂ hp a]

/-- `evalPolyStep`'s point, generically: a coordinate `a₀ + R ⊙ S`, `R` read at
`S`'s factors through `hR`. -/
theorem PolyZonotope.evalPolyStep_point (R S : PolyZonotope (Vec ℝ n)) (hR : R.p = S.p) (a0 : ℝ)
    (b : Fin R.p → ℝ) :
    (PolyZonotope.evalPolyStep R S hR a0).point b
      = fun i => a0 + R.point b i * S.point (fun k => b (Fin.cast hR.symm k)) i := by
  have hpt : (PolyZonotope.evalPolyStep R S hR a0).point b
      = (PolyZonotope.mul R S hR).c + (fun _ => a0)
        + ∑ l, PolyZonotope.monomial (PolyZonotope.mul R S hR).E b l
            • (PolyZonotope.mul R S hR).G l := rfl
  have hmul : (PolyZonotope.mul R S hR).c
        + ∑ l, PolyZonotope.monomial (PolyZonotope.mul R S hR).E b l
            • (PolyZonotope.mul R S hR).G l
      = (PolyZonotope.mul R S hR).point b := rfl
  rw [hpt, add_right_comm, hmul, PolyZonotope.mul_point R S hR b]
  funext i
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

/-- `evalPolyP`'s point, at the factor vector its own `p`-proof casts back to
`S`'s. Proved by induction, `evalPolyStep_point` carrying the Horner step and
the inductive hypothesis matching `evalPolyReal`'s own recursion. -/
theorem PolyZonotope.evalPolyP_point (S : PolyZonotope (Vec ℝ n)) (coeffs : List ℝ)
    (a : Fin S.p → ℝ) :
    (S.evalPolyP coeffs).1.point (fun k => a (Fin.cast (S.evalPolyP coeffs).2 k))
      = fun i => PolyZonotope.evalPolyReal coeffs (S.point a i) := by
  -- both the empty and the cons case match `evalPolyP`'s own two-case recursion
  induction coeffs with
  | nil =>
    funext i
    simp [PolyZonotope.evalPolyP, PolyZonotope.point, PolyZonotope.evalPolyReal]
  | cons a0 rest ih =>
    -- `R` is the accumulator one level down, `hR` its shared factor count
    set R := (S.evalPolyP rest).1 with hRdef
    set hR := (S.evalPolyP rest).2 with hRdef2
    funext i
    show (PolyZonotope.evalPolyStep R S hR a0).point (fun k => a (Fin.cast hR k)) i
      = PolyZonotope.evalPolyReal (a0 :: rest) (S.point a i)
    have key : (PolyZonotope.evalPolyStep R S hR a0).point (fun k => a (Fin.cast hR k)) i
        = a0 + R.point (fun k => a (Fin.cast hR k)) i
            * S.point (fun k => a (Fin.cast hR (Fin.cast hR.symm k))) i :=
      congrFun (PolyZonotope.evalPolyStep_point R S hR a0 (fun k => a (Fin.cast hR k))) i
    have hcancel : (fun k : Fin S.p => a (Fin.cast hR (Fin.cast hR.symm k))) = a := by
      funext k; simp
    rw [key, hcancel, congrFun ih i, PolyZonotope.evalPolyReal]
    ring

theorem PolyZonotope.evalPoly_exact (S : PolyZonotope (Vec ℝ n)) (coeffs : List ℝ)
    (a : Fin S.p → ℝ) :
    (S.evalPoly coeffs).point (fun k => a (Fin.cast (S.evalPoly_p coeffs) k))
      = fun i => PolyZonotope.evalPolyReal coeffs (S.point a i) :=
  PolyZonotope.evalPolyP_point S coeffs a

end CORALean.Real
