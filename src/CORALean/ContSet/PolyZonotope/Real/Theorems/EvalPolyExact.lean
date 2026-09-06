import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulPoint

/-!
# `PolyZonotope.evalPoly` is exactly the polynomial, evaluated coordinatewise

`MulPoint`'s idiom carried through the recursion: the claim is about `point`, not
`construct`, so no product of sets appears, only the coordinatewise image of the
admissible factors under `a ↦ evalPolyReal coeffs (point S a)`.

`evalPolyReal` is the same recursion over `ℝ` that `evalPoly` runs over the set,
so the induction matches it step for step — `mul_point` turns the multiplied set
into a product of points, and the centre shift matches `evalPolyReal`'s own step.
It is scalar, so coordinate `i` reads the coefficient list at `i`; that the
polynomials differ between coordinates costs the induction nothing.
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

/-- `evalPolyStep`'s point, generically: a coordinate `a₀ + R ⊙ S`, `R` read at
`S`'s factors through `hR`. -/
theorem PolyZonotope.evalPolyStep_point (R S : PolyZonotope (Vec ℝ n)) (hR : R.p = S.p)
    (a0 : Vec ℝ n) (b : Fin R.p → ℝ) :
    (PolyZonotope.evalPolyStep R S hR a0).point b
      = fun i => a0 i + R.point b i * S.point (fun k => b (Fin.cast hR.symm k)) i := by
  have hpt : (PolyZonotope.evalPolyStep R S hR a0).point b
      = (PolyZonotope.mul R S hR).c + a0
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
theorem PolyZonotope.evalPolyP_point (S : PolyZonotope (Vec ℝ n)) (coeffs : List (Vec ℝ n))
    (a : Fin S.p → ℝ) :
    (S.evalPolyP coeffs).1.point (fun k => a (Fin.cast (S.evalPolyP coeffs).2 k))
      = fun i => PolyZonotope.evalPolyReal (coeffs.map fun v => v i) (S.point a i) := by
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
      = PolyZonotope.evalPolyReal ((a0 :: rest).map fun v => v i) (S.point a i)
    have key : (PolyZonotope.evalPolyStep R S hR a0).point (fun k => a (Fin.cast hR k)) i
        = a0 i + R.point (fun k => a (Fin.cast hR k)) i
            * S.point (fun k => a (Fin.cast hR (Fin.cast hR.symm k))) i :=
      congrFun (PolyZonotope.evalPolyStep_point R S hR a0 (fun k => a (Fin.cast hR k))) i
    have hcancel : (fun k : Fin S.p => a (Fin.cast hR (Fin.cast hR.symm k))) = a := by
      funext k; simp
    rw [key, hcancel, congrFun ih i, List.map_cons, PolyZonotope.evalPolyReal]
    ring

theorem PolyZonotope.evalPoly_exact (S : PolyZonotope (Vec ℝ n)) (coeffs : List (Vec ℝ n))
    (a : Fin S.p → ℝ) :
    (S.evalPoly coeffs).point (fun k => a (Fin.cast (S.evalPoly_p coeffs) k))
      = fun i => PolyZonotope.evalPolyReal (coeffs.map fun v => v i) (S.point a i) :=
  PolyZonotope.evalPolyP_point S coeffs a

end CORALean.Real
