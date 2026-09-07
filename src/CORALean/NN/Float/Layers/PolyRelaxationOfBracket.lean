import CORALean.NN.Float.Layers.ActivationPoly

/-!
# A float relaxation out of a bracket, and what recentring costs

`computeApproxError`'s last step [1]: a bracket for `σ - p` over the box, its two
ends averaged into the constant coefficient, and what is left is a radius. Over
ℝ that shift is exact; here it is one `addUp`, and the coefficient that lands is
the one `sound` is then measured against.

That makes the shift the *only* coefficient rounding anything pays for. The
fit's own is free — `PolyRelaxation.sound` quantifies over the floats stored, so
a rounded fit is a different fit and not a wrong one — while the shift is
applied after the bracket was taken, so it moves the polynomial out from under
it. `bracketError` is the payment: how far the stored constant actually moved,
bracketed by a `subDown` and a `subUp`, each end widening the end it can hurt.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {m : ℕ}

/-- The constant coefficient moved by `s`, every other one left alone. -/
def shiftConst (c : Fin (m + 1) → 𝕋) (s : 𝕋) : Fin (m + 1) → 𝕋 :=
  fun i => if i = 0 then addUp (c i) s else c i

/-- Read as reals it is the exact recentring, at whatever the rounded sum
actually moved the constant coefficient by. -/
theorem evalPoly_shiftConst (c : Fin (m + 1) → 𝕋) (s : 𝕋) (t : ℝ) :
    Real.evalPoly (fun k => toReal (shiftConst c s k)) t
      = Real.evalPoly (fun k => toReal (c k)) t
        + (toReal (addUp (c 0) s) - toReal (c 0)) := by -- --- PROOF ---
  have hco : (fun k => toReal (shiftConst c s k))
      = Real.shiftConst (fun k => toReal (c k))
        (toReal (addUp (c 0) s) - toReal (c 0)) := by
    funext k
    -- only the constant slot moves, and there the rounded sum is what landed
    by_cases hk : k = 0
    · subst hk
      show toReal (if (0 : Fin (m + 1)) = 0 then addUp (c 0) s else c 0)
        = toReal (c 0) + (if (0 : Fin (m + 1)) = 0 then
            toReal (addUp (c 0) s) - toReal (c 0) else 0)
      rw [if_pos rfl, if_pos rfl]
      ring
    · show toReal (if k = 0 then addUp (c k) s else c k)
        = toReal (c k) + (if k = 0 then toReal (addUp (c 0) s) - toReal (c 0) else 0)
      rw [if_neg hk, if_neg hk, add_zero]
  rw [hco, Real.evalPoly_shiftConst]

/-- The recentring itself: the bracket's two ends averaged, `half` being exact
and the rounding all in the `addUp`. -/
def bracketShift (lo hi : 𝕋) : 𝕋 := half (addUp lo hi)

/-- The radius the recentred bracket leaves, each end widened by the end of the
shift's own rounding that can hurt it. -/
def bracketError (c0 lo hi : 𝕋) : 𝕋 :=
  maximum (subUp hi (subDown (addUp c0 (bracketShift lo hi)) c0))
    (subUp (subUp (addUp c0 (bracketShift lo hi)) c0) lo)

/-- A value inside the bracket is inside that radius of the shift, which is what
makes the recentred relaxation sound however the shift rounded. -/
theorem abs_sub_le_bracketError {c0 lo hi : 𝕋} {y : ℝ}
    (h1 : toReal lo ≤ y) (h2 : y ≤ toReal hi) :
    |y - (toReal (addUp c0 (bracketShift lo hi)) - toReal c0)|
      ≤ toReal (bracketError c0 lo hi) := by -- --- PROOF ---
  have hlo := subDown_le_sub (addUp c0 (bracketShift lo hi)) c0
  have hhi := sub_le_subUp (addUp c0 (bracketShift lo hi)) c0
  have hA := sub_le_subUp hi (subDown (addUp c0 (bracketShift lo hi)) c0)
  have hB := sub_le_subUp (subUp (addUp c0 (bracketShift lo hi)) c0) lo
  -- each end of the max covers one end of the moved bracket
  have hmA := le_max_left (toReal (subUp hi (subDown (addUp c0 (bracketShift lo hi)) c0)))
    (toReal (subUp (subUp (addUp c0 (bracketShift lo hi)) c0) lo))
  have hmB := le_max_right (toReal (subUp hi (subDown (addUp c0 (bracketShift lo hi)) c0)))
    (toReal (subUp (subUp (addUp c0 (bracketShift lo hi)) c0) lo))
  rw [bracketError, toReal_maximum, abs_le]
  exact ⟨by linarith, by linarith⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A float relaxation out of any bracket for `σ` minus the fit, recentred. The
fit is free and the bracket owes everything, exactly as over ℝ. -/
def PolyRelaxation.ofBracket (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (lo hi : 𝕋 → 𝕋 → 𝕋)
    (hb : ∀ (l u : 𝕋) (t : ℝ), toReal l ≤ t → t ≤ toReal u →
      toReal (lo l u) ≤ σ t - Real.evalPoly (fun k => toReal (c l u k)) t
        ∧ σ t - Real.evalPoly (fun k => toReal (c l u k)) t ≤ toReal (hi l u)) :
    PolyRelaxation 𝕋 σ m where
  coeffs l u := shiftConst (c l u) (bracketShift (lo l u) (hi l u))
  error l u := bracketError (c l u 0) (lo l u) (hi l u)
  sound {l u t} hl hu := by
    obtain ⟨h1, h2⟩ := hb l u t hl hu
    rw [evalPoly_shiftConst, sub_add_eq_sub_sub]
    exact abs_sub_le_bracketError h1 h2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
