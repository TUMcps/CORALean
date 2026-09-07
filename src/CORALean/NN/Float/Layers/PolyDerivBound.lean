import CORALean.NN.Float.Layers.Activation
import CORALean.NN.Float.Layers.PolyEval
import CORALean.NN.Layers.PolyDerivBound

/-!
# Bounding the fit's derivative in floating point

What `ofSampling` asks for and nothing else supplies: an `M` with
`|σ' - p'| ≤ M` on the box, as a float. The exact argument is `PolyDerivBound`'s
— the fit's derivative bracketed around its linear coefficient, which no box
widens, against a bracket for `σ'` — and the float layer changes only where the
rounding goes.

The centre is stored exactly, being one coefficient copied. Everything else
rounds up: the spread of the `σ'` bracket around that centre through `subUp`,
the radius through `sumUp` and `mulUp`, and the two through one `addUp`.

The degree count `(i : ℕ)` is a natural, so it reaches the scalar as
`nsmulUp i one` — an upper bound rather than a cast, `FloatOps` having no
integer literal above one. It is exact wherever the format can hold `i`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The fit's linear coefficient, which is its whole derivative at order 1 and
which no box widens. Below order 1 there is none, and the centre is zero. -/
def polyDerivCenter (c : Fin (n + 1) → 𝕋) : 𝕋 := if h : 1 < n + 1 then c ⟨1, h⟩ else zero

theorem toReal_polyDerivCenter (c : Fin (n + 1) → 𝕋) :
    toReal (polyDerivCenter c)
      = Real.polyDerivCenter (fun k => toReal (c k)) := by -- --- PROOF ---
  show toReal (if h : 1 < n + 1 then c ⟨1, h⟩ else zero)
    = ∑ i : Fin (n + 1), if (i : ℕ) = 1 then toReal (c i) else 0
  by_cases h : 1 < n + 1
  · -- one index carries the linear term and every other contributes nothing
    have hsum : (∑ i : Fin (n + 1), if (i : ℕ) = 1 then toReal (c i) else 0)
        = toReal (c ⟨1, h⟩) := by
      rw [Finset.sum_eq_single (⟨1, h⟩ : Fin (n + 1))]
      · rw [if_pos rfl]
      · exact fun b _ hb => if_neg fun hb1 => hb (Fin.ext hb1)
      · exact fun hmem => absurd (Finset.mem_univ _) hmem
    rw [dif_pos h, hsum]
  · have hn : n = 0 := by omega
    subst hn
    rw [dif_neg h, toReal_zero, Fin.sum_univ_one, if_neg (by norm_num)]

/-- How far the remaining monomials move that centre over the box: every one at
the end furthest from zero, and every sign taken against itself. -/
def polyDerivRadiusUp (c : Fin (n + 1) → 𝕋) (l u : 𝕋) : 𝕋 :=
  sumUp fun i => if (i : ℕ) = 1 then zero
    else mulUp (mulUp (absolute (c i)) (nsmulUp (i : ℕ) one))
      (powRange (maximum (absolute l) (absolute u)) ((i : ℕ) - 1)).2

theorem polyDerivRadius_le (c : Fin (n + 1) → 𝕋) (l u : 𝕋) :
    Real.polyDerivRadius (fun k => toReal (c k)) (toReal l) (toReal u)
      ≤ toReal (polyDerivRadiusUp c l u) := by -- --- PROOF ---
  show (∑ i : Fin (n + 1), if (i : ℕ) = 1 then (0 : ℝ)
    else |toReal (c i)| * (i : ℕ) * max |toReal l| |toReal u| ^ ((i : ℕ) - 1)) ≤ _
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
  by_cases hi : (i : ℕ) = 1
  · rw [if_pos hi, if_pos hi, toReal_zero]
  · rw [if_neg hi, if_neg hi]
    -- the box's worse end, the degree count from above, and the coefficient exactly
    have hm : toReal (maximum (absolute l) (absolute u)) = max |toReal l| |toReal u| := by
      rw [toReal_maximum, toReal_absolute, toReal_absolute]
    have hp := (powRange_bounds (maximum (absolute l) (absolute u)) ((i : ℕ) - 1)).2
    rw [hm] at hp
    have hnat : ((i : ℕ) : ℝ) ≤ toReal (nsmulUp (i : ℕ) (one : 𝕋)) := by
      have hn := le_nsmulUp (i : ℕ) (one : 𝕋)
      rwa [toReal_one, mul_one] at hn
    have h1 : |toReal (c i)| * ((i : ℕ) : ℝ)
        ≤ toReal (mulUp (absolute (c i)) (nsmulUp (i : ℕ) one)) := by
      refine le_trans ?_ (mul_le_mulUp _ _)
      rw [toReal_absolute]
      exact mul_le_mul_of_nonneg_left hnat (abs_nonneg _)
    have h0 : (0 : ℝ) ≤ |toReal (c i)| * ((i : ℕ) : ℝ) :=
      mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
    refine le_trans (mul_le_mul h1 hp (by positivity) (le_trans h0 h1)) (mul_le_mulUp _ _)

/-- The `M` that `ofSampling` asks for: the `σ'` bracket's spread around the
centre, plus the radius the rest of the fit's derivative can reach. -/
def polyDerivBoundUp (c : Fin (n + 1) → 𝕋) (loD hiD l u : 𝕋) : 𝕋 :=
  addUp (maximum (subUp hiD (polyDerivCenter c)) (subUp (polyDerivCenter c) loD))
    (polyDerivRadiusUp c l u)


-- =======================================  MAIN THEOREM  ======================================= --

/-- A bracket for `σ'` over the box bounds what `ofSampling` asks about, the
fit's own derivative being bracketed by construction. -/
theorem abs_sub_evalPolyDeriv_le {c : Fin (n + 1) → 𝕋} {σ' : ℝ → ℝ} {loD hiD l u : 𝕋}
    {x : ℝ} (hlo : toReal loD ≤ σ' x) (hhi : σ' x ≤ toReal hiD)
    (hl : toReal l ≤ x) (hu : x ≤ toReal u) :
    |σ' x - Real.evalPolyDeriv (fun k => toReal (c k)) x|
      ≤ toReal (polyDerivBoundUp c loD hiD l u) := by -- --- PROOF ---
  have h1 := abs_sub_le_spread (c := polyDerivCenter c) hlo hhi
  have h2 := Real.abs_evalPolyDeriv_sub_center_le (fun k => toReal (c k)) hl hu
  have h3 := polyDerivRadius_le c l u
  have h4 := add_le_addUp (maximum (subUp hiD (polyDerivCenter c))
    (subUp (polyDerivCenter c) loD)) (polyDerivRadiusUp c l u)
  rw [toReal_polyDerivCenter] at h1
  rw [polyDerivBoundUp]
  -- the difference splits at the centre: the bracket's spread, then the radius
  calc |σ' x - Real.evalPolyDeriv (fun k => toReal (c k)) x|
      ≤ |σ' x - Real.polyDerivCenter (fun k => toReal (c k))|
        + |Real.polyDerivCenter (fun k => toReal (c k))
          - Real.evalPolyDeriv (fun k => toReal (c k)) x| := abs_sub_le _ _ _
    _ ≤ toReal (addUp (maximum (subUp hiD (polyDerivCenter c))
        (subUp (polyDerivCenter c) loD)) (polyDerivRadiusUp c l u)) := by
      rw [abs_sub_comm (Real.polyDerivCenter fun k => toReal (c k))]
      linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
