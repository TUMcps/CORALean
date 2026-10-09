import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError
import CORALean.Global.Float.Exp
import CORALean.Global.Float.ToRat

/-!
# `girardReach` in floats: [1, Alg. 1]

`girardReach` computed in `𝕋`, one `let` per printed line as there, the exact quantities
replaced by float enclosures: `e^{rA}` by `[e^{rA}]` (`expIntervalFloat` at an order
`reachOrderFloat` admits), `‖A‖` by the float bound `normUpperBound`, `e^{r‖A‖}` by `expUp`,
`sup_{x∈I} ‖x‖` by the largest `absBoundError`, which covers `I`'s error box too, and `α_r`,
`β_r` rounded up. `β_r = (e^{r‖A‖} - 1)/‖A‖ · μ` grows with `‖A‖`, so dividing by an upper
bound on it is sound. `□(c)` is the box `[-c, c]ⁿ` as a zonotope. `N = ⌈T/r⌉` is computed
in ℚ from the float step, read back through `ToRat`; `expUp`'s precision is chosen there too,
as one past the bit length of `⌈r‖A‖⌉`, which keeps its argument in range.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] in floats: `Q₀ = P₀ + □(α_r + β_r)`, then `Qᵢ = [e^{rA}]Qᵢ₋₁ + □(β_r)` for
`i < N`, returned as the list of the `Qᵢ`, or `none` if no order admits `[e^{rA}]`. -/
def LinearSys.girardReachFloat (sys : LinearSys 𝕋 n) (I : Zonotope 𝕋 n) (μ r : 𝕋) (T : ℚ) :
    Option (List (Zonotope 𝕋 n)) := do
  let N := ⌈T / ToRat.toRat r⌉₊                                     -- N = ⌈T/r⌉
  let η ← sys.reachOrderFloat r r 2                                 -- an order [e^{rA}] admits
  let eRA := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- [e^{rA}] ·
    (sys.expIntervalFloat r r η)
  let nA := MatExp.normUpperBound (Interval.point sys.A)            -- ≥ ‖A‖
  let x := mulUp r nA                                               -- ≥ r‖A‖
  let E := expUp (Nat.log2 (⌈ToRat.toRat x⌉₊ + 1) + 5) x            -- ≥ e^{r‖A‖}
  let s := maximum zero (maximumOver fun j => I.absBoundError j)    -- ≥ sup_{x∈I} ‖x‖
  let αr := mulUp (subUp (subUp E one) x) s                         -- α_r
  let βr := mulUp (divUp (subUp E one) nA) μ                        -- β_r
  let cube := fun c : 𝕋 => (⟨fun _ => neg c, fun _ => c⟩ : Interval (Vec 𝕋 n)).zonotope  -- □(c)
  let P₀ := LinComb.linComb I (eRA I)                               -- P₀ = conv(I, [e^{rA}] I)
  let Q₀ := P₀ ⊞ cube (addUp αr βr)                                 -- Q₀ = P₀ + □(α_r + β_r)
  let R₀ := [Q₀]                                                    -- R₀ = Q₀
  pure ((List.range (N - 1)).foldl
    (fun (QR : Zonotope 𝕋 n × List (Zonotope 𝕋 n)) _ =>
      let Pᵢ := eRA QR.1                                            -- Pᵢ = [e^{rA}] Qᵢ₋₁
      let Qᵢ := Pᵢ ⊞ cube βr                                        -- Qᵢ = Pᵢ + □(β_r)
      let Rᵢ := QR.2 ++ [Qᵢ]                                        -- Rᵢ = Rᵢ₋₁ ∪ Qᵢ
      (Qᵢ, Rᵢ))
    (Q₀, R₀)).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
