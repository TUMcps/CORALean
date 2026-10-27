module

public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.Interfaces
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

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

## Inputs
* `sys` – linear system
* `I` – initial float zonotope
* `μ` – float input norm bound
* `r` – float step length
* `T` – time horizon

## Output
* float zonotopes covering the horizon, if some order admits the exponential

## References

* [1] [A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". Hybrid Systems:
      Computation and Control,
      2005.](../../../../../references/2005/girard-hscc-reachability-zonotopes.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] in floats: `Q₀ = P₀ + □(α_r + β_r)`, then `Qᵢ = [e^{rA}]Qᵢ₋₁ + □(β_r)` for
`i < N`, returned as the list of the `Qᵢ`, or `none` if no order admits `[e^{rA}]`. -/
def LinearSys.girardReachFloat (sys : LinearSys 𝕋 n) (I : Zonotope (Vec 𝕋 n)) (μ r : 𝕋) (T : ℚ) :
    Option (List (Zonotope (Vec 𝕋 n))) := do
  -- 1. N = ⌈T/r⌉
  let N := ⌈T / ToRat.toRat r⌉₊
  let η ← sys.reachOrderFloat r r 2                                 -- an order [e^{rA}] admits
  let eRA := Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- [e^{rA}] ·
    (S := 𝒵[𝕋])
    (sys.expIntervalFloat r r η)
  let nA := MatExp.normUpperBound (Interval.point sys.A)            -- ≥ ‖A‖
  let x := mulUp r nA                                               -- ≥ r‖A‖
  let E := expUp (Nat.log2 (⌈ToRat.toRat x⌉₊ + 1) + 5) x            -- ≥ e^{r‖A‖}
  let s := maximum zero (maximumOver fun j => I.absBoundError j)    -- ≥ sup_{x∈I} ‖x‖
  -- 2. α_r
  let αr := mulUp (subUp (subUp E one) x) s
  -- 3. β_r
  let βr := mulUp (divUp (subUp E one) nA) μ
  let cube := fun c : 𝕋 => (⟨fun _ => neg c, fun _ => c⟩ : Interval (Vec 𝕋 n)).zonotope  -- □(c)
  -- 4. P₀ = conv(I, [e^{rA}] I)
  let P₀ := LinComb.linComb I (eRA I)
  -- 5. Q₀ = P₀ + □(α_r + β_r)
  let Q₀ := P₀ ⊞ cube (addUp αr βr)
  -- 6. R₀ = Q₀
  let R₀ := [Q₀]
  -- 7. for i = 1 … N - 1
  pure ((List.range (N - 1)).foldl
    (fun (QR : Zonotope (Vec 𝕋 n) × List (Zonotope (Vec 𝕋 n))) _ =>
      -- 8. Pᵢ = [e^{rA}] Qᵢ₋₁
      let Pᵢ := eRA QR.1
      -- 9. Qᵢ = Pᵢ + □(β_r)
      let Qᵢ := Pᵢ ⊞ cube βr
      -- 10. Rᵢ = Rᵢ₋₁ ∪ Qᵢ
      let Rᵢ := QR.2 ++ [Qᵢ]
      (Qᵢ, Rᵢ))
    (Q₀, R₀)).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
