module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Operations.Smul

@[expose] public section

/-!
# Interval matrices: the Taylor series past order two, over a floating-point scalar

`expIntervalTaylorTail`: orders `3 … κ` of [1, Thm. 1]'s Taylor series at an interval matrix,
`Real.MatExp.expIntervalTaylorTail` rounded. Each order is `Interval.smul` at
`invFactorialBounds`, the float layer's only handle on `1/k!`, and below order three there
are none, so `κ < 3` is the truncation `I + W(t)`.

Each partial sum is `materialiseMat`d before the next term is added, and what runs carries the
power along instead of rebuilding `Bᵏ` at every order, by `@[csimp]`, exactly as
`expIntervalTaylor` does.

## Inputs
* `B` – float interval matrix

## Output
* float interval matrix of the Taylor terms from order three up to the given order

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Orders `3 … κ` of the Taylor series at an interval matrix. Below order three there are
none. -/
def MatExp.expIntervalTaylorTail (B : Interval (Mat 𝕋 n n)) : ℕ → Interval (Mat 𝕋 n n)
  | 0 => Interval.point fun _ _ => zero
  | 1 => Interval.point fun _ _ => zero
  | 2 => Interval.point fun _ _ => zero
  | k + 3 => (Interval.matPlus
      (Interval.smul (MatExp.invFactorialBounds (k + 3)).inf (MatExp.invFactorialBounds (k + 3)).sup
        (Interval.matPow B (k + 3)))
      (MatExp.expIntervalTaylorTail B (k + 2))).materialiseMat


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The power and the tail at order `k`, the power carried from one order to the next. -/
def MatExp.aux_expIntervalTaylorTailPair (B : Interval (Mat 𝕋 n n)) :
    ℕ → Interval (Mat 𝕋 n n) × Interval (Mat 𝕋 n n)
  | 0 => (Interval.matPow B 0, Interval.point fun _ _ => zero)
  | k + 1 =>
    let PS := MatExp.aux_expIntervalTaylorTailPair B k
    let P := (Interval.matMul B PS.1).materialiseMat
    (P, if k < 2 then Interval.point fun _ _ => zero
      else (Interval.matPlus (Interval.smul (MatExp.invFactorialBounds (k + 1)).inf
        (MatExp.invFactorialBounds (k + 1)).sup P) PS.2).materialiseMat)

/-- The same tail, one product per order rather than `κ` of them. -/
def MatExp.aux_expIntervalTaylorTailImpl (B : Interval (Mat 𝕋 n n)) (k : ℕ) :
    Interval (Mat 𝕋 n n) :=
  (MatExp.aux_expIntervalTaylorTailPair B k).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
