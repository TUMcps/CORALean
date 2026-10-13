module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Operations.Smul

@[expose] public section

/-!
# Interval matrices: the Taylor series past order two, over a floating-point scalar

`expIntervalTaylorTail`: orders `3 … κ` of [1, Thm. 3.2]'s Taylor series at an interval matrix,
`Real.MatExp.expIntervalTaylorTail` rounded. Each order is `Interval.smul` at
`invFactorialBounds`, the float layer's only handle on `1/k!`, and below order three there
are none, so `κ < 3` is the truncation `I + W(t)`.

Each partial sum is `materialiseMat`d before the next term is added, and what runs carries the
power along instead of rebuilding `Bᵏ` at every order, by `@[csimp]`, exactly as
`expIntervalTaylor` does.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
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
      (Interval.smul (MatExp.invFactorialBounds (k + 3)).1 (MatExp.invFactorialBounds (k + 3)).2
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
      else (Interval.matPlus (Interval.smul (MatExp.invFactorialBounds (k + 1)).1
        (MatExp.invFactorialBounds (k + 1)).2 P) PS.2).materialiseMat)

/-- The same tail, one product per order rather than `κ` of them. -/
def MatExp.aux_expIntervalTaylorTailImpl (B : Interval (Mat 𝕋 n n)) (k : ℕ) :
    Interval (Mat 𝕋 n n) :=
  (MatExp.aux_expIntervalTaylorTailPair B k).2

@[csimp] theorem MatExp.aux_expIntervalTaylorTail_eq_impl :
    @MatExp.expIntervalTaylorTail = @MatExp.aux_expIntervalTaylorTailImpl := by -- --- PROOF ---
  funext 𝕋 _ n B k
  have hpair : ∀ k, MatExp.aux_expIntervalTaylorTailPair B k
      = (Interval.matPow B k, MatExp.expIntervalTaylorTail B k) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [MatExp.aux_expIntervalTaylorTailPair, ih]
      match k with
      | 0 => rfl
      | 1 => rfl
      | m + 2 => rfl
  rw [MatExp.aux_expIntervalTaylorTailImpl, hpair]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
