module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Operations.Smul

@[expose] public section

/-!
# `MatExp.expIntervalTaylor`, over a floating-point scalar

`Real.MatExp.expIntervalTaylor` rounded: `i = 0 … η` matching that recursion
term by term, each term `Interval.smul` at `invFactorialBounds i` — the float
layer's only handle on `1/i!`, which no float exactly holds.

Each partial sum is `materialiseMat`d before the next term is added to it, for
the reason `Interval.matPow`'s own recursion is: left as a closure, `η` nested
`matPlus`es would rebuild the whole sum on every entry read. What runs carries
the power along instead of rebuilding `Aⁱ` at every order, by `@[csimp]`: the
same products in the same order, so the same values.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.expIntervalTaylor (A : Interval (Mat 𝕋 n n)) : ℕ → Interval (Mat 𝕋 n n)
  | 0 => Interval.smul (MatExp.invFactorialBounds 0).inf (MatExp.invFactorialBounds 0).sup
      (Interval.matPow A 0)
  | k + 1 => (Interval.matPlus
      (Interval.smul (MatExp.invFactorialBounds (k + 1)).inf (MatExp.invFactorialBounds (k + 1)).sup
        (Interval.matPow A (k + 1)))
      (MatExp.expIntervalTaylor A k)).materialiseMat


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The power and the partial sum at order `k`, the power carried from one order
to the next by `matPow`'s own step. -/
def MatExp.aux_expIntervalTaylorPair (A : Interval (Mat 𝕋 n n)) :
    ℕ → Interval (Mat 𝕋 n n) × Interval (Mat 𝕋 n n)
  | 0 => (Interval.matPow A 0, Interval.smul (MatExp.invFactorialBounds 0).inf
      (MatExp.invFactorialBounds 0).sup (Interval.matPow A 0))
  | k + 1 =>
    let PS := MatExp.aux_expIntervalTaylorPair A k
    let P := (Interval.matMul A PS.1).materialiseMat
    (P, (Interval.matPlus (Interval.smul (MatExp.invFactorialBounds (k + 1)).inf
      (MatExp.invFactorialBounds (k + 1)).sup P) PS.2).materialiseMat)

/-- The same sum, `η` products rather than `η²/2`. -/
def MatExp.aux_expIntervalTaylorImpl (A : Interval (Mat 𝕋 n n)) (k : ℕ) : Interval (Mat 𝕋 n n) :=
  (MatExp.aux_expIntervalTaylorPair A k).2

@[csimp] theorem MatExp.aux_expIntervalTaylor_eq_impl :
    @MatExp.expIntervalTaylor = @MatExp.aux_expIntervalTaylorImpl := by -- --- PROOF ---
  funext 𝕋 _ n A k
  -- the pair is the power and the sum, order by order
  have hpair : ∀ k, MatExp.aux_expIntervalTaylorPair A k
      = (Interval.matPow A k, MatExp.expIntervalTaylor A k) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [MatExp.aux_expIntervalTaylorPair, ih]; rfl
  rw [MatExp.aux_expIntervalTaylorImpl, hpair]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
