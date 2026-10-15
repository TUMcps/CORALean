module

public import CORALean.ContSet.Taylm.Float.Operations.BernsteinStep
public import CORALean.ContSet.Taylm.Float.Operations.ProdBounds
public import CORALean.ContSet.Taylm.Float.Operations.Smul
public import CORALean.ContSet.Taylm.Float.Operations.TermBounds
public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.Global.Float.FloatOps
public import CORALean.Global.Float.ListSum

@[expose] public section

/-!
# `ContSet/Taylm/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

section

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  `Taylm.belowPow`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The range `expUp p` is sound on: halve `x` `p` times, which `half` does exactly, and compare
with `1/2`. -/
def Taylm.belowPow (p : ℕ) (x : 𝕋) : Bool := le (half^[p] x) (half one)


-- ===============================  `Taylm.bernsteinEntryBounds`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- `bernsteinEntry N e j`, the sum over `i ≤ e` of its terms, between two floats: the terms'
`bernsteinStep` brackets, the lower ends summed down and the upper ends summed up. -/
def Taylm.bernsteinEntryBounds (N e j : ℕ) : Interval 𝕋 :=
  ⟨listSumDown ((List.range (e + 1)).map fun i => (Taylm.bernsteinStep (𝕋 := 𝕋) N e j i).inf),
    listSumUp ((List.range (e + 1)).map fun i => (Taylm.bernsteinStep (𝕋 := 𝕋) N e j i).sup)⟩


-- ======================================  `Taylm.boxMid`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The midpoint of a box, `(l + u) / 2` with the sum rounded up. -/
def Taylm.boxMid (B : Fin n → Interval 𝕋) : Vec 𝕋 n := fun k => half (addUp (B k).inf (B k).sup)


-- ======================================  `Taylm.boxRad`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- A radius around the stored midpoint reaching both ends of the box: the larger of the two gaps,
rounded up. -/
def Taylm.boxRad (B : Fin n → Interval 𝕋) : Vec 𝕋 n :=
  fun k => maximum (subUp (B k).sup (Taylm.boxMid B k)) (subUp (Taylm.boxMid B k) (B k).inf)


-- ======================================  `Taylm.const`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constant Taylor model -/
def Taylm.const (n : ℕ) (c : 𝕋) (N : ℕ) : Taylm 𝕋 n := ⟨[(c, 0)], zero, zero, N⟩


-- ====================================  `Taylm.constCoef`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Summed downward; any float is a sound center, so the rounding costs only precision. -/
def Taylm.constCoef (T : Taylm 𝕋 n) : 𝕋 :=
  listSumDown ((T.terms.filter fun a => Real.Taylm.degree a.2 == 0).map Prod.fst)


-- ======================================  `Taylm.empty`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The empty model in each coordinate: no terms and the crossed remainder, lower bound `one`
and upper bound `zero`. -/
def Taylm.empty (n : ℕ) : Fin n → Taylm 𝕋 n :=
  fun _ => ⟨[], one, zero, 0⟩


-- =====================================  `Taylm.listMax`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The largest of `f` over a list, `zero` for the empty list. -/
def Taylm.listMax {α : Type} (f : α → 𝕋) : List α → 𝕋
  | [] => zero
  | [a] => f a
  | a :: b :: l => maximum (f a) (Taylm.listMax f (b :: l))


-- =====================================  `Taylm.listMin`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The smallest of `f` over a list, `zero` for the empty list. -/
def Taylm.listMin {α : Type} (f : α → 𝕋) : List α → 𝕋
  | [] => zero
  | [a] => f a
  | a :: b :: l => minimum (f a) (Taylm.listMin f (b :: l))


-- =======================================  `Taylm.plus`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The term lists side by side, which rounds nothing; only the remainder sum rounds outward. -/
def Taylm.plus (T₁ T₂ : Taylm 𝕋 n) : Taylm 𝕋 n :=
  ⟨T₁.terms ++ T₂.terms, addDown T₁.remInf T₂.remInf, addUp T₁.remSup T₂.remSup,
    max T₁.maxOrder T₂.maxOrder⟩


-- ====================================  `Taylm.polyBounds`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The term ranges summed, each end rounded outward. -/
def Taylm.polyBounds (L : List (𝕋 × (Fin n → ℕ))) : Interval 𝕋 :=
  ⟨listSumDown (L.map fun a => (Taylm.termBounds a).inf),
    listSumUp (L.map fun a => (Taylm.termBounds a).sup)⟩


-- ======================================  `Taylm.bounds`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The range of a Taylor model -/
def Taylm.bounds (T : Taylm 𝕋 n) : Interval 𝕋 :=
  ⟨addDown (Taylm.polyBounds T.terms).inf T.remInf, addUp (Taylm.polyBounds T.terms).sup T.remSup⟩


-- ======================================  `Taylm.magUp`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The largest absolute value of the constant part and the two ends of the range: a bound of
`|ξ|` on the hull of the center and the range, which is where a Lagrange remainder looks for
the derivative. -/
def Taylm.magUp (T : Taylm 𝕋 n) : 𝕋 :=
  maximum (absolute T.constCoef) (maximum (absolute T.bounds.inf) (absolute T.bounds.sup))


-- =======================================  `Taylm.sum`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Taylm.sum` -/
def Taylm.sum : {m : ℕ} → (Fin m → Taylm 𝕋 n) → Taylm 𝕋 n
  | 0, _ => ⟨[], zero, zero, 0⟩
  | _ + 1, T => (T 0).plus (Taylm.sum fun i => T i.succ)


-- ======================================  `Taylm.mtimes`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- By a float matrix, each entry an exact factor, `smul` at `alo = ahi`. -/
def Taylm.mtimes {k m : ℕ} (M : Mat 𝕋 k m) (T : Fin m → Taylm 𝕋 n) : Fin k → Taylm 𝕋 n :=
  fun i => Taylm.sum fun j => (T j).smul (M i j) (M i j)


-- ==================================  `Taylm.termBoxBounds`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The range of one term `c ∏ tₖ ^ eₖ` over a box `B`: the power ranges of the coordinates
multiplied, then the coefficient, every end rounded outward. -/
def Taylm.termBoxBounds (B : Fin n → Interval 𝕋) (a : 𝕋 × (Fin n → ℕ)) : Interval 𝕋 :=
  let M := Taylm.prodBounds fun k => Taylm.powBounds (B k).inf (B k).sup (a.2 k)
  ⟨Interval.mulLo a.1 a.1 M.inf M.sup, Interval.mulHi a.1 a.1 M.inf M.sup⟩


-- ==================================  `Taylm.polyBoxBounds`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The range of a term list over a box `B`: the term ranges summed, each end rounded outward. -/
def Taylm.polyBoxBounds (L : List (𝕋 × (Fin n → ℕ))) (B : Fin n → Interval 𝕋) : Interval 𝕋 :=
  ⟨listSumDown (L.map fun a => (Taylm.termBoxBounds B a).inf),
    listSumUp (L.map fun a => (Taylm.termBoxBounds B a).sup)⟩


-- ======================================  `Taylm.trace`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The sum of the diagonal, `Taylm.sum` of `A i i`; see the exact layer. -/
def Taylm.trace {k : ℕ} (A : Fin k → Fin k → Taylm 𝕋 n) : Taylm 𝕋 n :=
  Taylm.sum fun i => A i i


-- ======================================  `Taylm.uminus`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Exact: negation is. -/
def Taylm.uminus (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  ⟨T.terms.map fun a => (neg a.1, a.2), neg T.remSup, neg T.remInf, T.maxOrder⟩


-- ======================================  `Taylm.minus`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Taylm.minus` -/
def Taylm.minus (T₁ T₂ : Taylm 𝕋 n) : Taylm 𝕋 n := T₁.plus T₂.uminus


-- ======================================  `Taylm.uplus`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's unary `+`: the model itself. -/
def Taylm.uplus (T : Taylm 𝕋 n) : Taylm 𝕋 n := T

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ======================================  `Taylm.InBox`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- A real point lies in the box whose stored float ends are read as reals. -/
def Taylm.InBox (B : Fin n → Interval 𝕋) (t : Vec ℝ n) : Prop :=
  ∀ k, toReal (B k).inf ≤ t k ∧ t k ≤ toReal (B k).sup


-- ======================================  `Taylm.Covers`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- Every point of the box `X` lies in one of the boxes `l`. -/
def Taylm.Covers (X : Fin n → Interval 𝕋) (l : List (Fin n → Interval 𝕋)) : Prop :=
  ∀ t, Taylm.InBox X t → ∃ B ∈ l, Taylm.InBox B t

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
