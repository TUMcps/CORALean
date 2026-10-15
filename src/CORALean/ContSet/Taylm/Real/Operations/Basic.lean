module

public import CORALean.ContSet.Taylm.Real.Operations.Plus
public import CORALean.ContSet.Taylm.Real.Operations.Smul

@[expose] public section

/-!
# `ContSet/Taylm/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n : ℕ}


-- ======================================  `Taylm.boxMid`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The centre of a box -/
noncomputable def Taylm.boxMid (B : Fin n → Interval ℝ) : Vec ℝ n :=
    fun k => ((B k).inf + (B k).sup) / 2


-- ======================================  `Taylm.boxRad`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The radius of a box -/
noncomputable def Taylm.boxRad (B : Fin n → Interval ℝ) : Vec ℝ n :=
    fun k => ((B k).sup - (B k).inf) / 2


-- ======================================  `Taylm.const`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `aux_addConst` with nothing to add it to: one term at the zero exponent and no
remainder. `compose` subtracts it to centre a model on its constant part. -/
def Taylm.const (n : ℕ) (c : ℝ) (N : ℕ) : Taylm n := ⟨[(c, 0)], ⟨0, 0⟩, N⟩


-- ======================================  `Taylm.degree`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- What `times` truncates against, CORA's hashed first exponent column. -/
def Taylm.degree (e : Fin n → ℕ) : ℕ := ∑ k, e k


-- ====================================  `Taylm.constCoef`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `c_f`, the coefficient at the zero exponent, where the elementary functions expand.
Summed, as the list may repeat the exponent; any centre is sound and this one is CORA's. -/
def Taylm.constCoef (T : Taylm n) : ℝ :=
  ((T.terms.filter fun a => Taylm.degree a.2 == 0).map Prod.fst).sum


-- ======================================  `Taylm.empty`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `empty(n)`: the model of the empty interval in each coordinate, a polynomial of
zero and the crossed remainder `[1, 0]`, which no function can satisfy. -/
def Taylm.empty (n : ℕ) : Fin n → Taylm n :=
  fun _ => ⟨[], ⟨1, 0⟩, 0⟩


-- =====================================  `Taylm.getSyms`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `@taylm/getSyms`: the polynomial part of the model, without its remainder, as a symbolic
expression in the variables, `Σ c · ∏ v ^ degs` over the terms. Here the same polynomial as a
function of the variables; `sym` itself, a MATLAB symbolic object, is not modelled. -/
def Taylm.getSyms (T : Taylm n) (t : Vec ℝ n) : ℝ :=
  (T.terms.map fun a => a.1 * ∏ k, t k ^ a.2 k).sum


-- =====================================  `Taylm.mulTerms`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every pair multiplied, exponents added: CORA's `aux_multiply`, before truncation. -/
def Taylm.mulTerms (L₁ L₂ : List (ℝ × (Fin n → ℕ))) : List (ℝ × (Fin n → ℕ)) :=
  L₁.flatMap fun a => L₂.map fun b => (a.1 * b.1, a.2 + b.2)


-- =======================================  `Taylm.sum`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `sum` of an array of models: `plus` folded from the right, the empty sum being the
zero model. -/
def Taylm.sum : {m : ℕ} → (Fin m → Taylm n) → Taylm n
  | 0, _ => ⟨[], ⟨0, 0⟩, 0⟩
  | _ + 1, T => (T 0).plus (Taylm.sum fun i => T i.succ)


-- ======================================  `Taylm.mtimes`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `mtimes` of a numeric matrix and an array of models: row `i` is `Σⱼ M i j · T j`,
the loop CORA runs with `times` and `plus`. -/
def Taylm.mtimes {k m : ℕ} (M : Mat ℝ k m) (T : Fin m → Taylm n) : Fin k → Taylm n :=
  fun i => Taylm.sum fun j => (T j).smul (M i j)


-- ======================================  `Taylm.uminus`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's unary `-`: every coefficient negated, the remainder reflected. -/
def Taylm.uminus (T : Taylm n) : Taylm n :=
  ⟨T.terms.map fun a => (-a.1, a.2), ⟨-T.rem.sup, -T.rem.inf⟩, T.maxOrder⟩


-- ======================================  `Taylm.uplus`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's unary `+`: the model itself. -/
def Taylm.uplus (T : Taylm n) : Taylm n := T

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
