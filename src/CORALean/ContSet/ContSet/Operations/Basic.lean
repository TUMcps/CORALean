module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.ContSet.Operations.Minus
public import CORALean.Global.NegScalar

@[expose] public section

/-!
# `ContSet/ContSet/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

section

open ContSet

variable {S α : Type} [ContSet S α] [Isequal S]


-- =======================================  `ContSet.eq`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `eq`: `res = isequal(S1, S2)`. -/
def ContSet.eq (s t : S) : Prop := Isequal.isequal s t


-- =======================================  `ContSet.ne`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `ne`: `res = ~isequal(S1, S2)`. -/
def ContSet.ne (s t : S) : Prop := ¬ Isequal.isequal s t

end


section

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] [Neg 𝕋] [NegScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}


-- =====================================  `ContSet.uminus`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- CORA's `uminus`: `S = -1 * S`.

`-1 * S`, as CORA's `uminus` has it, through the set's own `mtimes`. -/
def ContSet.uminus (s : S n) : S n :=
  let A : Mat 𝕋 n n := -1
  Mtimes.mtimes A s

end


section

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] [Neg 𝕋] [NegScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ} [∀ n, Plus (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)]


-- ===================================  `ContSet.minusFrom`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `minus` for a numeric minuend `p`: `S = -S + p`.

`-S + p`, CORA's second case, where a vector is subtracted from a set the other way round. -/
def ContSet.minusFrom (p : Vec ℝ n) (s : S n) : S n :=
  Plus.plus (ContSet.uminus (𝕋 := 𝕋) s) (OfPoint.ofPoint p)

end


section

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] [Neg 𝕋] [NegScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ} [∀ n, Plus (S n) (Vec ℝ n)]
variable [OfScalarPoint 𝕋 S]


-- ================================  `ContSet.minusFromScalar`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `minus` for a numeric minuend `p`: `S = -S + p`.

`-S + p`, as `ContSet.minusFrom`, the point a vector of the representation's own scalar. -/
def ContSet.minusFromScalar (p : Vec 𝕋 n) (s : S n) : S n :=
  Plus.plus (ContSet.uminus (𝕋 := 𝕋) s) (OfScalarPoint.ofVec (𝕋 := 𝕋) p)

end


section

open ContSet Scalar

variable {S α : Type} [ContSet S α]


-- =====================================  `ContSet.uplus`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `uplus`: `S = S`.

CORA's `uplus` is the identity, so it takes no operation class. -/
def ContSet.uplus (s : S) : S := s

end

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
