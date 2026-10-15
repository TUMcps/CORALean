module

public import CORALean.ContSet.HPolytope.Float.Operations.EqScalar
public import CORALean.ContSet.HPolytope.Float.Operations.Eqs
public import CORALean.ContSet.HPolytope.Float.Operations.Fullspace
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.MemEqsIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemIneqsIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadLeft
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadRight
public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
public import CORALean.ContSet.HPolytope.Float.Operations.PadRight
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows
public import CORALean.ContSet.HPolytope.Float.Operations.Translate

@[expose] public section

/-!
# `ContSet/HPolytope/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

section

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ====================================  `HPolytope.errUp`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- The most the row `a` reads on the error box, rounded up: each term at the end of its
coordinate's range the sign of `aⱼ` picks. -/
def HPolytope.errUp (P : HPolytope 𝕋 (Vec 𝕋 n)) (a : Vec 𝕋 n) : 𝕋 :=
  sumUp fun j => maximum (mulUp (a j) (P.I_error.sup j)) (mulUp (a j) (P.I_error.inf j))


-- =====================================  `HPolytope.beLN`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The negated lower end of equality row `i` with the error box folded in, rounded up: the
bound of the row `-Aeᵢ`, so that the equality reads as the two inequalities `Aeᵢ x ≤ beU i` and
`-Aeᵢ x ≤ beLN i`. -/
def HPolytope.beLN (P : HPolytope 𝕋 (Vec 𝕋 n)) (i : Fin P.me) : 𝕋 :=
  addUp (neg (P.be i)) (P.errUp (-(P.Ae i)))


-- =====================================  `HPolytope.beU`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The upper end of equality row `i` with the error box folded in, rounded up. -/
def HPolytope.beU (P : HPolytope 𝕋 (Vec 𝕋 n)) (i : Fin P.me) : 𝕋 :=
  addUp (P.be i) (P.errUp (P.Ae i))


-- ====================================  `HPolytope.beRes`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- How far equality row `i` can read from `beᵢ` on a point of the polytope, its error box
included, rounded up: the larger of the two widenings `beU` and `beLN` add. -/
def HPolytope.beRes (P : HPolytope 𝕋 (Vec 𝕋 n)) (i : Fin P.me) : 𝕋 :=
  maximum (subUp (P.beU i) (P.be i)) (subUp (P.beLN i) (neg (P.be i)))


-- ======================================  `HPolytope.bU`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The right-hand side of inequality row `i` with the error box folded in, rounded up: the
bound every point of the polytope, box included, satisfies. -/
def HPolytope.bU (P : HPolytope 𝕋 (Vec 𝕋 n)) (i : Fin P.m) : 𝕋 :=
  addUp (P.b i) (P.errUp (P.A i))


-- ==================================  `HPolytope.isZeroVec`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- All entries `eqScalar` to `zero`.

Every entry certified equal to `zero`: CORA's `withinTol(row, 0)` at tolerance zero. -/
def HPolytope.isZeroVec (v : Vec 𝕋 n) : Bool :=
  (List.finRange n).all fun j => HPolytope.eqScalar (v j) zero


-- ==================================  `HPolytope.isErrFree`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every bound of the error box certified equal to `zero`: the check that the polytope denotes
its nominal part (`HPolytope.errFree_of_isErrFree`). `false` says nothing. -/
def HPolytope.isErrFree (P : HPolytope 𝕋 (Vec 𝕋 n)) : Bool :=
  HPolytope.isZeroVec P.I_error.inf && HPolytope.isZeroVec P.I_error.sup


-- ====================================  `HPolytope.minus`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The translation by `-v`. Negation is exact, so the subtrahend costs no rounding
of its own; the shift rounds as `translate` does. -/
def HPolytope.minus (P : HPolytope 𝕋 (Vec 𝕋 n)) (v : Vec 𝕋 n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  HPolytope.translate (-v) P

end


section

open Matrix FloatOps SoundFloatArithmetic

-- membership at each shape, the block that is absent discharged by `Fin.elim0`
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ} {S : Set (Vec ℝ n)}


-- ================================  `HPolytope.mem_fullspace`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- Every point is in `HPolytope.fullspace` -/
theorem HPolytope.mem_fullspace (x : Vec ℝ n) :
    x ∈ (HPolytope.fullspace 𝕋 n).construct :=
  (HPolytope.mem_construct_iff (HPolytope.errFree_of_origin rfl)).mpr
    ⟨fun i => i.elim0, fun i => i.elim0⟩


-- ===============================  `HPolytope.subset_ofBounds`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- The rounding has already been paid where each bound was combined, and nothing
rounds here. -/
theorem HPolytope.subset_ofBounds (Aq : Mat 𝕋 q n) (u : ∀ i, FloatBound 𝕋 S (rowLin Aq i)) :
    S ⊆ (HPolytope.ofBounds Aq u).construct :=
  fun x hx => HPolytope.mem_ineqs_iff.mpr fun i => (u i).le x hx

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n n₁ n₂ : ℕ}


-- ===========================  `HPolytope.mem_padLeft_nominal_iff`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Membership of the padded nominal part is membership of the block it came from. -/
theorem HPolytope.mem_padLeft_nominal_iff {P : HPolytope 𝕋 (Vec 𝕋 n₁)} {x : Vec ℝ (n₁ + n₂)} :
    x ∈ (P.padLeft n₂).nominal.construct ↔ blockLeft n₁ n₂ x ∈ P.nominal.construct := by
  rw [HPolytope.mem_nominal_iff, HPolytope.mem_nominal_iff]
  simp only [HPolytope.padLeft, HPolytope.mulVec_padLeft]


-- ===========================  `HPolytope.mem_padRight_nominal_iff`  =========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The mirror statement for the right block. -/
theorem HPolytope.mem_padRight_nominal_iff {P : HPolytope 𝕋 (Vec 𝕋 n₂)} {x : Vec ℝ (n₁ + n₂)} :
    x ∈ (HPolytope.padRight n₁ P).nominal.construct ↔ blockRight n₁ n₂ x ∈ P.nominal.construct := by
  rw [HPolytope.mem_nominal_iff, HPolytope.mem_nominal_iff]
  simp only [HPolytope.padRight, HPolytope.mulVec_padRight]


-- ==============================  `HPolytope.mem_stackRows_iff`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- Membership splits with the rows, each half read on the nominal part it came from. -/
theorem HPolytope.mem_stackRows_iff {P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)} {x : Vec ℝ n} :
    x ∈ (P₁.stackRows P₂).construct ↔ x ∈ P₁.nominal.construct ∧ x ∈ P₂.nominal.construct := by
  rw [HPolytope.construct_eq_nominal (HPolytope.errFree_of_origin rfl)]
  exact HPolytope.mem_stackRows_nominal_iff

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
