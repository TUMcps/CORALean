import CORALean.Global.Tensor

/-!
# Reading one block of a concatenated vector

`Fin.append` builds a vector out of two; these read the halves back, as linear
maps rather than as functions, so that a constraint on one half becomes a
constraint on the whole by `comap` and no sum has to be split.

That is what lets an operation which concatenates coefficient vectors — a
constrained zonotope's `plus`, or its multiplication by an interval matrix —
state its constraints by composing polytopes instead of assembling matrix rows.

`blockLast` is the same for a block of one, landing in the scalar rather than in
a vector, which is the form a single appended parameter is read in.

`blockPadLeft` and `blockPadRight` go the other way, putting a vector into one
half and zero into the other. A set's image under the two, summed, is its
Cartesian product with the other half's set, which is how a product of sets is
taken inside one `Vec` rather than in a pair type.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

/-- The first `m` coordinates. -/
def blockLeft (m n : ℕ) : Vec ℝ (m + n) →ₗ[ℝ] Vec ℝ m where
  toFun v := fun j => v (Fin.castAdd n j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The last `n` coordinates. -/
def blockRight (m n : ℕ) : Vec ℝ (m + n) →ₗ[ℝ] Vec ℝ n where
  toFun v := fun j => v (Fin.natAdd m j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem blockLeft_append {m n : ℕ} (u : Vec ℝ m) (v : Vec ℝ n) :
    blockLeft m n (Fin.append u v) = u :=
  funext fun j => Fin.append_left u v j

@[simp] theorem blockRight_append {m n : ℕ} (u : Vec ℝ m) (v : Vec ℝ n) :
    blockRight m n (Fin.append u v) = v :=
  funext fun j => Fin.append_right u v j

/-- A vector put into the first `m` coordinates, zero in the last `n`. -/
def blockPadLeft (m n : ℕ) : Vec ℝ m →ₗ[ℝ] Vec ℝ (m + n) where
  toFun u := Fin.append u 0
  map_add' _ _ := by funext j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
  map_smul' _ _ := by funext j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

/-- A vector put into the last `n` coordinates, zero in the first `m`. -/
def blockPadRight (m n : ℕ) : Vec ℝ n →ₗ[ℝ] Vec ℝ (m + n) where
  toFun v := Fin.append 0 v
  map_add' _ _ := by funext j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
  map_smul' _ _ := by funext j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

/-- The coordinate a trailing one-column block holds, as a functional: what an
operation that appends a single parameter names it with. -/
def blockLast (m : ℕ) : Vec ℝ (m + 1) →ₗ[ℝ] ℝ where
  toFun v := v (Fin.natAdd m 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem blockLast_append {m : ℕ} (u : Vec ℝ m) (w : Vec ℝ 1) :
    blockLast m (Fin.append u w) = w 0 :=
  Fin.append_right u w 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
