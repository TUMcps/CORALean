module

/-!
# Polynomial level sets at float, collected

No float representation yet. A float constrained polynomial zonotope keeps its constraint rows in
its own fields, each with its recorded rounding `b_error`; a polynomial level set of its own at
float would have to move an error box into polynomial rows, which takes a bound on the
polynomial's variation over the box that an unbounded set does not supply.
-/
