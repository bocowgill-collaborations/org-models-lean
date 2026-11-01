import OrgLib.NK.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.BigOperators

/-!
# Exact rational-to-real interpretation of NK evaluation

The rational evaluator and the real-valued model use the same topology, local words,
tables, and averaging definition. Casting each rational table entry therefore commutes
with contribution and fitness evaluation. No contribution bounds are needed.

These theorems concern exact arithmetic. They do not identify rational evaluation
with an R floating-point computation or certify the R interpreter.
-/

namespace OrgLib.NK

variable {N K : ℕ}

/-- Casting table entries to the reals preserves the exact local contribution. -/
theorem contribution_ratCast (T : Topology N K) (c : Tables N K ℚ)
    (x : Config N) (i : Fin N) :
    ((contribution T c x i : ℚ) : ℝ) =
      contribution T (fun j w ↦ (c j w : ℝ)) x i :=
  rfl

/-- T12: exact rational fitness casts to the real fitness of the cast table entries. -/
theorem fitness_ratCast (T : Topology N K) (c : Tables N K ℚ) (x : Config N) :
    ((fitness T c x : ℚ) : ℝ) = fitness T (fun i w ↦ (c i w : ℝ)) x := by
  simp [fitness, contribution]

end OrgLib.NK
