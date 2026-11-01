import OrgLib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Executable examples of canonical NK landscapes

These small rational fixtures exercise the public API at zero interactions and maximal
arity. They are constructed directly in Lean and are not translations of either paper's
R code. Numerical checks here concern these exact fixtures only.

The full-arity example uses asymmetric table arguments: permuting scopes alone changes
fitness, while transporting tables with the scopes preserves it.
-/

namespace OrgLibExamples.NK

open OrgLib.NK

/-- The smallest valid topology; its only contribution reads its only bit. -/
def singletonTopology : Topology 1 0 where
  k_lt_n := by decide
  scope := fun i ↦ ⟨fun _ ↦ i, fun a b _ ↦ (Fin.eq_zero a).trans (Fin.eq_zero b).symm⟩
  self := fun _ ↦ rfl

/-- A constant table deliberately ignores its permitted input. -/
def tiedTables : Tables 1 0 ℚ := fun _ _ ↦ 1 / 2

/-- A two-coordinate topology with no interactions. -/
def separateTopology : Topology 2 0 where
  k_lt_n := by decide
  scope := fun i ↦ ⟨fun _ ↦ i, fun a b _ ↦ (Fin.eq_zero a).trans (Fin.eq_zero b).symm⟩
  self := fun _ ↦ rfl

/-- Both coordinates prefer true, with distinct gains of one and one half. -/
def separateTables : Tables 2 0 ℚ :=
  fun i w ↦ if w 0 then (if i = 0 then 1 else 1 / 2) else 0

/-- The all-true candidate for the separable example. -/
def separateBest : Config 2 := fun _ ↦ true

/-- At maximal arity every scope includes all three loci, in focal-first order. -/
def fullTopology : Topology 3 2 where
  k_lt_n := by decide
  scope := fun i ↦ (Equiv.swap 0 i).toEmbedding
  self := Equiv.swap_apply_left 0

/-- Unequal slot weights detect an unaccompanied change of scope order. -/
def asymmetricTables : Tables 3 2 ℚ :=
  fun i w ↦ (if w 0 then 1 else 0) +
    (if w 1 then 2 else 0) + (if w 2 then 4 else 0) + i.val

/-- Keep the focal slot fixed and exchange the two interaction slots. -/
def swapInteractions : Fin 3 → Equiv.Perm (Fin 3) := fun _ ↦ Equiv.swap 1 2

/-- This permutation meets the reindexing API's focal-slot condition. -/
theorem swapInteractions_fix_zero (i : Fin 3) : swapInteractions i 0 = 0 := by
  rfl

/-- A configuration that distinguishes the two interaction slots. -/
def fullState : Config 3 := fun j ↦ j == 1

/-- The tied singleton has fitness one half at every state. -/
theorem tied_fitness (x : Config 1) :
    fitness singletonTopology tiedTables x = 1 / 2 := by
  simp [fitness, contribution, tiedTables]

/-- Both one-bit neighbors tie, so the weak maximality predicate holds. -/
theorem tied_local (x : Config 1) :
    IsOneBitLocalMax (fitness singletonTopology tiedTables) x := by
  simp [IsOneBitLocalMax, tied_fitness]

/-- Exact rational evaluation of a two-coordinate separable landscape. -/
theorem separateBest_fitness :
    fitness separateTopology separateTables separateBest = 3 / 4 := by
  norm_num [fitness_K_zero, separateTables, separateBest, Fin.sum_univ_succ]

/-- Exhaust the two possible flips using the computable rational evaluator. -/
theorem separateBest_local :
    IsOneBitLocalMax (fitness separateTopology separateTables) separateBest := by
  norm_num [IsOneBitLocalMax, Fin.forall_fin_succ, fitness, contribution, extract,
    separateTables, separateBest, separateTopology, OrgLib.NK.flip, Function.update,
    Fin.sum_univ_succ]

/-- Transporting scope order and tables together preserves this full-arity landscape. -/
theorem full_reindexed_fitness (x : Config 3) :
    fitness (fullTopology.reindex swapInteractions swapInteractions_fix_zero)
      (reindexTables asymmetricTables swapInteractions) x =
      fitness fullTopology asymmetricTables x :=
  fitness_reindex_slots fullTopology asymmetricTables
    swapInteractions swapInteractions_fix_zero x

/-- Slot weights produce a nonintegral exact rational average. -/
theorem full_fitness :
    fitness fullTopology asymmetricTables fullState = 8 / 3 := by
  norm_num [fitness, contribution, extract, fullTopology, asymmetricTables,
    fullState, Fin.sum_univ_succ, Equiv.swap_apply_def, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (0 : Fin 3) ≠ 2 by decide]

/-- Changing scope order without transporting the tables changes this average. -/
theorem full_scope_only_fitness :
    fitness (fullTopology.reindex swapInteractions swapInteractions_fix_zero)
      asymmetricTables fullState = 4 := by
  norm_num [fitness, contribution, extract, fullTopology, asymmetricTables,
    fullState, Fin.sum_univ_succ, Equiv.swap_apply_def, Topology.reindex, swapInteractions,
    show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (0 : Fin 3) ≠ 2 by decide]

/-- The singleton tables satisfy the hypothesis of the core bounds theorem. -/
theorem tiedTables_bounded (i : Fin 1) (w : LocalWord 0) :
    tiedTables i w ∈ Set.Icc (0 : ℚ) 1 := by
  norm_num [tiedTables]

/-- Apply T02 to the smallest valid topology. -/
theorem tied_bounded (x : Config 1) :
    fitness singletonTopology tiedTables x ∈ Set.Icc (0 : ℚ) 1 :=
  fitness_mem_Icc singletonTopology tiedTables tiedTables_bounded x

/-- T04 includes every tied singleton state as a global maximum. -/
theorem tied_global (x : Config 1) :
    IsMaxOn (fitness singletonTopology tiedTables) Set.univ x :=
  (isOneBitLocalMax_iff_isMaxOn_K_zero singletonTopology tiedTables x).mp (tied_local x)

/-- Turn the checked two-flip comparison into global maximality through T04. -/
theorem separateBest_global :
    IsMaxOn (fitness separateTopology separateTables) Set.univ separateBest :=
  (isOneBitLocalMax_iff_isMaxOn_K_zero separateTopology separateTables separateBest).mp
    separateBest_local

/-- The transported tables retain the original exact rational value. -/
theorem full_reindexed_value :
    fitness (fullTopology.reindex swapInteractions swapInteractions_fix_zero)
      (reindexTables asymmetricTables swapInteractions) fullState = 8 / 3 :=
  (full_reindexed_fitness fullState).trans full_fitness

/--
info: [8 / 3, 8 / 3, 4]
-/
#guard_msgs in
#eval [
  fitness fullTopology asymmetricTables fullState,
  fitness (fullTopology.reindex swapInteractions swapInteractions_fix_zero)
    (reindexTables asymmetricTables swapInteractions) fullState,
  fitness (fullTopology.reindex swapInteractions swapInteractions_fix_zero)
    asymmetricTables fullState]

end OrgLibExamples.NK
