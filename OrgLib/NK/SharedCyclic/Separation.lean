import OrgLib.NK.SharedCyclic.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Fixed-label separation of shared and locus-specific cyclic landscapes

At `N = 2`, `K = 0`, a bounded rational locus-specific table family gives fitness
one at the labeled configuration `01` and zero at `10`. Rotation exchanges those
states, whereas every shared cyclic landscape is invariant under rotation.
Thus no shared table, even an unbounded one, represents this landscape on the same
labeled configurations.

This is a deterministic representation restriction. Complementing the first bit
turns this particular witness into a shared additive landscape; no obstruction to
arbitrary state recodings or stochastic-law equality is asserted here.
-/

namespace OrgLib.NK.SharedCyclic

open OrgLib.NK

/-- The labeled state with coordinate zero false and coordinate one true. -/
def state01 : Config 2 := fun i ↦ i == 1

/-- The labeled state with coordinate zero true and coordinate one false. -/
def state10 : Config 2 := fun i ↦ i == 0

/-- The first locus prefers false and the second prefers true, with values zero and one. -/
def witnessTables : Tables 2 0 ℚ :=
  fun i w ↦ if i = 0 then (if w 0 then 0 else 1) else (if w 0 then 1 else 0)

/-- Every entry of the separating family belongs to the canonical unit interval. -/
theorem witnessTables_bounded (i : Fin 2) (w : LocalWord 0) :
    witnessTables i w ∈ Set.Icc (0 : ℚ) 1 := by
  simp only [witnessTables]
  split_ifs <;> norm_num

/-- The prescribed witness has fitness one at the labeled state `01`. -/
theorem witness_fitness_state01 :
    locusSpecificCyclic (by decide : 0 < 2) witnessTables state01 = 1 := by
  rw [locusSpecificCyclic, fitness_K_zero, Fin.sum_univ_two]
  norm_num [witnessTables, state01]

/-- The prescribed witness has fitness zero at the labeled state `10`. -/
theorem witness_fitness_state10 :
    locusSpecificCyclic (by decide : 0 < 2) witnessTables state10 = 0 := by
  rw [locusSpecificCyclic, fitness_K_zero, Fin.sum_univ_two]
  norm_num [witnessTables, state10]

/-- A one-coordinate rotation exchanges the two labeled states used in the witness. -/
theorem rotate_state01 : rotate (1 : Fin 2) state01 = state10 := by
  decide

/-- Every shared sharedCyclic table assigns equal quality to the two rotated labeled states. -/
theorem sharedCyclic_state01_eq_state10 {R : Type*} [Field R] [CharZero R]
    (φ : LocalWord 0 → R) :
    sharedCyclic (by decide : 0 < 2) φ state01 = sharedCyclic (by decide : 0 < 2) φ state10 := by
  simpa only [rotate_state01] using
    (sharedCyclic_fitness_rotate (by decide : 0 < 2) φ state01 (1 : Fin 2)).symm

/-- T11: the bounded witness has no shared-table representation at the fixed labeled states. -/
theorem witness_no_shared_representation :
    ¬∃ φ : LocalWord 0 → ℚ, ∀ x,
      sharedCyclic (by decide : 0 < 2) φ x =
        locusSpecificCyclic (by decide : 0 < 2) witnessTables x := by
  rintro ⟨φ, hφ⟩
  have h := (hφ state01).symm.trans ((sharedCyclic_state01_eq_state10 φ).trans (hφ state10))
  simp [witness_fitness_state01, witness_fitness_state10] at h

end OrgLib.NK.SharedCyclic
