import OrgLib

/-!
# Shared cyclic public interface checks

These applications pin the unrestricted deterministic statements: valid cyclic
scopes, shared-table symmetry, exact evaluation, and the controlled inclusion.
-/

namespace OrgLibTest.SharedCyclic

open OrgLib.NK
open OrgLib.NK.SharedCyclic
open scoped BigOperators

variable {N K : ℕ} {R : Type*}

example (hKN : K < N) (i : Fin N) (j : Fin (K + 1)) :
    ((cyclicTopology hKN).scope i j).val = (i.val + j.val) % N :=
  cyclicTopology_scope_val hKN i j

example (r : Fin N) (x : Config N) (i : Fin N) :
    rotate r x i = x ⟨(i.val + r.val) % N, Nat.mod_lt _ (Nat.zero_lt_of_lt i.is_lt)⟩ :=
  rotate_apply_mod r x i

example [Field R] [CharZero R] (hKN : K < N) (φ : LocalWord K → R) :
    locusSpecificCyclic hKN (sharedTables φ) = sharedCyclic hKN φ :=
  locusSpecificCyclic_sharedTables hKN φ

example [Field R] [CharZero R] (hKN : K < N) (φ : LocalWord K → R) (x : Config N) :
    sharedCyclic hKN φ x =
      (∑ i : Fin N, φ (fun j : Fin (K + 1) ↦
        x ⟨(i.val + j.val) % N, Nat.mod_lt _ (Nat.zero_lt_of_lt hKN)⟩)) / (N : R) :=
  sharedCyclic_fitness_eq hKN φ x

example [Field R] [CharZero R] (hKN : K < N) (φ : LocalWord K → R)
    (x : Config N) (r : Fin N) :
    sharedCyclic hKN φ (rotate r x) = sharedCyclic hKN φ x :=
  sharedCyclic_fitness_rotate hKN φ x r

example [Field R] [CharZero R] (hKN : K < N)
    (entries : Fin (2 ^ (K + 1)) → R) (x : Config N) :
    sharedCyclicFromEntries hKN entries x =
      ∑ i : Fin N, entries (encode (fun j : Fin (K + 1) ↦
        x ⟨(i.val + j.val) % N, Nat.mod_lt _ (Nat.zero_lt_of_lt hKN)⟩)) / (N : R) :=
  sharedCyclic_entries_fitness_eq hKN entries x

example [Field R] [CharZero R] (hN : 0 < N) (φ : LocalWord 0 → R) (x : Config N) :
    sharedCyclic hN φ x =
      (((N - hammingWeight x : ℕ) : R) * φ (fun _ ↦ false) +
        (hammingWeight x : R) * φ (fun _ ↦ true)) / (N : R) :=
  sharedCyclic_K_zero_hamming hN φ x

example [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hN : 0 < N) (φ : LocalWord 0 → R) (x : Config N)
    (hφ : φ (fun _ ↦ false) < φ (fun _ ↦ true)) :
    IsMaxOn (sharedCyclic hN φ) Set.univ x ↔ ∀ i, x i = true :=
  sharedCyclic_isMaxOn_iff_all_true hN φ x hφ

example [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hN : 0 < N) (φ : LocalWord 0 → R) (x : Config N)
    (hφ : φ (fun _ ↦ true) < φ (fun _ ↦ false)) :
    IsMaxOn (sharedCyclic hN φ) Set.univ x ↔ ∀ i, x i = false :=
  sharedCyclic_isMaxOn_iff_all_false hN φ x hφ

example [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hN : 0 < N) (φ : LocalWord 0 → R) (x : Config N)
    (hφ : φ (fun _ ↦ false) = φ (fun _ ↦ true)) :
    IsMaxOn (sharedCyclic hN φ) Set.univ x :=
  sharedCyclic_isMaxOn_of_eq hN φ x hφ

example : ¬∃ φ : LocalWord 0 → ℚ, ∀ x,
    sharedCyclic (by decide : 0 < 2) φ x =
      locusSpecificCyclic (by decide : 0 < 2) witnessTables x :=
  witness_no_shared_representation

end OrgLibTest.SharedCyclic
