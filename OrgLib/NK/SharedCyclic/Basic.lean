import OrgLib.NK.Cyclic
import OrgLib.NK.Encoding
import OrgLib.NK.Properties

/-!
# Shared cyclic landscapes and a locus-specific alternative

Scott C. Ganz, *Adaptive Rationality, Garbage Cans, and the Policy Process*, §2.2,
uses forward cyclic scopes and one shared contribution table
(DOI: 10.1108/S0733-558X20210000076004).
The supplied `RSO_replication.R:91–108` implements the same raw-quality
construction: duplicate the configuration string, read a focal-first window, and
look up one shared vector using the MSB-first binary address plus one.

Both constructions below reuse canonical NK fitness. The locus-specific alternative
holds topology and state meanings fixed while accepting a table at each locus.
It imposes no stochastic independence or inequality among those tables.
-/

namespace OrgLib.NK.SharedCyclic

open OrgLib.NK
open scoped BigOperators

variable {N K : ℕ} {R : Type*}

/-- One shared contribution table evaluated on forward cyclic scopes. -/
def sharedCyclic [Field R] [CharZero R] (hKN : K < N) (φ : LocalWord K → R) : Config N → R :=
  fitness (cyclicTopology hKN) (sharedTables φ)

/-- Controlled deterministic alternative: the same cyclic scopes with a table at each locus. -/
def locusSpecificCyclic [Field R] [CharZero R]
    (hKN : K < N) (c : Tables N K R) : Config N → R :=
  fitness (cyclicTopology hKN) c

/-- The locus-specific family includes every sharedCyclic landscape by using shared tables. -/
@[simp]
theorem locusSpecificCyclic_sharedTables [Field R] [CharZero R]
    (hKN : K < N) (φ : LocalWord K → R) :
    locusSpecificCyclic hKN (sharedTables φ) = sharedCyclic hKN φ :=
  rfl

/-- Interpret a single address-indexed vector using the canonical binary codec. -/
def sharedCyclicFromEntries [Field R] [CharZero R]
    (hKN : K < N) (entries : Fin (2 ^ (K + 1)) → R) : Config N → R :=
  sharedCyclic hKN (fun w ↦ entries (encode w))

/-- Shared canonical fitness equals the explicit forward-window average. -/
theorem sharedCyclic_fitness_eq [Field R] [CharZero R]
    (hKN : K < N) (φ : LocalWord K → R) (x : Config N) :
    sharedCyclic hKN φ x =
      (∑ i : Fin N, φ (fun j : Fin (K + 1) ↦
        x ⟨(i.val + j.val) % N, Nat.mod_lt _ (Nat.zero_lt_of_lt hKN)⟩)) / (N : R) :=
  rfl

/-- The active R-shaped formula uses the single indexed vector and divides each term by N. -/
theorem sharedCyclic_entries_fitness_eq [Field R] [CharZero R]
    (hKN : K < N) (entries : Fin (2 ^ (K + 1)) → R) (x : Config N) :
    sharedCyclicFromEntries hKN entries x =
      ∑ i : Fin N, entries (encode (fun j : Fin (K + 1) ↦
        x ⟨(i.val + j.val) % N, Nat.mod_lt _ (Nat.zero_lt_of_lt hKN)⟩)) / (N : R) := by
  simp only [sharedCyclicFromEntries, sharedCyclic_fitness_eq, Finset.sum_div]

/-- T08: every rotation preserves sharedCyclic quality because its cyclic table is shared. -/
theorem sharedCyclic_fitness_rotate [Field R] [CharZero R]
    (hKN : K < N) (φ : LocalWord K → R) (x : Config N) (r : Fin N) :
    sharedCyclic hKN φ (rotate r x) = sharedCyclic hKN φ x :=
  fitness_shared_rotate hKN φ x r

/-- Bounded shared tables inherit the canonical NK unit-interval bound. -/
theorem sharedCyclic_fitness_mem_Icc [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hKN : K < N) (φ : LocalWord K → R)
    (hφ : ∀ w, φ w ∈ Set.Icc (0 : R) 1) (x : Config N) :
    sharedCyclic hKN φ x ∈ Set.Icc (0 : R) 1 :=
  fitness_mem_Icc (cyclicTopology hKN) (sharedTables φ) (fun _ w ↦ hφ w) x

/-- Bounded locus-specific tables inherit the same canonical bound on the same scopes. -/
theorem locusSpecificCyclic_fitness_mem_Icc
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hKN : K < N) (c : Tables N K R)
    (hc : ∀ i w, c i w ∈ Set.Icc (0 : R) 1) (x : Config N) :
    locusSpecificCyclic hKN c x ∈ Set.Icc (0 : R) 1 :=
  fitness_mem_Icc (cyclicTopology hKN) c hc x

end OrgLib.NK.SharedCyclic
