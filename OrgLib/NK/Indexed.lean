import OrgLib.NK.Properties
import OrgLib.NK.Encoding
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# Indexed tables and ordered neighborhoods

Scott C. Ganz, *Conflict, Chaos, and the Art of Institutional Design*, §3.1,
uses a canonical NK quality landscape (DOI: 10.1287/orsc.2023.1662).
The supplied `gcm_model.R:72–104` evaluates focal-first local words using one table
per locus. This adapter constructs the canonical NK topology from supplied distinct,
nonfocal neighbors. It preserves their order; sorting belongs to the source generator.

The correspondence concerns exact raw quality for fixed valid scopes and tables.
Sampling, floating-point execution, weighted utilities, and search are separate.
-/

namespace OrgLib.NK

open scoped BigOperators

variable {N K : ℕ} {R : Type*}

/-- Prepend the focal locus to the supplied ordered nonfocal neighbors. -/
def Topology.ofNeighbors (hKN : K < N) (neighbors : Fin N → (Fin K ↪ Fin N))
    (hne : ∀ i j, neighbors i j ≠ i) : Topology N K where
  k_lt_n := hKN
  scope i := Fin.Embedding.cons (neighbors i) (fun ⟨j, hj⟩ ↦ hne i j hj)
  self := fun _ ↦ rfl

/-- The first scope slot is exactly the focal locus. -/
@[simp]
theorem Topology.ofNeighbors_scope_zero (hKN : K < N) (neighbors : Fin N → (Fin K ↪ Fin N))
    (hne : ∀ i j, neighbors i j ≠ i) (i : Fin N) :
    (Topology.ofNeighbors hKN neighbors hne).scope i 0 = i :=
  rfl

/-- Successor slots read neighbors in precisely their supplied order. -/
@[simp]
theorem Topology.ofNeighbors_scope_succ (hKN : K < N) (neighbors : Fin N → (Fin K ↪ Fin N))
    (hne : ∀ i j, neighbors i j ≠ i) (i : Fin N) (j : Fin K) :
    (Topology.ofNeighbors hKN neighbors hne).scope i j.succ = neighbors i j :=
  rfl

/-- The local word is the focal bit followed by the supplied neighbor bits. -/
@[simp]
theorem extract_ofNeighbors (hKN : K < N) (neighbors : Fin N → (Fin K ↪ Fin N))
    (hne : ∀ i j, neighbors i j ≠ i) (x : Config N) (i : Fin N) :
    extract (Topology.ofNeighbors hKN neighbors hne) x i =
      Fin.cases (x i) (fun j ↦ x (neighbors i j)) := by
  funext j
  cases j using Fin.cases <;> rfl

/--
T06: canonical fitness equals the exact focal-first, address-indexed sum in the active
OrgSci evaluator. Division is performed inside the sum, as at `gcm_model.R:76`.
-/
theorem fitness_eq_indexedAverage [Field R] [CharZero R]
    (hKN : K < N) (neighbors : Fin N → (Fin K ↪ Fin N))
    (hne : ∀ i j, neighbors i j ≠ i) (entries : TableEntries N K R) (x : Config N) :
    fitness (Topology.ofNeighbors hKN neighbors hne) (tablesFromEntries entries) x =
      ∑ i, entries i (encode (Fin.cases (x i) (fun j ↦ x (neighbors i j)))) / (N : R) := by
  simp [fitness, contribution, tablesFromEntries, Finset.sum_div]

/-- Bounded OrgSci entries inherit the canonical NK fitness bounds. -/
theorem indexed_fitness_mem_Icc
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hKN : K < N) (neighbors : Fin N → (Fin K ↪ Fin N))
    (hne : ∀ i j, neighbors i j ≠ i) (entries : TableEntries N K R)
    (he : ∀ i q, entries i q ∈ Set.Icc (0 : R) 1) (x : Config N) :
    fitness (Topology.ofNeighbors hKN neighbors hne) (tablesFromEntries entries) x ∈
      Set.Icc (0 : R) 1 :=
  fitness_mem_Icc (Topology.ofNeighbors hKN neighbors hne) (tablesFromEntries entries)
    (fun i w ↦ he i (encode w)) x

/-- At zero interactions, OrgSci weak one-bit maxima inherit global maximality, including ties. -/
theorem indexed_isOneBitLocalMax_iff_isMaxOn_K_zero
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hN : 0 < N) (neighbors : Fin N → (Fin 0 ↪ Fin N))
    (hne : ∀ i j, neighbors i j ≠ i) (entries : TableEntries N 0 R) (x : Config N) :
    IsOneBitLocalMax
        (fitness (Topology.ofNeighbors hN neighbors hne) (tablesFromEntries entries)) x ↔
      IsMaxOn (fitness (Topology.ofNeighbors hN neighbors hne) (tablesFromEntries entries))
        Set.univ x :=
  isOneBitLocalMax_iff_isMaxOn_K_zero (Topology.ofNeighbors hN neighbors hne)
    (tablesFromEntries entries) x

end OrgLib.NK
