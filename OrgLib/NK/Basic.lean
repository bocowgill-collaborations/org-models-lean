import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Basic

/-!
# Canonical deterministic NK landscapes

An NK landscape has binary configurations, an ordered injective scope of `K + 1`
coordinates at each locus, and a local contribution table for each locus. Slot zero is
the focal locus. Fitness is the average of the local contributions.

This proposed canonical representation follows the exposition in Felipe A. Csaszar,
*A note on how NK landscapes work* (2018), pp. 2–3 (DOI: 10.1186/s41469-018-0039-0).
The tables are supplied deterministic data; no distribution or independence assumption
is part of this core. Local slot permutations act contravariantly on tables, preserving
the resulting landscape.
-/

namespace OrgLib.NK

open scoped BigOperators

/-- A binary configuration on `N` loci. -/
abbrev Config (N : ℕ) := Fin N → Bool

/-- A local binary word with the focal slot followed by `K` interaction slots. -/
abbrev LocalWord (K : ℕ) := Fin (K + 1) → Bool

/-- A separate local contribution table at each locus. -/
abbrev Tables (N K : ℕ) (R : Type*) := Fin N → LocalWord K → R

/-- Ordered, duplicate-free NK scopes with each focal locus in slot zero. -/
@[ext]
structure Topology (N K : ℕ) where
  /-- The number of other interacting loci is strictly smaller than `N`. -/
  k_lt_n : K < N
  /-- The ordered scope at each locus, including the focal locus. -/
  scope : Fin N → (Fin (K + 1) ↪ Fin N)
  /-- Slot zero is the focal locus. -/
  self : ∀ i, scope i 0 = i

variable {N K : ℕ} {R : Type*}

/-- Valid NK topologies necessarily have at least one locus. -/
theorem Topology.n_pos (T : Topology N K) : 0 < N :=
  Nat.zero_lt_of_lt T.k_lt_n

/-- Read the configuration in the order specified by the scope at a locus. -/
def extract (T : Topology N K) (x : Config N) (i : Fin N) : LocalWord K :=
  fun j ↦ x (T.scope i j)

/-- Evaluate one local contribution, with no algebraic assumptions on its values. -/
def contribution (T : Topology N K) (c : Tables N K R) (x : Config N) (i : Fin N) : R :=
  c i (extract T x i)

/-- Raw NK fitness, the average of the supplied local contributions. -/
def fitness [Field R] [CharZero R]
    (T : Topology N K) (c : Tables N K R) (x : Config N) : R :=
  (∑ i, contribution T c x i) / (N : R)

/-- Toggle exactly the indicated coordinate of a binary configuration. -/
def flip (x : Config N) (i : Fin N) : Config N :=
  Function.update x i (!x i)

/-- Weak local maximality with respect to the one-bit-flip neighborhood. -/
def IsOneBitLocalMax [Preorder R] (F : Config N → R) (x : Config N) : Prop :=
  ∀ i, F (flip x i) ≤ F x

/-- T01: a contribution depends only on the coordinates in its scope. -/
theorem contribution_eq_of_agree_on_scope
    (T : Topology N K) (c : Tables N K R) (x y : Config N) (i : Fin N)
    (h : ∀ j, x (T.scope i j) = y (T.scope i j)) :
    contribution T c x i = contribution T c y i :=
  congrArg (c i) (funext h)

/-- With no interactions, the local word is the focal bit alone. -/
@[simp]
theorem extract_K_zero (T : Topology N 0) (x : Config N) (i : Fin N) :
    extract T x i = fun _ ↦ x i := by
  simp [extract, funext_iff, Fin.eq_zero, T.self]

/-- T03: with no interactions, fitness separates into one term for each focal bit. -/
theorem fitness_K_zero [Field R] [CharZero R]
    (T : Topology N 0) (c : Tables N 0 R) (x : Config N) :
    fitness T c x = (∑ i, c i (fun _ ↦ x i)) / (N : R) := by
  simp [fitness, contribution]

/-- Reorder the local slots, keeping the focal slot fixed. -/
def Topology.reindex (T : Topology N K)
    (σ : Fin N → Equiv.Perm (Fin (K + 1))) (hσ : ∀ i, σ i 0 = 0) :
    Topology N K where
  k_lt_n := T.k_lt_n
  scope i := (σ i).toEmbedding.trans (T.scope i)
  self i := by simp [hσ, T.self]

/-- Reindex table arguments inversely to a permutation of the topology's local slots. -/
def reindexTables (c : Tables N K R)
    (σ : Fin N → Equiv.Perm (Fin (K + 1))) : Tables N K R :=
  fun i w ↦ c i (fun j ↦ w ((σ i).symm j))

/-- Reindexing a scope composes each extracted word with the slot permutation. -/
@[simp]
theorem extract_reindex (T : Topology N K)
    (σ : Fin N → Equiv.Perm (Fin (K + 1))) (hσ : ∀ i, σ i 0 = 0)
    (x : Config N) (i : Fin N) :
    extract (T.reindex σ hσ) x i = fun j ↦ extract T x i (σ i j) :=
  rfl

/-- Matching topology and table reindexing preserves each local contribution. -/
@[simp]
theorem contribution_reindex_slots (T : Topology N K) (c : Tables N K R)
    (σ : Fin N → Equiv.Perm (Fin (K + 1))) (hσ : ∀ i, σ i 0 = 0)
    (x : Config N) (i : Fin N) :
    contribution (T.reindex σ hσ) (reindexTables c σ) x i = contribution T c x i := by
  simp only [contribution, reindexTables, extract_reindex, Equiv.apply_symm_apply]

/-- T05: relabeling local slots and their table inputs preserves the fitness landscape. -/
@[simp]
theorem fitness_reindex_slots [Field R] [CharZero R]
    (T : Topology N K) (c : Tables N K R)
    (σ : Fin N → Equiv.Perm (Fin (K + 1))) (hσ : ∀ i, σ i 0 = 0)
    (x : Config N) :
    fitness (T.reindex σ hσ) (reindexTables c σ) x = fitness T c x := by
  simp [fitness]

/-- The identity slot permutation leaves a topology unchanged. -/
@[simp]
theorem Topology.reindex_refl (T : Topology N K) :
    T.reindex (fun _ ↦ Equiv.refl _) (fun _ ↦ rfl) = T :=
  rfl

/-- The identity slot permutation leaves the tables unchanged. -/
@[simp]
theorem reindexTables_refl (c : Tables N K R) :
    reindexTables c (fun _ ↦ Equiv.refl _) = c :=
  rfl

/-- Successive slot reindexings compose as functions: first `τ`, then `σ` inside a scope. -/
theorem Topology.reindex_reindex (T : Topology N K)
    (σ τ : Fin N → Equiv.Perm (Fin (K + 1)))
    (hσ : ∀ i, σ i 0 = 0) (hτ : ∀ i, τ i 0 = 0) :
    (T.reindex σ hσ).reindex τ hτ =
      T.reindex (fun i ↦ (τ i).trans (σ i))
        (fun i ↦ (congrArg (σ i) (hτ i)).trans (hσ i)) :=
  rfl

/-- Table reindexing has the same composition order as topology reindexing. -/
theorem reindexTables_reindex (c : Tables N K R)
    (σ τ : Fin N → Equiv.Perm (Fin (K + 1))) :
    reindexTables (reindexTables c σ) τ =
      reindexTables c (fun i ↦ (τ i).trans (σ i)) :=
  rfl

end OrgLib.NK
