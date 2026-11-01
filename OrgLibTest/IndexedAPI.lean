import OrgLib

/-!
# Public interface contract

The codec has no topology or numeric hypotheses. The adapter preserves the supplied
neighbor order, and the exact source-shaped formula divides within each summand.
-/

namespace OrgLibTest

open OrgLib.NK
open scoped BigOperators

variable {m N K : ℕ} {R : Type*}

example (q : Fin (2 ^ m)) : encode (decode q) = q := encode_decode q

example (w : Fin m → Bool) : decode (encode w) = w := decode_encode w

example (entries : TableEntries N K R) (i : Fin N) (w : LocalWord K) :
    tablesFromEntries entries i w = entries i (encode w) :=
  lookup_eq entries i w

example (w : Fin m → Bool) : rIndex w = (encode w).val + 1 := rfl

example (w : Fin m → Bool) :
    (encode w).val = ∑ j : Fin m, (if w j then 1 else 0) * 2 ^ (m - 1 - j.val) :=
  encode_val w

example (entries : TableEntries N K R) (i : Fin N) (w : LocalWord K) :
    tablesFromEntries entries i w = entries i ⟨rIndex w - 1, by simp [rIndex]⟩ :=
  lookup_rIndex entries i w

example [Field R] [CharZero R]
    (hKN : K < N) (neighbors : Fin N → (Fin K ↪ Fin N))
    (hne : ∀ i j, neighbors i j ≠ i) (entries : TableEntries N K R) (x : Config N) :
    fitness (Topology.ofNeighbors hKN neighbors hne) (tablesFromEntries entries) x =
      ∑ i, entries i (encode (Fin.cases (x i) (fun j ↦ x (neighbors i j)))) / (N : R) :=
  fitness_eq_indexedAverage hKN neighbors hne entries x

example [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hKN : K < N) (neighbors : Fin N → (Fin K ↪ Fin N))
    (hne : ∀ i j, neighbors i j ≠ i) (entries : TableEntries N K R)
    (he : ∀ i q, entries i q ∈ Set.Icc (0 : R) 1) (x : Config N) :
    fitness (Topology.ofNeighbors hKN neighbors hne) (tablesFromEntries entries) x ∈
      Set.Icc (0 : R) 1 :=
  indexed_fitness_mem_Icc hKN neighbors hne entries he x

example [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hN : 0 < N) (neighbors : Fin N → (Fin 0 ↪ Fin N))
    (hne : ∀ i j, neighbors i j ≠ i) (entries : TableEntries N 0 R) (x : Config N) :
    IsOneBitLocalMax
        (fitness (Topology.ofNeighbors hN neighbors hne) (tablesFromEntries entries)) x ↔
      IsMaxOn (fitness (Topology.ofNeighbors hN neighbors hne)
        (tablesFromEntries entries)) Set.univ x :=
  indexed_isOneBitLocalMax_iff_isMaxOn_K_zero
    hN neighbors hne entries x

end OrgLibTest
