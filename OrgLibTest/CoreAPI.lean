import OrgLib

/-!
# Canonical NK public interface checks

These applications pin the statements under the public import. In particular,
locality requires no arithmetic structure, and K=0 maximality requires no table bounds.
-/

namespace OrgLibTest

open OrgLib.NK
open scoped BigOperators

variable {N K : ℕ} {R : Type*}

example (T : Topology N K) (c : Tables N K R) (x y : Config N) (i : Fin N)
    (h : ∀ j, x (T.scope i j) = y (T.scope i j)) :
    contribution T c x i = contribution T c y i :=
  contribution_eq_of_agree_on_scope T c x y i h

example [Field R] [CharZero R] (T : Topology N 0) (c : Tables N 0 R) (x : Config N) :
    fitness T c x = (∑ i, c i (fun _ ↦ x i)) / (N : R) :=
  fitness_K_zero T c x

example [Field R] [CharZero R] (T : Topology N K) (c : Tables N K R)
    (σ : Fin N → Equiv.Perm (Fin (K + 1))) (hσ : ∀ i, σ i 0 = 0) (x : Config N) :
    fitness (T.reindex σ hσ) (reindexTables c σ) x = fitness T c x :=
  fitness_reindex_slots T c σ hσ x

example [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (T : Topology N K) (c : Tables N K R)
    (hc : ∀ i w, c i w ∈ Set.Icc (0 : R) 1) (x : Config N) :
    fitness T c x ∈ Set.Icc (0 : R) 1 :=
  fitness_mem_Icc T c hc x

example [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (T : Topology N 0) (c : Tables N 0 R) (x : Config N) :
    IsOneBitLocalMax (fitness T c) x ↔ IsMaxOn (fitness T c) Set.univ x :=
  isOneBitLocalMax_iff_isMaxOn_K_zero T c x

end OrgLibTest
