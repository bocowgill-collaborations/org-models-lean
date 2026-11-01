import OrgLib.NK.SharedCyclic.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Zero-interaction properties of shared cyclic landscapes

At `K = 0`, one shared table makes sharedCyclic fitness depend only on the number of
true bits. Strict preference between its two values determines the maximizing
configuration; equal values make every state maximal. These statements concern
raw quality, with no sampling or search assumptions.
-/

namespace OrgLib.NK.SharedCyclic

open OrgLib.NK
open scoped BigOperators

variable {N : ℕ} {R : Type*}

/-- The number of true bits in a binary configuration. -/
def hammingWeight (x : Config N) : ℕ :=
  (Finset.univ.filter fun i ↦ x i = true).card

/-- The number of true bits cannot exceed the number of loci. -/
theorem hammingWeight_le (x : Config N) : hammingWeight x ≤ N := by
  simpa [hammingWeight] using
    (Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun i ↦ x i = true))

/-- The remaining loci are exactly the false bits. -/
theorem card_false_eq_sub_hammingWeight (x : Config N) :
    (Finset.univ.filter fun i ↦ x i = false).card = N - hammingWeight x := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i : Fin N ↦ x i = true)
  simpa [hammingWeight, Bool.not_eq_true] using
    (Nat.eq_sub_of_add_eq (by simpa [Nat.add_comm] using h))

/-- T09: a shared zero-interaction landscape depends only on its true-bit count. -/
theorem sharedCyclic_K_zero_hamming [Field R] [CharZero R]
    (hN : 0 < N) (φ : LocalWord 0 → R) (x : Config N) :
    sharedCyclic hN φ x =
      (((N - hammingWeight x : ℕ) : R) * φ (fun _ ↦ false) +
        (hammingWeight x : R) * φ (fun _ ↦ true)) / (N : R) := by
  rw [sharedCyclic, fitness_K_zero]
  congr 1
  rw [← card_false_eq_sub_hammingWeight]
  have he (i : Fin N) : φ (fun _ ↦ x i) =
      if x i = true then φ (fun _ ↦ true) else φ (fun _ ↦ false) := by
    cases x i <;> simp
  simp_rw [sharedTables, he]
  simp [Finset.sum_ite, hammingWeight, Bool.not_eq_true, add_comm]

/-- T10: if true has strictly higher shared quality, precisely the all-true state is maximal. -/
theorem sharedCyclic_isMaxOn_iff_all_true
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hN : 0 < N) (φ : LocalWord 0 → R) (x : Config N)
    (hφ : φ (fun _ ↦ false) < φ (fun _ ↦ true)) :
    IsMaxOn (sharedCyclic hN φ) Set.univ x ↔ ∀ i, x i = true := by
  rw [sharedCyclic, ← isOneBitLocalMax_iff_isMaxOn_K_zero]
  simp only [IsOneBitLocalMax, fitness_flip_le_iff_K_zero, sharedTables]
  refine forall_congr' (fun i ↦ ?_)
  cases hi : x i
  all_goals simp [not_le_of_gt hφ, le_of_lt hφ]

/-- T10: if false has strictly higher shared quality, precisely the all-false state is maximal. -/
theorem sharedCyclic_isMaxOn_iff_all_false
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hN : 0 < N) (φ : LocalWord 0 → R) (x : Config N)
    (hφ : φ (fun _ ↦ true) < φ (fun _ ↦ false)) :
    IsMaxOn (sharedCyclic hN φ) Set.univ x ↔ ∀ i, x i = false := by
  rw [sharedCyclic, ← isOneBitLocalMax_iff_isMaxOn_K_zero]
  simp only [IsOneBitLocalMax, fitness_flip_le_iff_K_zero, sharedTables]
  refine forall_congr' (fun i ↦ ?_)
  cases hi : x i
  all_goals simp [not_le_of_gt hφ, le_of_lt hφ]

/-- T10: tied shared values make every configuration globally maximal. -/
theorem sharedCyclic_isMaxOn_of_eq [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hN : 0 < N) (φ : LocalWord 0 → R) (x : Config N)
    (hφ : φ (fun _ ↦ false) = φ (fun _ ↦ true)) :
    IsMaxOn (sharedCyclic hN φ) Set.univ x := by
  rw [sharedCyclic, ← isOneBitLocalMax_iff_isMaxOn_K_zero]
  simp only [IsOneBitLocalMax, fitness_flip_le_iff_K_zero, sharedTables]
  intro i
  cases x i
  all_goals simp [hφ]

end OrgLib.NK.SharedCyclic
