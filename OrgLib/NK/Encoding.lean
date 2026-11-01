import OrgLib.NK.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Shared fixed-width binary encoding

The leftmost bit is most significant. Reversing the slot order converts mathlib's
least-significant-first `finFunctionFinEquiv` into this convention. Both directions
are computable, preserve leading zeros, and include the empty word at length zero.

For the supplied OrgSci source, math slot zero corresponds to R vector index one;
the local table lookup uses the encoded value plus one. The mathematical codec has
no machine-width bound. Literal R evaluator correspondence instead assumes integer
`1 ≤ N ≤ 31`, `0 ≤ K < N`, valid supplied scopes and finite correctly sized tables.
-/

namespace OrgLib.NK

open scoped BigOperators

/-- Constructive equivalence from MSB-first binary words to fixed-width addresses. -/
def wordEquiv (m : ℕ) : (Fin m → Bool) ≃ Fin (2 ^ m) :=
  (Equiv.arrowCongr Fin.revPerm finTwoEquiv.symm).trans finFunctionFinEquiv

/-- Interpret a fixed-width word as an address, with its first bit most significant. -/
def encode {m : ℕ} (w : Fin m → Bool) : Fin (2 ^ m) :=
  wordEquiv m w

/-- Decode an address to a fixed-width MSB-first word, retaining leading zeros. -/
def decode {m : ℕ} (q : Fin (2 ^ m)) : Fin m → Bool :=
  (wordEquiv m).symm q

/-- Encoding a decoded address returns that address at every word length. -/
@[simp]
theorem encode_decode {m : ℕ} (q : Fin (2 ^ m)) : encode (decode q) = q :=
  (wordEquiv m).apply_symm_apply q

/-- Decoding an encoded word returns that word, including the empty word. -/
@[simp]
theorem decode_encode {m : ℕ} (w : Fin m → Bool) : decode (encode w) = w :=
  (wordEquiv m).symm_apply_apply w

/-- The MSB-first address is the corresponding positional binary sum. -/
theorem encode_val {m : ℕ} (w : Fin m → Bool) :
    (encode w).val = ∑ j : Fin m, (if w j then 1 else 0) * 2 ^ (m - 1 - j.val) := by
  rw [encode, wordEquiv, Equiv.trans_apply, finFunctionFinEquiv_apply]
  rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin m ↦
    ((Equiv.arrowCongr Fin.revPerm finTwoEquiv.symm) w i).val * 2 ^ i.val)]
  simp [Equiv.arrowCongr, Fin.revPerm, finTwoEquiv, Nat.sub_sub,
    Nat.add_comm, Bool.cond_eq_ite, apply_ite]

/-- A locus-specific table represented by zero-based binary addresses. -/
abbrev TableEntries (N K : ℕ) (R : Type*) := Fin N → Fin (2 ^ (K + 1)) → R

/-- Interpret address-indexed entries as local-word contribution tables. -/
def tablesFromEntries {N K : ℕ} {R : Type*} (entries : TableEntries N K R) :
    Tables N K R :=
  fun i w ↦ entries i (encode w)

/-- Direct local-word lookup selects the corresponding encoded table entry. -/
@[simp]
theorem lookup_eq {N K : ℕ} {R : Type*} (entries : TableEntries N K R)
    (i : Fin N) (w : LocalWord K) :
    tablesFromEntries entries i w = entries i (encode w) :=
  rfl

/-- The one-based R array index of a fixed-width local word. -/
def rIndex {m : ℕ} (w : Fin m → Bool) : ℕ :=
  (encode w).val + 1

/-- One-based indexing always gives a positive array index, including at length zero. -/
theorem rIndex_pos {m : ℕ} (w : Fin m → Bool) : 0 < rIndex w :=
  Nat.succ_pos _

/-- The R index stays within the array of all fixed-width binary words. -/
theorem rIndex_le {m : ℕ} (w : Fin m → Bool) : rIndex w ≤ 2 ^ m :=
  Nat.succ_le_of_lt (encode w).is_lt

/-- Removing R's one-based offset recovers the mathematical address. -/
@[simp]
theorem rIndex_sub_one {m : ℕ} (w : Fin m → Bool) :
    rIndex w - 1 = (encode w).val :=
  Nat.add_sub_cancel _ _

/-- One-based R lookup and zero-based mathematical lookup select the same entry. -/
theorem lookup_rIndex {N K : ℕ} {R : Type*} (entries : TableEntries N K R)
    (i : Fin N) (w : LocalWord K) :
    tablesFromEntries entries i w =
      entries i ⟨rIndex w - 1, by simp [rIndex]⟩ :=
  rfl

/-- Encode a direct local-word table as address-indexed entries. -/
def entriesFromTables {N K : ℕ} {R : Type*} (c : Tables N K R) : TableEntries N K R :=
  fun i q ↦ c i (decode q)

/-- Address-indexing followed by local-word interpretation preserves every table. -/
@[simp]
theorem tablesFromEntries_entriesFromTables {N K : ℕ} {R : Type*} (c : Tables N K R) :
    tablesFromEntries (entriesFromTables c) = c := by
  funext i w
  simp [tablesFromEntries, entriesFromTables]

/-- Local-word interpretation followed by address-indexing preserves every array. -/
@[simp]
theorem entriesFromTables_tablesFromEntries {N K : ℕ} {R : Type*}
    (entries : TableEntries N K R) : entriesFromTables (tablesFromEntries entries) = entries := by
  funext i q
  simp [tablesFromEntries, entriesFromTables]

end OrgLib.NK
