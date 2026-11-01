import OrgLib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Binary codec boundary and orientation checks

The codec includes empty words and preserves leading zeros. Distinct most- and
least-significant-bit fixtures prevent a reversed convention from passing these
tests. The inverse laws below apply to arbitrary lengths, beyond the small fixtures.
-/

namespace OrgLibTest.Encoding

open OrgLib.NK

example (w : Fin 0 → Bool) : encode w = 0 :=
  Fin.eq_zero _

example {m : ℕ} (w : Fin m → Bool) : decode (encode w) = w :=
  decode_encode w

example {m : ℕ} (q : Fin (2 ^ m)) : encode (decode q) = q :=
  encode_decode q

example : (encode (fun _ : Fin 1 ↦ false)).val = 0 := by
  norm_num [encode_val, Fin.sum_univ_succ]

example : (encode (fun _ : Fin 1 ↦ true)).val = 1 := by
  norm_num [encode_val, Fin.sum_univ_succ]

example : (encode (fun i : Fin 3 ↦ i == 2)).val = 1 := by
  norm_num [encode_val, Fin.sum_univ_succ]

example : (encode (fun i : Fin 3 ↦ i == 0)).val = 4 := by
  norm_num [encode_val, Fin.sum_univ_succ]

example : decode (2 : Fin (2 ^ 3)) = fun i : Fin 3 ↦ i == 1 := by
  decide

example : rIndex (fun _ : Fin 3 ↦ false) = 1 := by
  norm_num [rIndex, encode_val, Fin.sum_univ_succ]

example : rIndex (fun _ : Fin 3 ↦ true) = 8 := by
  norm_num [rIndex, encode_val, Fin.sum_univ_succ]

example {N K : ℕ} {R : Type*} (entries : TableEntries N K R)
    (i : Fin N) (w : LocalWord K) :
    tablesFromEntries entries i w = entries i (encode w) :=
  lookup_eq entries i w

/--
info: 0
-/
#guard_msgs in
#eval (encode (fun i : Fin 0 ↦ Fin.elim0 i)).val

/--
info: []
-/
#guard_msgs in
#eval List.ofFn (decode (0 : Fin (2 ^ 0)))

/--
info: [0, 1, 1, 4, 1, 8]
-/
#guard_msgs in
#eval [
  (encode (fun _ : Fin 1 ↦ false)).val,
  (encode (fun _ : Fin 1 ↦ true)).val,
  (encode (fun i : Fin 3 ↦ i == 2)).val,
  (encode (fun i : Fin 3 ↦ i == 0)).val,
  rIndex (fun _ : Fin 3 ↦ false),
  rIndex (fun _ : Fin 3 ↦ true)]

/--
info: [false, true, false]
-/
#guard_msgs in
#eval List.ofFn (decode (2 : Fin (2 ^ 3)))

end OrgLibTest.Encoding
