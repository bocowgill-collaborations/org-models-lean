import OrgLib.NK.Basic
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Cyclic NK scopes and rotation

Cyclic scopes read the focal locus and the next `K` coordinates, wrapping around
the ring. A single shared table gives a rotation-invariant fitness landscape.
-/

namespace OrgLib.NK

open scoped BigOperators

variable {N K : ℕ} {R : Type*}

/-- Forward cyclic scopes with their focal locus in slot zero. -/
def cyclicTopology (hKN : K < N) : Topology N K where
  k_lt_n := hKN
  scope i :=
    { toFun := fun j ↦ i + Fin.castLE (Nat.succ_le_of_lt hKN) j
      inj' := fun _ _ h ↦ Fin.castLE_injective _ (add_left_cancel h) }
  self i := Fin.ext (by simp [Fin.add_def, Nat.mod_eq_of_lt i.is_lt])

/-- Every locus uses the same supplied local contribution table. -/
def sharedTables (φ : LocalWord K → R) : Tables N K R :=
  fun _ ↦ φ

/-- Rotate the configuration by reading coordinate `i + r` at coordinate `i`. -/
def rotate (r : Fin N) (x : Config N) : Config N :=
  fun i ↦ x (i + r)

/-- The cyclic scope is the forward modular window required by the source model. -/
@[simp]
theorem cyclicTopology_scope_val (hKN : K < N) (i : Fin N) (j : Fin (K + 1)) :
    ((cyclicTopology hKN).scope i j).val = (i.val + j.val) % N :=
  rfl

/-- Extracting a cyclic scope reads its forward modular word. -/
theorem extract_cyclic (hKN : K < N) (x : Config N) (i : Fin N) :
    extract (cyclicTopology hKN) x i = fun j ↦
      x ⟨(i.val + j.val) % N, Nat.mod_lt _ (Nat.zero_lt_of_lt hKN)⟩ :=
  rfl

/-- Rotation acts by modular addition on the coordinate index. -/
@[simp]
theorem rotate_apply (r : Fin N) (x : Config N) (i : Fin N) :
    rotate r x i = x (i + r) :=
  rfl

/-- The same rotation written with explicit natural-number modular indices. -/
theorem rotate_apply_mod (r : Fin N) (x : Config N) (i : Fin N) :
    rotate r x i = x ⟨(i.val + r.val) % N, Nat.mod_lt _ (Nat.zero_lt_of_lt i.is_lt)⟩ :=
  rfl

/-- Rotating the state shifts the focal locus of every extracted cyclic word. -/
theorem extract_cyclic_rotate (hKN : K < N) (r : Fin N) (x : Config N) (i : Fin N) :
    extract (cyclicTopology hKN) (rotate r x) i =
      extract (cyclicTopology hKN) x (i + r) := by
  funext j
  simp [extract, rotate, cyclicTopology, add_assoc, add_comm]

/-- A shared cyclic table gives the same fitness after every rotation of the state. -/
theorem fitness_shared_rotate [Field R] [CharZero R]
    (hKN : K < N) (φ : LocalWord K → R) (x : Config N) (r : Fin N) :
    fitness (cyclicTopology hKN) (sharedTables φ) (rotate r x) =
      fitness (cyclicTopology hKN) (sharedTables φ) x := by
  letI : NeZero N := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hKN)⟩
  simp only [fitness, contribution, extract_cyclic_rotate, sharedTables]
  congr 1
  exact Equiv.sum_comp (Equiv.addRight r) (fun i ↦ φ (extract (cyclicTopology hKN) x i))

end OrgLib.NK
