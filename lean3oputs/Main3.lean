import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fintype

#align_import main

--import data.equiv.basic
--import data.equiv.basic
-- import array_group
-- import array_group
open Equiv

section permArray

parameter {n : ℕ} {α : Type _}

@[simp]
private theorem array.read_def {f : Fin n → α} {i : Fin n} : Array'.read { data := f } i = f i :=
  rfl

def permArray (a : Array' n α) (p : Perm (Fin n)) : Array' n α :=
  ⟨a.read ∘ p.invFun⟩
#align perm_array permArray

theorem permArray_def (a : Array' n α) (p : Perm (Fin n)) : permArray a p = ⟨a.read ∘ p.invFun⟩ :=
  rfl
#align perm_array_def permArray_def

@[simp]
theorem permArray_array'_one {p : Perm (Fin n)} [Group α] : permArray 1 p = 1 :=
  by
  apply Array'.ext
  intro i
  rfl
#align perm_array_array_one permArray_array'_one

@[simp]
theorem permArray_perm_one {a : Array' n α} : permArray a 1 = a :=
  by
  apply Array'.ext
  intro i
  rfl
#align perm_array_perm_one permArray_perm_one

@[simp]
theorem permArray_comp {a : Array' n α} {p₁ p₂ : Perm (Fin n)} :
    permArray (permArray a p₁) p₂ = permArray a (p₂ * p₁) :=
  by
  apply Array'.ext
  simp [permArray_def, perm.mul_def]
#align perm_array_comp permArray_comp

end permArray

section

parameter {n : ℕ} {α : Type _} [Group α]

def ArrayPerm (n : ℕ) (α : Type _) :=
  Array' n α × Perm (Fin n)
#align array_perm ArrayPerm

@[reducible]
private def ap :=
  ArrayPerm n α

variable (a b c : ap)

private def mul : ap :=
  (permArray a.fst b.snd * b.fst, b.snd * a.snd)

private def inv : ap :=
  (permArray a.fst⁻¹ a.snd⁻¹, a.snd⁻¹)

instance ArrayPerm.hasMul : Mul ap :=
  ⟨mul⟩
#align array_perm.has_mul ArrayPerm.hasMul

instance ArrayPerm.hasOne : One ap :=
  ⟨(mkArray' n 1, 1)⟩
#align array_perm.has_one ArrayPerm.hasOne

instance ArrayPerm.hasInv : Inv ap :=
  ⟨inv⟩
#align array_perm.has_inv ArrayPerm.hasInv

@[simp]
private theorem mul_def : a * b = (permArray a.fst b.snd * b.fst, b.snd * a.snd) :=
  rfl

@[simp]
private theorem one_def : (1 : ap) = (mkArray' n 1, 1) :=
  rfl

@[simp]
private theorem inv_def : a⁻¹ = (permArray a.fst⁻¹ a.snd⁻¹, a.snd⁻¹) :=
  rfl

#print mul_assoc /-
private theorem mul_assoc : a * b * c = a * (b * c) :=
  by
  dsimp
  congr 1
  apply Array'.ext
  intro i
  simp only [permArray_def, Function.comp, array.read_mul, array.read_def, mul_assoc]
  rfl
-/

#print one_mul /-
private theorem one_mul : 1 * a = a := by
  dsimp
  change (permArray 1 a.snd * a.fst, a.snd * 1) = a
  rw [permArray_array'_one]
  simp
-/

#print mul_one /-
private theorem mul_one : a * 1 = a := by
  dsimp
  rw [permArray_perm_one]
  change (a.fst * 1, 1 * a.snd) = a
  simp
-/

#print mul_left_inv /-
private theorem mul_left_inv : a⁻¹ * a = 1 := by
  dsimp
  rw [permArray_comp]
  simp
  rfl
-/

instance arrayPermGroup : Group ap :=
  { mul := (· * ·)
    mul_assoc
    one := 1
    one_mul
    mul_one
    inv := Inv.inv
    hMul_left_inv }
#align array_perm_group arrayPermGroup

end
