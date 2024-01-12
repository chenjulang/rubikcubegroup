import Algebra.Group.Defs

#align_import main

open Array'

variable {n : ℕ} {α : Type _} [Group α] (a b c : Array' n α)

instance : Mul (Array' n α) :=
  ⟨Array'.map₂ (· * ·)⟩

instance : One (Array' n α) :=
  ⟨mkArray' n 1⟩

instance : Inv (Array' n α) :=
  ⟨flip Array'.map Inv.inv⟩

#print mul_assoc /-
private theorem mul_assoc : a * b * c = a * (b * c) :=
  by
  apply Array'.ext
  intro i
  apply mul_assoc
-/

#print one_mul /-
private theorem one_mul : 1 * a = a := by
  apply Array'.ext
  intro i
  apply one_mul
-/

#print mul_one /-
private theorem mul_one : a * 1 = a := by
  apply Array'.ext
  intro i
  apply mul_one
-/

#print mul_left_inv /-
private theorem mul_left_inv : a⁻¹ * a = 1 :=
  by
  apply Array'.ext
  intro i
  apply mul_left_inv
-/

instance arrayGroup : Group (Array' n α)
    where
  mul := (· * ·)
  mul_assoc := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  inv := Inv.inv
  hMul_left_inv := mul_left_inv
#align array_group arrayGroup

@[simp]
theorem Array'.read_hMul {a₁ a₂ : Array' n α} {i : Fin n} :
    (a₁ * a₂).read i = a₁.read i * a₂.read i :=
  rfl
#align array.read_mul Array'.read_hMul

