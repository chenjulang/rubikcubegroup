import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

#align_import main

open Fin Nat

def Fin' :=
  Fin
#align fin' Fin'

variable {n : ℕ} (a b c : Fin' n.succ)

instance : One (Fin' n.succ) :=
  ⟨(0 : Fin n.succ)⟩

instance : Mul (Fin' n.succ) :=
  ⟨((· + ·) : Fin n.succ → Fin n.succ → Fin n.succ)⟩

private def inv : Fin' n.succ := by
  cases a
  cases a_val
  · exact 1
  · exact (n - a_val : Fin n.succ)

instance : Inv (Fin' n.succ) :=
  ⟨inv⟩

#print mul_assoc /-
private theorem mul_assoc : a * b * c = a * (b * c) :=
  by
  apply eq_of_veq
  simp [(· * ·), Fin.add_def, add_assoc]
-/

#print one_mul /-
private theorem one_mul : 1 * a = a := by
  apply eq_of_veq
  simp [One.one, (· * ·), Fin.add_def, mod_eq_of_lt a.is_lt]
-/

#print mul_one /-
private theorem mul_one : a * 1 = a := by
  apply eq_of_veq
  simp [One.one, (· * ·), Fin.add_def, mod_eq_of_lt a.is_lt]
-/

#print mul_left_inv /-
private theorem mul_left_inv : a⁻¹ * a = 1 :=
  by
  apply eq_of_veq
  cases a
  cases a_val
  · simp only [One.one, (· * ·), Inv.inv, inv, Fin.add_def]
    simp
  · simp only [(· * ·), Inv.inv, inv, Fin.add_def, Fin.sub_def]
    rw [coe_val_of_lt, coe_val_of_lt] <;> try simp [lt_of_succ_lt a_property]
    have : a_val ≤ n.succ := by
      have := nat.succ_lt_succ_iff.mp a_property
      apply le_of_lt
      apply lt_trans this
      apply n.lt_succ_self
    zify [this]
    trans ((n.succ : ℤ) + ((a_val.succ : ℤ) - (a_val : ℤ) + (n : ℤ))) % (n.succ : ℤ)
    · congr 1; ring
    rw [← Int.emod_add_emod, Int.emod_self, zero_add]
    push_cast
    simp only [add_tsub_cancel_left]
    rw [add_comm]
    norm_cast
    apply mod_self
    -- ???
    apply n.lt_succ_self
-/

#print mul_comm /-
private theorem mul_comm : a * b = b * a :=
  by
  apply eq_of_veq
  simp [(· * ·), Fin.add_def, add_comm]
-/

instance : CommGroup (Fin' n.succ) where
  mul := (· * ·)
  mul_assoc := mul_assoc
  one := 0
  one_mul := one_mul
  mul_one := mul_one
  inv := inv
  hMul_left_inv := mul_left_inv
  mul_comm := mul_comm
