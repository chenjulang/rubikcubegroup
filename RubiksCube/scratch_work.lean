import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Equiv Perm

def gp12 : Group (Equiv.Perm (Fin 12)) := permGroup
#check gp12

def iden : (Fin 12) → (Fin 12) := fun x => x

def idenPerm : Perm (Fin 12) := {
  toFun := iden
  invFun := iden
  left_inv := fun x => rfl
  right_inv := fun x => rfl
}

#check Perm.mul_def

def v : Vector (Fin 5) 3 := ⟨[4,0,1], (by rfl)⟩
def v2 : Vector (Fin 3) 3 := ⟨[2,0,1], (by rfl)⟩

#eval v + v

def move_right : (Fin 3) → (Fin 3) := fun x => x + 1
def moveRightPerm : Perm (Fin 3) := {
  toFun := move_right
  invFun := fun x => x - 1
  left_inv := fun x => by simp [move_right]
  right_inv := fun x => by simp [move_right]
}

def swapFLPerm : Perm (Fin 3) := Equiv.swap 0 2
def ident : Perm (Fin 3) := 1

#eval ident 2

#check Perm
#check List.ofFn
#check List.map
#check Vector.map

def permuteVector {α : Type} {n : ℕ} : Perm (Fin n) → Vector α n → Vector α n :=
  fun p v => {
    val := (Vector.ofFn (fun i => v.get (p.invFun i))).toList
    property := by simp
  }

-- #eval v.map swapFLPerm -- FAILS
#eval v
#eval permuteVector moveRightPerm v
#eval moveRightPerm 1
#eval moveRightPerm⁻¹ 1
-- #eval v2.map swapFLPerm -- not what I wanted

#eval ([-1, -2, -3, -4, -0] : List (Fin 5))
