import Lean
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Module.Equiv
open Equiv Perm

instance (n : Nat) : Repr (Perm (Fin n)) :=
    ⟨reprPrec ∘ Equiv.toFun⟩
instance (n : Nat) : DecidableEq (Perm (Fin n)) :=
  λ a b => mk.injEq a.toFun a.invFun _ _ b.toFun b.invFun _ _ ▸ inferInstance

structure PieceState (pieces orientations: ℕ+) where
  permute : Perm (Fin pieces)
  orient : Fin pieces → Fin orientations -- 这里应该是增加量，不是绝对量
  deriving Repr, DecidableEq

def ps_mul {p o : ℕ+} : PieceState p o → PieceState p o → PieceState p o :=
    fun a1 a2 => {
      permute := a2.permute * a1.permute -- *先运算右，再运算左。
      orient := (a2.orient ∘ a1.permute) + a1.orient -- ∘是右边的函数作用到左边的对象
    }
instance {p o : ℕ+} : Mul (PieceState p o) where
  mul a1 a2 := {
    permute := a2.permute * a1.permute
    orient := (a2.orient ∘ a1.permute) + a1.orient
  }

abbrev CornerType := PieceState 8 3
abbrev EdgeType := PieceState 12 2

abbrev RubiksSuperType := CornerType × EdgeType

def cyclePieces {α : Type*} [DecidableEq α] -- 这里如何文字上理解也是个问题，输入旧位置，得到新位置？
: List α → Perm α
:= fun list =>  List.formPerm list
def Orient
(p o : ℕ+)
(pairs : List ((Fin p) × (Fin o)))
: Fin p → Fin o :=
  fun i =>
    match pairs.lookup i with
    | some x => x
    | none => 0

def Solved
: RubiksSuperType
where
  fst := {
    permute := 1
    orient := 0
  }
  snd := {
    permute := 1
    orient := 0
  }

def U : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [0,3,2,1], orient := 0},
      {permute := cyclePieces [0,3,2,1], orient := 0}
    ⟩
def D : RubiksSuperType :=
  ⟨
    {permute := cyclePieces [4, 5, 6, 7], orient := 0},
    {permute := cyclePieces [8, 9, 10, 11], orient := 0}
  ⟩
def R : RubiksSuperType :=
  ⟨
    {permute := cyclePieces [1,2,6,5], orient := Orient 8 3 [(1, 2), (2, 1), (5, 1), (6, 2)]},
    {permute := cyclePieces [1, 6, 9, 5], orient := Orient 12 2 [(1,1 ), (5,1 ), (6,1 ), (9,1 )]}
  ⟩
def L : RubiksSuperType :=
  ⟨
    {permute := cyclePieces [0, 4, 7, 3], orient := Orient 8 3 [(0, 1), (3, 2), (4, 2), (7, 1)]},
    {permute := cyclePieces [3,4 ,11 ,7 ], orient := Orient 12 2 [(3, 1), (4,1 ), (7, 1), (11, 1)]}
  ⟩
def F : RubiksSuperType :=
  ⟨
    {permute := cyclePieces [0,1 ,5 ,4 ], orient := Orient 8 3 [(0, 2), (1, 1), (4, 1), (5, 2)]},
    {permute := cyclePieces [0, 5, 8, 4] , orient :=  Orient 12 2 [(0, 0), (4, 0), (5, 0), (8, 0)]}
  ⟩
def B : RubiksSuperType :=
  ⟨
    {permute := cyclePieces [2, 3, 7,6 ], orient := Orient 8 3 [(2, 2), (3, 1), (6, 1), (7, 2)]},
    {permute := cyclePieces [2, 7, 10,6 ], orient := Orient 12 2 [(2, 0), (6, 0), (7, 0), (10, 0)]}
  ⟩
def U2 := U^2
def D2 := D^2
def R2 := R^2
def L2 := L^2
def F2 := F^2
def B2 := B^2
def U' := U⁻¹
def D' := D⁻¹
def R' := R⁻¹
def L' := L⁻¹
def F' := F⁻¹
def B' := B⁻¹


def G1Perm_element : RubiksSuperType
  := R' * D * D * R * B' * U * U * B
def G1Perm : RubiksSuperType
  := G1Perm_element^2

#eval (F*G1Perm*F').1.permute
