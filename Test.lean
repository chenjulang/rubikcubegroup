import Lean
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Equiv Perm

section RubiksSuperGroup

  instance (n : Nat) : Repr (Perm (Fin n)) :=
    ⟨reprPrec ∘ Equiv.toFun⟩

  instance (n : Nat) : DecidableEq (Perm (Fin n)) :=
    λ a b => mk.injEq a.toFun a.invFun _ _ b.toFun b.invFun _ _ ▸ inferInstance


  /- This PieceState structure is used to represent the entire state of both corner pieces and edge pieces.-/
  structure PieceState (pieces orientations: ℕ+) where
    permute : Perm (Fin pieces)
    orient : Fin pieces → Fin orientations
    deriving Repr, DecidableEq


  def ps_mul {p o : ℕ+} : PieceState p o → PieceState p o → PieceState p o :=
    fun a1 a2 => {
      permute := a1.permute * a2.permute
      orient := (a2.orient ∘ a1.permute.invFun) + a1.orient
    }
  instance {p o : ℕ+} : Mul (PieceState p o) where
    mul a1 a2 := {
      permute := a1.permute * a2.permute
      orient := (a2.orient ∘ a1.permute.invFun) + a1.orient
    }


  @[simp] -- 这个同时代表了手写证明中的ρ和σ的同态性质
  theorem permute_mul {p o : ℕ+} (a1 a2 : PieceState p o)
  : (a1 * a2).permute = a1.permute * a2.permute
  := rfl

  @[simp]
  lemma ps_mul_assoc {p o : ℕ+} :
  ∀ (a b c : PieceState p o),
  -- ps_mul a (ps_mul b c) = ps_mul (ps_mul a b) c -- 一样的，换个位置。
  ps_mul (ps_mul a b) c = ps_mul a (ps_mul b c)
  := by
    intro a b c
    simp [ps_mul]
    apply And.intro
    · simp [Perm.mul_def]
      simp [Equiv.trans_assoc]
    · rw [← add_assoc]
      simp only [add_left_inj]
      exact rfl
    done


  @[simp]
  lemma ps_one_mul {p o : ℕ+} :
  ∀ (a : PieceState p o),
  ps_mul {permute := 1, orient := 0} a  =  a
  := by
    intro a
    simp only [ps_mul]
    simp only [one_mul, invFun_as_coe, one_symm, coe_one, Function.comp.right_id, add_zero]
    done


  @[simp]
  lemma ps_mul_one {p o : ℕ+} :
  ∀ (a : PieceState p o),
  ps_mul a {permute := 1, orient := 0} = a := by
    intro a
    simp only [ps_mul]
    simp only [mul_one, invFun_as_coe, Pi.zero_comp, zero_add]
    done


  def ps_inv {p o : ℕ+}
  : PieceState p o → PieceState p o
  :=
    fun ps =>
    {
      permute := ps.permute⁻¹
      orient := (-ps.orient) ∘ ps.permute
    }

  @[simp]
  lemma ps_mul_left_inv {p o : ℕ+} :
  ∀ (a : PieceState p o),
  ps_mul (ps_inv a) a = {permute := 1, orient := 0}
  := by
    intro a
    simp only [ps_inv]
    simp only [ps_mul]
    simp only [mul_left_inv]
    simp only [invFun_as_coe, PieceState.mk.injEq, true_and]
    exact neg_eq_iff_add_eq_zero.mp rfl

  /- This sets up a group structure for all Rubik's cube positions
  (including invalid ones that couldn't be reached from a solved state without removing pieces from the cube,
  twisting corners, etc.). -/
  instance PieceGroup (p o: ℕ+) :
  Group (PieceState p o) := {
    mul := ps_mul
    mul_assoc := ps_mul_assoc
    one := {permute := 1, orient := 0}
    one_mul := ps_one_mul
    mul_one := ps_mul_one
    inv := ps_inv
    mul_left_inv := ps_mul_left_inv
  }


  @[simp]
  lemma PieceState.mul_def {p o : ℕ+} (a b : PieceState p o) : a * b = ps_mul a b := by rfl
  @[simp]
  lemma PieceState.inv_def {p o : ℕ+} (a b : PieceState p o) : a⁻¹ = ps_inv a := by rfl

  abbrev CornerType := PieceState 8 3
  abbrev EdgeType := PieceState 12 2

  instance Rubiks2x2Group :
  Group CornerType
  := PieceGroup 8 3

  abbrev RubiksSuperType := CornerType × EdgeType
  instance RubiksSuperGroup -- 就是手写证明中的群H
  : Group RubiksSuperType
  := Prod.instGroup --???

end RubiksSuperGroup

/- Creates an orientation function given a list of input-output pairs
(with 0 for anything left unspecified). -/


def Orient
(p o : ℕ+)
(pairs : List ((Fin p) × (Fin o)))
: Fin p → Fin o :=
  fun i =>
    match pairs.lookup i with
    | some x => x
    | none => 0

#eval Orient 3 2 [(0, 1), (1, 0), (2, 1)] -- ![1, 0, 1]

def Solved
: RubiksSuperType
:= 1

section FACE_TURNS

  /- These two functions (from kendfrey's repository) create a cycle permutation,
  which is useful for defining the rotation of any given face, as seen directly below. -/

  def cycleImpl {α : Type*} [DecidableEq α]
  : α → List α → Perm α
    | _, [] => 1 -- “_”指的是第一个元素。可以写成a吗???
    | a, (x :: xs) => (swap a x) * (cycleImpl x xs) -- “a”指的是第一个元素
    --

  def cyclePieces {α : Type*} [DecidableEq α]
  : List α → Perm α
    | [] => 1
    | (x :: xs) => cycleImpl x xs


  def U : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [0, 1, 2, 3], orient := 0}, -- 第一是角块
      {permute := cyclePieces [0, 1, 2, 3], orient := 0}  -- 第二是棱块
    ⟩
  def D : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [4, 5, 6, 7], orient := 0},
      {permute := cyclePieces [4, 5, 6, 7], orient := 0}
    ⟩
  def R : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [1, 6, 5, 2], orient := Orient 8 3 [(1, 1), (6, 2), (5, 1), (2, 2)]},
      {permute := cyclePieces [1, 9, 5, 10], orient := 0}
    ⟩
  def L : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [0, 3, 4, 7], orient := Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)]},
      {permute := cyclePieces [3, 11, 7, 8], orient := 0}
    ⟩
  def F : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [2, 5, 4, 3], orient := Orient 8 3 [(2, 1), (5, 2), (4, 1), (3, 2)]},
      {permute := cyclePieces [2, 10, 4, 11], orient := Orient 12 2 [(2, 1), (10, 1), (4, 1), (11, 1)]}
    ⟩
  def B : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [0, 7, 6, 1], orient := Orient 8 3 [(0, 1), (7, 2), (6, 1), (1, 2)]},
      {permute := cyclePieces [0, 8, 6, 9], orient := Orient 12 2 [(0, 1), (8, 1), (6, 1), (9, 1)]}
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

  -- #check Multiplicative.coeToFun

  inductive FaceTurn
  : RubiksSuperType → Prop where
    | U : FaceTurn U
    | D : FaceTurn D
    | R : FaceTurn R
    | L : FaceTurn L
    | F : FaceTurn F
    | B : FaceTurn B
    | U2 : FaceTurn U2
    | D2 : FaceTurn D2
    | R2 : FaceTurn R2
    | L2 : FaceTurn L2
    | F2 : FaceTurn F2
    | B2 : FaceTurn B2
    | U' : FaceTurn U'
    | D' : FaceTurn D'
    | R' : FaceTurn R'
    | L' : FaceTurn L'
    | F' : FaceTurn F'
    | B' : FaceTurn B'

  instance : ToString RubiksSuperType where
    toString : RubiksSuperType → String :=
    fun c =>
      if c = Solved then "Solved"
      else if c = U then "U"
      else if c = D then "D"
      else if c = R then "R"
      else if c = L then "L"
      else if c = F then "F"
      else if c = B then "B"
      else if c = U2 then "U2"
      else if c = D2 then "D2"
      else if c = R2 then "R2"
      else if c = L2 then "L2"
      else if c = F2 then "F2"
      else if c = B2 then "B2"
      else if c = U' then "U'"
      else if c = D' then "D'"
      else if c = R' then "R'"
      else if c = L' then "L'"
      else if c = F' then "F'"
      else if c = B' then "B'"
      else s!"{repr c}"

  -- instance : Multiplicative.coeToFun RubiksSuperType := {coe := fun (a : RubiksSuperType) => fun (b : RubiksSuperType) => a * b }
  --? How do I get the line above to work?

end FACE_TURNS


def TPerm : RubiksSuperType -- 这个*是在哪里定义的呢？，看定义就知道，因为RubiksSuperType是笛卡尔积CornerType × EdgeType，其乘法就是两个分量分别乘积
  := R * U * R' * U' * R' * F * R2 * U' * R' * U' * R * U * R' * F'
def AlteredYPerm : RubiksSuperType
  := R * U' * R' * U' * R * U * R' * F' * R * U * R' * U' * R' * F * R


def CornerTwist : RubiksSuperType  -- 应该是形容两个不可能的魔方状态：只旋转一次角块，还有只旋转一次棱块
  := (
      {permute := 1, orient := (fun | 0 => 1 | _ => 0) }, -- 这种是归纳定义的向量写法，只有0位置为1，其余为0。
      {permute := 1, orient := 0}
     )
def EdgeFlip : RubiksSuperType
  := (
      {permute := 1, orient := 0},
      {permute := 1, orient := (fun | 0 => 1 | _ => 0)}
     )



section RubiksGroup

  -- def ValidCube : Set RubiksSuperType := {c | Perm.sign c.fst.permute = Perm.sign c.snd.permute ∧ Fin.foldl 8 (fun acc n => acc + c.fst.orient n) 0 = 0 ∧ Fin.foldl 12 (fun acc n => acc + c.snd.orient n) 0 = 0}
  def ValidCube :
  Set RubiksSuperType
  :=
  {
    c |
    Perm.sign c.fst.permute = Perm.sign c.snd.permute
    ∧
    Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) c.fst.orient = 0
    ∧
    Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) c.snd.orient = 0
  }

  lemma mul_mem' {a b : RubiksSuperType}
  : a ∈ ValidCube → b ∈ ValidCube → a * b ∈ ValidCube
  := by
    intro hav hbv
    simp only [ValidCube]
    -- simp only [PieceState.mul_def]
    -- simp only [ps_mul]
    -- repeat' apply And.intro
    apply And.intro
    {
      have h1 : sign a.1.permute = sign a.2.permute
        := by apply hav.left
      have h2 : sign b.1.permute = sign b.2.permute
        := by apply hbv.left
      simp only [Prod.fst_mul, PieceState.mul_def, Prod.snd_mul]
      simp only [ps_mul]
      simp only [map_mul]
      exact Mathlib.Tactic.LinearCombination.mul_pf h1 h2
    }
    apply And.intro
    {
      have h1 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} a.1.orient = 0
        := by apply hav.right.left
      have h2 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} b.1.orient = 0
        := by apply hbv.right.left
      -- rw [PieceState.orient, PieceState.orient]
      -- rw [Finset.sum_add_distrib, h2]
      simp only [Finset.mem_singleton, Finset.mem_insert, zero_ne_one, false_or, Prod.fst_mul,PieceState.mul_def]
      simp only [ps_mul]
      simp only [Finset.mem_singleton, Finset.mem_insert, zero_ne_one, false_or, invFun_as_coe,
        Pi.add_apply, Function.comp_apply]
      simp only [Finset.sum_add_distrib]
      rw [h1]
      simp only [add_zero]
      -- refine Equiv.Perm.prod_comp
      -- apply h2
      sorry
    }
    { sorry }

end RubiksGroup
