import Lean
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Equiv Perm

section RubiksSuperGroup

instance (n : Nat) : Repr (Perm (Fin n)) :=
  ⟨reprPrec ∘ Equiv.toFun⟩

instance (n m : Nat) : Repr (Vector (Fin n) m) :=
  ⟨reprPrec ∘ Vector.toList⟩

def permuteVector {α : Type} {n : ℕ} : Perm (Fin n) → Vector α n → Vector α n :=
  fun p v => {
    val := (Vector.ofFn (fun i => v.get (p.invFun i))).toList
    property := by simp
  }

structure PieceState (pieces orientations: ℕ+) where
  permute : Perm (Fin pieces)
  orient : Vector (Fin orientations) pieces
  deriving Repr

def ps_mul {p o : ℕ+} : PieceState p o → PieceState p o → PieceState p o :=
  fun a b => {
    permute := b.permute * a.permute
    orient := Vector.map₂ Fin.add (permuteVector b.permute a.orient) b.orient
  }

lemma ps_mul_assoc {p o : ℕ+} : ∀ (a b c : PieceState p o), ps_mul (ps_mul a b) c = ps_mul a (ps_mul b  c) := by
  intro a b c
  simp [ps_mul]
  apply And.intro
  { simp [Perm.mul_def, Equiv.trans_assoc] }
  { simp [permuteVector]
    sorry }

lemma ps_one_mul {p o : ℕ+} : ∀ (a : PieceState p o), ps_mul {permute := 1, orient := Vector.replicate p 0} a = a := by
  intro a
  simp [ps_mul, permuteVector]
  cases a with
  | mk a.permute a.orient =>
    simp
    sorry

lemma ps_mul_one {p o : ℕ+} : ∀ (a : PieceState p o), ps_mul a {permute := 1, orient := Vector.replicate p 0} = a := by
  intro a
  simp [ps_mul, permuteVector]
  cases a with
  | mk a.permute a.orient =>
    simp
    sorry

def ps_inv {p o : ℕ+} : PieceState p o → PieceState p o :=
  fun ps =>
  { permute := ps.permute⁻¹
    orient := permuteVector ps.permute⁻¹ (Vector.map (fun x => -x) ps.orient) }

lemma ps_mul_left_inv {p o : ℕ+} : ∀ (a : PieceState p o), ps_mul (ps_inv a) a = {permute := 1, orient := Vector.replicate p 0} := by
  intro a
  simp [ps_inv, ps_mul, permuteVector]
  sorry

instance PieceGroup (pieces orientations: ℕ+) :
Group (PieceState pieces orientations) := {
  mul := ps_mul
  mul_assoc := ps_mul_assoc
  one := {permute := 1, orient := Vector.replicate pieces 0}
  one_mul := ps_one_mul
  mul_one := ps_mul_one
  inv := ps_inv
  mul_left_inv := ps_mul_left_inv
}

lemma PieceState.mul_def {p o : ℕ+} (a b : PieceState p o) : a * b = ps_mul a b := by rfl

lemma PieceState.inv_def {p o : ℕ+} (a b : PieceState p o) : a⁻¹ = ps_inv a := by rfl

abbrev CornerType := PieceState 8 3
abbrev EdgeType := PieceState 12 2

instance Rubiks2x2Group : Group CornerType := PieceGroup 8 3

abbrev RubiksSuperType := CornerType × EdgeType
instance RubiksSuperGroup : Group RubiksSuperType := Prod.instGroup

end RubiksSuperGroup

def zeroOrient (p o : ℕ+) : Vector (Fin o) p  := Vector.replicate p 0

def orientVector (p o : ℕ+) : List ((Fin p) × (Fin o)) → Vector (Fin o) p
  | [] => zeroOrient p o
  | (i, x) :: os => (orientVector p o os).set i x

section FACE_TURNS

  def cycleImpl {α : Type*} [DecidableEq α] : α → List α → Perm α
    | _, [] => 1
    | a, (x :: xs) => swap a x * cycleImpl x xs

  def cyclePieces {α : Type*} [DecidableEq α] : List α → Perm α
    | [] => 1
    | (x :: xs) => cycleImpl x xs

  def U : RubiksSuperType :=
    ⟨{permute := cyclePieces [0, 1, 2, 3], orient := zeroOrient 8 3},
    {permute := cyclePieces [0, 1, 2, 3], orient := zeroOrient 12 2}⟩
  def D : RubiksSuperType :=
    ⟨{permute := cyclePieces [4, 5, 6, 7], orient := zeroOrient 8 3},
    {permute := cyclePieces [4, 5, 6, 7], orient := zeroOrient 12 2}⟩
  def R : RubiksSuperType :=
    ⟨{permute := cyclePieces [1, 6, 5, 2], orient := orientVector 8 3 [(1, 1), (6, 2), (5, 1), (2, 2)]},
    {permute := cyclePieces [1, 9, 5, 10], orient := zeroOrient 12 2}⟩
  def L : RubiksSuperType :=
    ⟨{permute := cyclePieces [0, 3, 4, 7], orient := orientVector 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)]},
    {permute := cyclePieces [3, 11, 7, 8], orient := zeroOrient 12 2}⟩
  def F : RubiksSuperType :=
    ⟨{permute := cyclePieces [2, 5, 4, 3], orient := orientVector 8 3 [(2, 1), (5, 2), (4, 1), (3, 2)]},
    {permute := cyclePieces [2, 10, 4, 11], orient := orientVector 12 2 [(2, 1), (10, 1), (4, 1), (11, 1)]}⟩
  def B : RubiksSuperType :=
    ⟨{permute := cyclePieces [0, 7, 6, 1], orient := orientVector 8 3 [(0, 1), (7, 2), (6, 1), (1, 2)]},
    {permute := cyclePieces [0, 8, 6, 9], orient := orientVector 12 2 [(0, 1), (8, 1), (6, 1), (9, 1)]}⟩
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

  inductive FaceTurn : RubiksSuperType → Prop where
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

end FACE_TURNS

def Solved : RubiksSuperType := 1
def TPerm : RubiksSuperType := R * U * R' * U' * R' * F * R2 * U' * R' * U' * R * U * R' * F'
def AlteredYPerm : RubiksSuperType := R * U' * R' * U' * R * U * R' * F' * R * U * R' * U' * R' * F * R

def CornerTwist : RubiksSuperType := ({permute := 1, orient := (zeroOrient 8 3).set 0 1}, {permute := 1, orient := zeroOrient 12 2})
def EdgeFlip : RubiksSuperType := ({permute := 1, orient := zeroOrient 8 3}, {permute := 1, orient := (zeroOrient 12 2).set 0 1})

section RubiksGroup

def ValidCube : Set RubiksSuperType := {c | Perm.sign c.fst.permute = Perm.sign c.snd.permute ∧ c.fst.orient.toList.sum = 0 ∧ c.snd.orient.toList.sum = 0}

lemma mul_mem' {a b : RubiksSuperType} : a ∈ ValidCube → b ∈ ValidCube → a * b ∈ ValidCube := by
  intro hav hbv
  simp [ValidCube, PieceState.mul_def, ps_mul]
  repeat' apply And.intro
  aesop
  { have h1 : sign fst.permute = sign snd.permute := by apply hav.left
    have h2 : sign fst_1.permute = sign snd_1.permute := by apply hbv.left
    simp [h1, h2] }
  { sorry }
  { sorry }

lemma one_mem' : 1 ∈ ValidCube := by
    simp [ValidCube]
    apply And.intro
    · apply Eq.refl
    · apply And.intro
      · apply Eq.refl
      · apply Eq.refl

lemma inv_mem' {x : RubiksSuperType} : x ∈ ValidCube → x⁻¹ ∈ ValidCube := by
  intro hxv
  simp [ValidCube, PieceState.inv_def, ps_inv]
  sorry

instance RubiksGroup : Subgroup RubiksSuperType := {
  carrier := ValidCube
  mul_mem' := mul_mem'
  one_mem' := one_mem'
  inv_mem' := inv_mem'
}

inductive Reachable : RubiksSuperType → Prop where
  | Solved : Reachable Solved
  | FT : ∀x : RubiksSuperType, FaceTurn x → Reachable x
  | mul : ∀x y : RubiksSuperType, Reachable x → Reachable y → Reachable (x * y)

end RubiksGroup

section WIDGET

inductive Color : Type | white | green | red | blue | orange | yellow

instance : ToString Color where
  toString :=
  fun c => match c with
    | Color.white => "#ffffff"
    | Color.green => "#00ff00"
    | Color.red => "#ff0000"
    | Color.blue => "#0000ff"
    | Color.orange => "#ff7f00"
    | Color.yellow => "#ffff00"

def List.vec {α : Type} : Π a : List α, Vector α (a.length)
  | [] => Vector.nil
  | (x :: xs) => Vector.cons x (xs.vec)

def corner_map : Vector (Vector Color 3) 8 :=
[
  [Color.white, Color.orange, Color.blue].vec,
  [Color.white, Color.blue, Color.red].vec,
  [Color.white, Color.red, Color.green].vec,
  [Color.white, Color.green, Color.orange].vec,
  [Color.yellow, Color.orange, Color.green].vec,
  [Color.yellow, Color.green, Color.red].vec,
  [Color.yellow, Color.red, Color.blue].vec,
  [Color.yellow, Color.blue, Color.orange].vec
].vec

def edge_map : Vector (Vector Color 2) 12 :=
[
  [Color.white, Color.blue].vec,
  [Color.white, Color.red].vec,
  [Color.white, Color.green].vec,
  [Color.white, Color.orange].vec,
  [Color.yellow, Color.green].vec,
  [Color.yellow, Color.red].vec,
  [Color.yellow, Color.blue].vec,
  [Color.yellow, Color.orange].vec,
  [Color.blue, Color.orange].vec,
  [Color.blue, Color.red].vec,
  [Color.green, Color.red].vec,
  [Color.green, Color.orange].vec
].vec

def corner_sticker : Fin 8 → Fin 3 → RubiksSuperType → Color :=
  fun i o cube => (corner_map.get (cube.1.permute⁻¹ i)).get (Fin.sub o (cube.1.orient.get i))

def edge_sticker : Fin 12 → Fin 2 → RubiksSuperType → Color :=
  fun i o cube => (edge_map.get (cube.2.permute⁻¹ i)).get (Fin.sub o (cube.2.orient.get i))

open Lean Widget

def L8x3 : List (ℕ × ℕ) := (List.map (fun x => (x, 0)) (List.range 8)) ++ (List.map (fun x => (x, 1)) (List.range 8)) ++ (List.map (fun x => (x, 2)) (List.range 8))
def L12x2 : List (ℕ × ℕ) := (List.map (fun x => (x, 0)) (List.range 12)) ++ (List.map (fun x => (x, 1)) (List.range 12))

def cubeStickerJson : RubiksSuperType → Json :=
  fun cube => Json.mkObj
  ((List.map (fun p => (s!"c_{p.fst}_{p.snd}", Json.str (toString (corner_sticker p.fst p.snd $ cube)))) L8x3)
  ++
  (List.map (fun p => (s!"e_{p.fst}_{p.snd}", Json.str (toString (edge_sticker p.fst p.snd $ cube)))) L12x2))

@[widget] def cubeWidget : UserWidgetDefinition where
  name := "Cube State"
  javascript :="
    import * as React from 'react';

  export default function (props) {
    return React.createElement(
      'div',
      {
        style: {
          display: 'grid',
          gridTemplateColumns: 'repeat(12, 20px)',
          gridTemplateRows: 'repeat(9, 20px)',
          rowGap: '2px',
          columnGap: '2px',
          margin: '10px',
        },
      },
      React.createElement('div', {style: {gridColumn: '4', gridRow: '1', backgroundColor: props.c_0_0}}),
      React.createElement('div', {style: {gridColumn: '5', gridRow: '1', backgroundColor: props.e_0_0}}),
      React.createElement('div', {style: {gridColumn: '6', gridRow: '1', backgroundColor: props.c_1_0}}),
      React.createElement('div', {style: {gridColumn: '4', gridRow: '2', backgroundColor: props.e_3_0}}),
      React.createElement('div', {style: {gridColumn: '5', gridRow: '2', backgroundColor: '#ffffff'}}),
      React.createElement('div', {style: {gridColumn: '6', gridRow: '2', backgroundColor: props.e_1_0}}),
      React.createElement('div', {style: {gridColumn: '4', gridRow: '3', backgroundColor: props.c_3_0}}),
      React.createElement('div', {style: {gridColumn: '5', gridRow: '3', backgroundColor: props.e_2_0}}),
      React.createElement('div', {style: {gridColumn: '6', gridRow: '3', backgroundColor: props.c_2_0}}),
      React.createElement('div', {style: {gridColumn: '1', gridRow: '4', backgroundColor: props.c_0_1}}),
      React.createElement('div', {style: {gridColumn: '2', gridRow: '4', backgroundColor: props.e_3_1}}),
      React.createElement('div', {style: {gridColumn: '3', gridRow: '4', backgroundColor: props.c_3_2}}),
      React.createElement('div', {style: {gridColumn: '1', gridRow: '5', backgroundColor: props.e_8_1}}),
      React.createElement('div', {style: {gridColumn: '2', gridRow: '5', backgroundColor: '#ff7f00'}}),
      React.createElement('div', {style: {gridColumn: '3', gridRow: '5', backgroundColor: props.e_11_1}}),
      React.createElement('div', {style: {gridColumn: '1', gridRow: '6', backgroundColor: props.c_7_2}}),
      React.createElement('div', {style: {gridColumn: '2', gridRow: '6', backgroundColor: props.e_7_1}}),
      React.createElement('div', {style: {gridColumn: '3', gridRow: '6', backgroundColor: props.c_4_1}}),
      React.createElement('div', {style: {gridColumn: '4', gridRow: '4', backgroundColor: props.c_3_1}}),
      React.createElement('div', {style: {gridColumn: '5', gridRow: '4', backgroundColor: props.e_2_1}}),
      React.createElement('div', {style: {gridColumn: '6', gridRow: '4', backgroundColor: props.c_2_2}}),
      React.createElement('div', {style: {gridColumn: '4', gridRow: '5', backgroundColor: props.e_11_0}}),
      React.createElement('div', {style: {gridColumn: '5', gridRow: '5', backgroundColor: '#00ff00'}}),
      React.createElement('div', {style: {gridColumn: '6', gridRow: '5', backgroundColor: props.e_10_0}}),
      React.createElement('div', {style: {gridColumn: '4', gridRow: '6', backgroundColor: props.c_4_2}}),
      React.createElement('div', {style: {gridColumn: '5', gridRow: '6', backgroundColor: props.e_4_1}}),
      React.createElement('div', {style: {gridColumn: '6', gridRow: '6', backgroundColor: props.c_5_1}}),
      React.createElement('div', {style: {gridColumn: '7', gridRow: '4', backgroundColor: props.c_2_1}}),
      React.createElement('div', {style: {gridColumn: '8', gridRow: '4', backgroundColor: props.e_1_1}}),
      React.createElement('div', {style: {gridColumn: '9', gridRow: '4', backgroundColor: props.c_1_2}}),
      React.createElement('div', {style: {gridColumn: '7', gridRow: '5', backgroundColor: props.e_10_1}}),
      React.createElement('div', {style: {gridColumn: '8', gridRow: '5', backgroundColor: '#ff0000'}}),
      React.createElement('div', {style: {gridColumn: '9', gridRow: '5', backgroundColor: props.e_9_1}}),
      React.createElement('div', {style: {gridColumn: '7', gridRow: '6', backgroundColor: props.c_5_2}}),
      React.createElement('div', {style: {gridColumn: '8', gridRow: '6', backgroundColor: props.e_5_1}}),
      React.createElement('div', {style: {gridColumn: '9', gridRow: '6', backgroundColor: props.c_6_1}}),
      React.createElement('div', {style: {gridColumn: '10', gridRow: '4', backgroundColor: props.c_1_1}}),
      React.createElement('div', {style: {gridColumn: '11', gridRow: '4', backgroundColor: props.e_0_1}}),
      React.createElement('div', {style: {gridColumn: '12', gridRow: '4', backgroundColor: props.c_0_2}}),
      React.createElement('div', {style: {gridColumn: '10', gridRow: '5', backgroundColor: props.e_9_0}}),
      React.createElement('div', {style: {gridColumn: '11', gridRow: '5', backgroundColor: '#0000ff'}}),
      React.createElement('div', {style: {gridColumn: '12', gridRow: '5', backgroundColor: props.e_8_0}}),
      React.createElement('div', {style: {gridColumn: '10', gridRow: '6', backgroundColor: props.c_6_2}}),
      React.createElement('div', {style: {gridColumn: '11', gridRow: '6', backgroundColor: props.e_6_1}}),
      React.createElement('div', {style: {gridColumn: '12', gridRow: '6', backgroundColor: props.c_7_1}}),
      React.createElement('div', {style: {gridColumn: '4', gridRow: '7', backgroundColor: props.c_4_0}}),
      React.createElement('div', {style: {gridColumn: '5', gridRow: '7', backgroundColor: props.e_4_0}}),
      React.createElement('div', {style: {gridColumn: '6', gridRow: '7', backgroundColor: props.c_5_0}}),
      React.createElement('div', {style: {gridColumn: '4', gridRow: '8', backgroundColor: props.e_7_0}}),
      React.createElement('div', {style: {gridColumn: '5', gridRow: '8', backgroundColor: '#ffff00'}}),
      React.createElement('div', {style: {gridColumn: '6', gridRow: '8', backgroundColor: props.e_5_0}}),
      React.createElement('div', {style: {gridColumn: '4', gridRow: '9', backgroundColor: props.c_7_0}}),
      React.createElement('div', {style: {gridColumn: '5', gridRow: '9', backgroundColor: props.e_6_0}}),
      React.createElement('div', {style: {gridColumn: '6', gridRow: '9', backgroundColor: props.c_6_0}}),
    );
  }"

end WIDGET

#widget cubeWidget (cubeStickerJson Solved)
#widget cubeWidget (cubeStickerJson TPerm)
#widget cubeWidget (cubeStickerJson AlteredYPerm)
#widget cubeWidget (cubeStickerJson CornerTwist)
#widget cubeWidget (cubeStickerJson EdgeFlip)

section SolutionState

def CornersSolved : RubiksSuperType → Prop :=
  fun c => c.fst.permute = 1 ∧ c.fst.orient = zeroOrient 8 3

def EdgesSolved : RubiksSuperType → Prop :=
  fun c => c.snd.permute = 1 ∧ c.snd.orient = zeroOrient 12 2

def IsSolved : RubiksSuperType → Prop := fun c => CornersSolved c ∧ EdgesSolved c

instance {c} : Decidable (CornersSolved c) := by apply And.decidable
instance {c} : Decidable (EdgesSolved c) := by apply And.decidable
instance {c} : Decidable (IsSolved c) := by apply And.decidable

end SolutionState
