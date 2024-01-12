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
  fun a b => {
    permute := b.permute * a.permute
    orient := (a.orient ∘ b.permute.invFun) + b.orient
  }

-- instance: Mul (PieceState p o) := mul
--? How can I define multiplication, one, and inverses as implicit components of the PieceState type?

lemma ps_mul_assoc {p o : ℕ+} : ∀ (a b c : PieceState p o), ps_mul (ps_mul a b) c = ps_mul a (ps_mul b  c) := by
  intro a b c
  simp [ps_mul]
  apply And.intro
  { simp [Perm.mul_def, Equiv.trans_assoc] }
  { sorry }

lemma ps_one_mul {p o : ℕ+} : ∀ (a : PieceState p o), ps_mul {permute := 1, orient := 0} a = a := by
  intro a
  simp [ps_mul]

lemma ps_mul_one {p o : ℕ+} : ∀ (a : PieceState p o), ps_mul a {permute := 1, orient := 0} = a := by
  intro a
  simp [ps_mul]

def ps_inv {p o : ℕ+} : PieceState p o → PieceState p o :=
  fun ps =>
  { permute := ps.permute⁻¹
    orient := fun x => - ps.orient (ps.permute⁻¹ x) }

lemma ps_mul_left_inv {p o : ℕ+} : ∀ (a : PieceState p o), ps_mul (ps_inv a) a = {permute := 1, orient := 0} := by
  intro a
  simp [ps_inv, ps_mul]
  sorry

/- This sets up a group structure for all Rubik's cube positions (including invalid ones that couldn't be reached from a solved state without removing pieces from the cube, twisting corners, etc.). -/
instance PieceGroup (pieces orientations: ℕ+) :
Group (PieceState pieces orientations) := {
  mul := ps_mul
  mul_assoc := ps_mul_assoc
  one := {permute := 1, orient := 0}
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

/- Creates an orientation function given a list of input-output pairs (with 0 for anything left unspecified). -/
def Orient (p o : ℕ+) (pairs : List ((Fin p) × (Fin o))) : Fin p → Fin o :=
  fun i =>
    match pairs.lookup i with
    | some x => x
    | none => 0

def Solved : RubiksSuperType := 1

section FACE_TURNS

  /- These two functions (from kendfrey's repository) create a cycle permutation, which is useful for defining the rotation of any given face, as seen directly below. -/
  def cycleImpl {α : Type*} [DecidableEq α] : α → List α → Perm α
    | _, [] => 1
    | a, (x :: xs) => swap a x * cycleImpl x xs

  def cyclePieces {α : Type*} [DecidableEq α] : List α → Perm α
    | [] => 1
    | (x :: xs) => cycleImpl x xs

  -- #eval List.map (cycle [0, 1, 2, 3] : Perm (Fin 12)) (List.range 12)
  -- #eval List.map (cycle [0, 5, 8] : Perm (Fin 12)) (List.range 12)

  def U : RubiksSuperType :=
    ⟨{permute := cyclePieces [0, 1, 2, 3], orient := 0},
    {permute := cyclePieces [0, 1, 2, 3], orient := 0}⟩
  def D : RubiksSuperType :=
    ⟨{permute := cyclePieces [4, 5, 6, 7], orient := 0},
    {permute := cyclePieces [4, 5, 6, 7], orient := 0}⟩
  def R : RubiksSuperType :=
    ⟨{permute := cyclePieces [1, 6, 5, 2], orient := Orient 8 3 [(1, 1), (6, 2), (5, 1), (2, 2)]},
    {permute := cyclePieces [1, 9, 5, 10], orient := 0}⟩
  def L : RubiksSuperType :=
    ⟨{permute := cyclePieces [0, 3, 4, 7], orient := Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)]},
    {permute := cyclePieces [3, 11, 7, 8], orient := 0}⟩
  def F : RubiksSuperType :=
    ⟨{permute := cyclePieces [2, 5, 4, 3], orient := Orient 8 3 [(2, 1), (5, 2), (4, 1), (3, 2)]},
    {permute := cyclePieces [2, 10, 4, 11], orient := Orient 12 2 [(2, 1), (10, 1), (4, 1), (11, 1)]}⟩
  def B : RubiksSuperType :=
    ⟨{permute := cyclePieces [0, 7, 6, 1], orient := Orient 8 3 [(0, 1), (7, 2), (6, 1), (1, 2)]},
    {permute := cyclePieces [0, 8, 6, 9], orient := Orient 12 2 [(0, 1), (8, 1), (6, 1), (9, 1)]}⟩
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

  #check Multiplicative.coeToFun

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

def TPerm : RubiksSuperType := R * U * R' * U' * R' * F * R2 * U' * R' * U' * R * U * R' * F'
def AlteredYPerm : RubiksSuperType := R * U' * R' * U' * R * U * R' * F' * R * U * R' * U' * R' * F * R

def CornerTwist : RubiksSuperType := ({permute := 1, orient := (fun | 0 => 1 | _ => 0) }, {permute := 1, orient := 0})
def EdgeFlip : RubiksSuperType := ({permute := 1, orient := 0}, {permute := 1, orient := (fun | 0 => 1 | _ => 0)})

section RubiksGroup

-- def ValidCube : Set RubiksSuperType := {c | Perm.sign c.fst.permute = Perm.sign c.snd.permute ∧ Fin.foldl 8 (fun acc n => acc + c.fst.orient n) 0 = 0 ∧ Fin.foldl 12 (fun acc n => acc + c.snd.orient n) 0 = 0}
def ValidCube : Set RubiksSuperType := {c | Perm.sign c.fst.permute = Perm.sign c.snd.permute ∧ Finset.sum ({0,1,2,3,4,5,6,7} : Finset (Fin 8)) c.fst.orient = 0 ∧ Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11} : Finset (Fin 12)) c.snd.orient = 0}

lemma mul_mem' {a b : RubiksSuperType} : a ∈ ValidCube → b ∈ ValidCube → a * b ∈ ValidCube := by
  intro hav hbv
  simp [ValidCube, PieceState.mul_def, ps_mul]
  repeat' apply And.intro
  { have h1 : sign a.1.permute = sign a.2.permute := by apply hav.left
    have h2 : sign b.1.permute = sign b.2.permute := by apply hbv.left
    simp [h1, h2] }
  { have h1 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} a.1.orient = 0 := by apply hav.right.left
    have h2 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} b.1.orient = 0 := by apply hbv.right.left
    -- rw [PieceState.orient, PieceState.orient]
    rw [Finset.sum_add_distrib, h2]
    sorry }
  { sorry }

#check Finset.sum_add_distrib

lemma one_mem' : 1 ∈ ValidCube := by
    simp [ValidCube]
    apply And.intro
    { apply Eq.refl }
    { apply And.intro
      { apply Eq.refl }
      { apply Eq.refl } }

lemma inv_mem' {x : RubiksSuperType} : x ∈ ValidCube → x⁻¹ ∈ ValidCube := by
  intro hxv
  simp [ValidCube, PieceState.inv_def, ps_inv]
  repeat' apply And.intro
  { apply hxv.left }
  { sorry }
  { sorry }

/- Defining the subgroup of valid Rubik's cube positions. -/
instance RubiksGroup : Subgroup RubiksSuperType := {
  carrier := ValidCube
  mul_mem' := mul_mem'
  one_mem' := one_mem'
  inv_mem' := inv_mem'
}

/- Defining the intuitively valid set of Rubik's cube positions. -/
inductive Reachable : RubiksSuperType → Prop where
  | Solved : Reachable Solved
  | FT : ∀x : RubiksSuperType, FaceTurn x → Reachable x
  | mul : ∀x y : RubiksSuperType, Reachable x → Reachable y → Reachable (x * y)

end RubiksGroup

/- The widget below was adapted from kendfrey's repository. -/
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
  fun i o cube => (corner_map.get (cube.1.permute⁻¹ i)).get (Fin.sub o (cube.1.orient i))

def edge_sticker : Fin 12 → Fin 2 → RubiksSuperType → Color :=
  fun i o cube => (edge_map.get (cube.2.permute⁻¹ i)).get (Fin.sub o (cube.2.orient i))

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

/- Useful predicates for the SolutionAlgorithm, as well as for some minor proofs. -/
section SolutionState

def CornersSolved : RubiksSuperType → Prop :=
  fun c => c.fst.permute = 1 ∧ c.fst.orient = 0

def EdgesSolved : RubiksSuperType → Prop :=
  fun c => c.snd.permute = 1 ∧ c.snd.orient = 0

def IsSolved : RubiksSuperType → Prop := fun c => CornersSolved c ∧ EdgesSolved c

instance {c} : Decidable (CornersSolved c) := by apply And.decidable
instance {c} : Decidable (EdgesSolved c) := by apply And.decidable
instance {c} : Decidable (IsSolved c) := by apply And.decidable

end SolutionState
