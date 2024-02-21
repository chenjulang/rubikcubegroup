import RubiksCube.RubiksCubeVector
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Equiv Perm

section ValidityChecks

-- lemma RValid : R ∈ ValidCube :=
--   by
--     simp [R, ValidCube]
--     apply And.intro
--     { apply Eq.refl }
--     { apply Eq.refl }

lemma ft_valid : ∀x : RubiksSuperType, FaceTurn x → x ∈ ValidCube :=
  by
    intro x hx
    cases hx with
    | _ =>
      simp [ValidCube, U, D, R, L, F, B, U2, D2, R2, L2, F2, B2, U', D', R', L', F', B']
      repeat' apply And.intro
      all_goals apply Eq.refl

lemma TPermValid : TPerm ∈ ValidCube :=
  by
    simp [TPerm]
    repeat apply RubiksGroup.mul_mem'
    all_goals apply ft_valid
    { apply FaceTurn.R }
    { apply FaceTurn.U }
    { apply FaceTurn.R' }
    { apply FaceTurn.U' }
    { apply FaceTurn.R' }
    { apply FaceTurn.F }
    { apply FaceTurn.R2 }
    { apply FaceTurn.U' }
    { apply FaceTurn.R' }
    { apply FaceTurn.U' }
    { apply FaceTurn.R }
    { apply FaceTurn.U }
    { apply FaceTurn.R' }
    { apply FaceTurn.F' }

lemma CornerTwistInvalid : CornerTwist ∉ ValidCube :=
  by
    simp [CornerTwist, ValidCube, zeroOrient, Vector.toList, Vector.replicate, Vector.set, List.set]
    exact (bne_iff_ne 3 1).mp (by rfl)

lemma EdgeFlipInvalid : EdgeFlip ∉ ValidCube :=
  by
    simp [EdgeFlip, ValidCube, zeroOrient, Vector.toList, Vector.replicate, Vector.set, List.set]
    exact (bne_iff_ne 2 1).mp (by rfl)

end ValidityChecks

theorem reachable_valid : ∀x : RubiksSuperType, Reachable x → x ∈ ValidCube := by
  intro x hrx
  induction hrx with
  | Solved =>
      simp [Solved, ValidCube]
      apply And.intro
      { apply Eq.refl }
      { apply And.intro
        { apply Eq.refl }
        { apply Eq.refl } }
  | FT c hc =>
      cases hc with
      | _ =>
          simp [ValidCube]
          apply And.intro
          { apply Eq.refl }
          { apply And.intro
            { apply Eq.refl }
            { apply Eq.refl } }
  | mul x y hrx hry a_ih a_ih_1 =>
      apply RubiksGroup.mul_mem'
      all_goals assumption

lemma solved_is_solved : IsSolved (Solved) := by
  simp [IsSolved, CornersSolved, EdgesSolved, Solved]
  apply And.intro
  { apply And.intro
    { apply Eq.refl }
    { apply Eq.refl } }
  { apply And.intro
    { apply Eq.refl }
    { apply Eq.refl } }

-- set_option maxHeartbeats 50000

lemma four_rs_solved : IsSolved (R * R * R * R) := by
  simp [R, IsSolved, CornersSolved, EdgesSolved, Solved, orientVector, zeroOrient]
  repeat (all_goals apply And.intro)
  { simp [cyclePieces, cycleImpl, PieceState.mul_def, ps_mul, Equiv.Perm.permGroup.mul_assoc]
    -- have h : swap 1 6 * (swap 6 5 * swap 5 2) *
    -- (swap 1 6 * (swap 6 5 * swap 5 2) * (swap 1 6 * (swap 6 5 * swap 5 2) * (swap 1 6 * (swap 6 5 * swap 5 2)))) = swap 1 6 * swap 6 5 * swap 5 2 *
    -- swap 1 6 * swap 6 5 * swap 5 2 * swap 1 6 * swap 6 5 * swap 5 2 * swap 1 6 * swap 6 5 * swap 5 2 := by apply
    sorry }
  { simp [cyclePieces, cycleImpl, PieceState.mul_def, ps_mul]
    sorry }
  { sorry }
  { sorry }

#check Equiv.Perm.permGroup.mul_assoc
