import RubiksCube.RubiksCubeFunc
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Equiv Perm
-- set_option maxHeartbeats 4000000

/- NOTE: ft_valid and reachable_valid will take a moment for Lean to process. -/
-- 怎么缩短时间呢？

section ValidityChecks

  --例子：
  lemma RValid : R ∈ ValidCube :=
    by
      simp [R, ValidCube]
      apply And.intro
      { apply Eq.refl }
      { apply Eq.refl }

  lemma ft_valid
  : ∀x : RubiksSuperType,
  FaceTurn x → x ∈ ValidCube
  :=
    by
      intro x hx
      cases hx with
      | _ =>
        -- 能证明但是很慢。分开写快一点？：
        -- method 1:
        -- simp [ValidCube, U, D, R, L, F, B, U2, D2, R2, L2, F2, B2, U', D', R', L', F', B']
        -- repeat' apply And.intro
        -- all_goals apply Eq.refl
        --------------
        -- method 2:
        -- simp only [ValidCube, U, D, R, L, F, B, U2, D2, R2, L2, F2, B2, U', D', R', L', F', B']
        -- <;> apply And.intro;apply Eq.refl;exact Prod.mk_eq_zero.mp rfl
        -- done
        sorry


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

  lemma CornerTwistInvalid : CornerTwist ∉ ValidCube
  := by
      simp only [CornerTwist, ValidCube]
      -- intro h
      simp only [Fin.zero_eta, imp_false, Finset.mem_singleton, Finset.mem_insert, zero_ne_one,
        false_or, Set.mem_setOf_eq, map_one, forall_true_left, Pi.zero_apply, Finset.sum_const_zero,
        and_true, true_and]
      --提示有了，但是还是报错了？
      -- exact
      --   (bne_iff_ne
      --         (Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} fun x ↦
      --           match x with
      --           | { val := 0, isLt := .(Nat.mod_lt 0 Fin.instOfNatFin.proof_1) } => 1
      --           | x => 0)
      --         0).mp
      --     rfl
      sorry
      -- have h2 : ∀x ∈ ({0,1,2,3,4,5,6,7} : Set (Fin 8)), (fun | 0 => 1 | _ => 0) x = 0 := Finset.sum_eq_zero_iff.mp h

  lemma EdgeFlipInvalid : EdgeFlip ∉ ValidCube :=
    by
      simp [EdgeFlip, ValidCube]
      -- 又有提示，但是证明失败：
      -- exact
      --   (bne_iff_ne
      --         (Finset.sum {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} fun x ↦
      --           match x with
      --           | { val := 0, isLt := .(Nat.mod_lt 0 Fin.instOfNatFin.proof_1) } => 1
      --           | x => 0)
      --         0).mp
      --     rfl
      sorry

end ValidityChecks


/- This theorem shows that the set of valid cube states as defined in terms of permutations and orientations of
the pieces contains all positions reachable with standard Rubik's cube moves. Further showing that these
two sets are in fact the same is equivalent to providing a solution algorithm for any valid cube state.
I do not have a proof that the solution algorithm in `SolutionAlgorithm.lean` will solve any valid cube,
but I am confident that this is the case (assuming no bugs in my concretely defined setup moves). -/

-- 魔方第二基本定理的右推左部分：
--todo--

  lemma solved_reachable
  (x : RubiksSuperType)
  (h : x = Solved)
  : Reachable x
  := by
    rw [h]
    exact Reachable.Solved


theorem valid_reachable
:∀x : RubiksSuperType, x ∈ ValidCube → Reachable x
:= by
  intro x hvx
  simp [ValidCube] at hvx
  -- x经过有限次操作变成了y
  set y : RubiksSuperType := sorry
  have h1 : y = Solved := sorry
  -- x经过有限次操作变成了y → Reachable y → Reachable x
  have h2 : Reachable y → Reachable x := sorry
  apply h2
  exact solved_reachable y h1
  done


  -- induction x with
  -- | mk fst snd => sorry

-- 魔方第二基本定理的左推右部分：
theorem reachable_valid
: ∀x : RubiksSuperType, Reachable x → x ∈ ValidCube
:= by
  intro x hrx
  -- cases hrx with
  induction hrx with
  | Solved =>
      simp only [Solved, ValidCube]
      apply And.intro
      { apply Eq.refl }
      { apply And.intro
        { apply Eq.refl }
        { apply Eq.refl } }
  | FT c hc =>
    sorry
    --这里能证明，但是运行很慢：
    -- cases hc with
    -- | _ =>
    --     simp only [ValidCube]
    --     apply And.intro
    --     { apply Eq.refl }
    --     { apply And.intro
    --       { apply Eq.refl }
    --       { apply Eq.refl } }
    --     done
  | mul x y hrx hry a_ih a_ih_1 =>
      -- 归纳证明：
      -- *** 精华在这里，前面写了几百行，就是为了这几行：
      apply RubiksGroup.mul_mem' -- 反推一步，两个元素都是
      simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid]
      exact a_ih
      exact a_ih_1
      -- method 2:
      -- all_goals assumption

/-- 魔方第二基本定理 -/
theorem RubikCubeSecondBasicRule
: ∀x : RubiksSuperType, Reachable x ↔ x ∈ ValidCube
:= by
  intro h
  constructor
  · exact reachable_valid h
  · exact valid_reachable h
  done



-- instance {n : ℕ} {α : Type*} [DecidableEq α] : DecidableEq (Fin n → α) :=
--   fun f g => Fintype.decidablePiFintype f g

--? Why do both of these pause forever?
-- lemma four_rs_eq_solved
-- : (R * R * R * R) = Solved
-- := by
--   simp only [R, Solved]
--   simp only [Prod.mk_mul_mk, PieceState.mul_def, ps_mul_assoc, Prod.mk_eq_one]
--   simp only [ps_mul]
--   simp only [invFun_as_coe, Pi.zero_comp, add_zero]
--   apply And.intro
--   simp only [cyclePieces, cycleImpl]
--   simp only [mul_one]
--   ring_nf
--   -- 如何让lean4简化这些permute的运算呢？
--   aesop

--todo--

lemma solved_is_solved
: IsSolved (Solved)
:= by
  simp only [IsSolved, CornersSolved, EdgesSolved, Solved]
  apply And.intro
  { apply And.intro
    { apply Eq.refl }
    { apply Eq.refl } }
  { apply And.intro
    { apply Eq.refl }
    { apply Eq.refl } }
  done

-- 这个也是类似“four_rs_eq_solved”的证明，虽然也没给出，这里就不证明了
lemma four_rs_solved :
IsSolved (R * R * R * R)
:= by
  simp only [R, IsSolved, CornersSolved, EdgesSolved, Solved]
  repeat (all_goals apply And.intro)
  { simp only [cyclePieces, cycleImpl, PieceState.mul_def, ps_mul, Equiv.Perm.permGroup.mul_assoc]
    -- have h : swap 1 6 * (swap 6 5 * swap 5 2) *
    -- (swap 1 6 * (swap 6 5 * swap 5 2) * (swap 1 6 * (swap 6 5 * swap 5 2) * (swap 1 6 * (swap 6 5 * swap 5 2)))) = swap 1 6 * swap 6 5 * swap 5 2 *
    -- swap 1 6 * swap 6 5 * swap 5 2 * swap 1 6 * swap 6 5 * swap 5 2 * swap 1 6 * swap 6 5 * swap 5 2 := by apply
    sorry }
  { simp [cyclePieces, cycleImpl, PieceState.mul_def, ps_mul, Orient]
    sorry }
  { sorry }
  { sorry }

#check Equiv.Perm.permGroup.mul_assoc
