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
      simp only [R, ValidCube]
      apply And.intro
      { apply Eq.refl }
      { apply And.intro
        · exact rfl
        · rfl
      }
      done


  lemma ft_valid
  : ∀x : RubiksSuperType,
  FaceTurn x → x ∈ ValidCube
  :=
    by
      intro x hx
      -- cases hx with
      -- | _ =>
        -- 能证明但是很慢。分开写快一点？：
        -- method 1:
        -- simp only [ValidCube, U, D, R, L, F, B, U2, D2, R2, L2, F2, B2, U', D', R', L', F', B']
        -- repeat' apply And.intro
        -- all_goals apply Eq.refl
        --------------
        -- method 2:
        -- simp only [ValidCube, U, D, R, L, F, B, U2, D2, R2, L2, F2, B2, U', D', R', L', F', B']
        -- <;> apply And.intro;apply Eq.refl;exact Prod.mk_eq_zero.mp rfl
        -- done
        -- sorry
      --- method 3:
      -- cases hx with
      -- | U =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | D =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | R =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | L =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | F =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | B =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | U2 =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | D2 =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | R2 =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | L2 =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | F2 =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | B2 =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | U' =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | D' =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | R' =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | L' =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | F' =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      -- | B' =>
      --   apply And.intro
      --   { apply Eq.refl }
      --   { apply And.intro
      --     · exact rfl
      --     · rfl
      --   }
      sorry
      done


  lemma TPermValid : TPerm ∈ ValidCube :=
    by
      simp only [TPerm]
      repeat apply RubiksGroup.mul_mem'
      all_goals apply ft_valid
      { apply FaceTurn.R } -- 这下面包括这行都是根据定义来的。
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
      done


  lemma CornerTwistInvalid : CornerTwist ∉ ValidCube
  := by
      simp only [CornerTwist, ValidCube]
      simp only [Fin.zero_eta, imp_false, Finset.mem_singleton, Finset.mem_insert, zero_ne_one,
        false_or, Set.mem_setOf_eq, map_one, forall_true_left, Pi.zero_apply, Finset.sum_const_zero,
        and_true, true_and]
      exact Fin.pos_iff_ne_zero.mp Nat.le.refl
      done

  lemma EdgeFlipInvalid : EdgeFlip ∉ ValidCube :=
    by
      simp only [EdgeFlip, ValidCube]
      simp only [Set.mem_setOf_eq, map_one, Pi.zero_apply, Finset.sum_const_zero, true_and]
      exact Fin.exists_succ_eq.mp (Exists.intro { val := Nat.zero, isLt := Nat.le.refl } rfl)
      done

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
: ∀x : RubiksSuperType, x ∈ ValidCube → Reachable x
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
lemma four_rs_eq_solved
: (R * R * R * R) = Solved
:= by
  simp only [R, Solved]
  simp only [Prod.mk_mul_mk, PieceState.mul_def, ps_mul_assoc, Prod.mk_eq_one]
  simp only [ps_mul]
  simp only [Prod.mk.injEq, PieceState.mk.injEq]
  simp only [cyclePieces,cycleImpl]
  apply And.intro
  · simp only [mul_one, coe_mul, coe_fn_mk]
    apply And.intro
    · ext i
      simp only [coe_mul, Function.comp_apply, coe_one, id_eq]

      -- 这里也是经过1到8检验，都会变回本身。
  -- ring_nf
  -- 如何让lean4简化这些permute的运算呢？
  -- aesop

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

-- -- 这个也是类似“four_rs_eq_solved”的证明，虽然也没给出，这里就不证明了
-- lemma four_rs_solved :
-- IsSolved (R * R * R * R)
-- := by
--   simp only [R, IsSolved, CornersSolved, EdgesSolved, Solved]
--   repeat (all_goals apply And.intro)
--   { simp only [cyclePieces, cycleImpl, PieceState.mul_def, ps_mul, Equiv.Perm.permGroup.mul_assoc]
--     -- have h : swap 1 6 * (swap 6 5 * swap 5 2) *
--     -- (swap 1 6 * (swap 6 5 * swap 5 2) * (swap 1 6 * (swap 6 5 * swap 5 2) * (swap 1 6 * (swap 6 5 * swap 5 2)))) = swap 1 6 * swap 6 5 * swap 5 2 *
--     -- swap 1 6 * swap 6 5 * swap 5 2 * swap 1 6 * swap 6 5 * swap 5 2 * swap 1 6 * swap 6 5 * swap 5 2 := by apply
--     sorry }
--   { simp [cyclePieces, cycleImpl, PieceState.mul_def, ps_mul, Orient]
--     sorry }
--   { sorry }
--   { sorry }

-- #check Equiv.Perm.permGroup.mul_assoc
