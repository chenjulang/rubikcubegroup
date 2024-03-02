import RubiksCube.RubiksCubeFunc
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Alternating

open Equiv Perm
open Equiv Equiv.Perm Subgroup Fintype
open alternatingGroup
-- set_option maxHeartbeats 4000000

/- NOTE: ft_valid and reachable_valid will take a moment for Lean to process. -/
-- 怎么缩短时间呢？

variable (α : Type*) [Fintype α] [DecidableEq α]


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
      -- done


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


  lemma solved_reachable
  (x : RubiksSuperType)
  (h : x = Solved)
  : Reachable x
  := by
    rw [h]
    exact Reachable.Solved

  lemma lemma1
  : ∀g : RubiksSuperType,
  Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0
  →
  ∃ h ∈ RubiksGroup ,
  (g * h).fst.orient = 0
  := by sorry

  lemma lemma2
  : ∀g : RubiksSuperType,
  Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.snd.orient = 0
  →
  ∃ h ∈ RubiksGroup ,
  (g * h).snd.orient = 0
  := by sorry


  -- 定理：closure_three_cycles_eq_alternating
  -- 定义：3循环： IsThreeCycle
  -- 通用小引理4.6：假设n>=3，对于任意集合M，假设M包含Sn中全体3循环，则=>， M >= An
  lemma lemma4_6
  (M:Subgroup (Perm α)):
  ∀ σ:Perm α,
    IsThreeCycle σ
    ∧
    σ ∈ M
  →
  sorry
  -- alternatingGroup α ⊂ M
  -- failed to synthesize instance HasSSubset (Subgroup (Perm α))
  := by sorry

  -- 好像写错了，先不纠结,应该写成参数好一点
  lemma lemma3_1
  :∃ g : RubiksSuperType,
  Reachable g
  ∧
  ∀ x : RubiksSuperType,
  IsThreeCycle x.1.permute
  ∧
  x.2.permute = 1
  ∧
  x.1.orient = 0
  ∧
  x.2.orient = 0
  →
  x * g = Solved
  := by sorry

  lemma lemma3_2
  :∃ g : RubiksSuperType,
  Reachable g
  ∧
  ∀ x : RubiksSuperType,
  IsThreeCycle x.2.permute
  ∧
  x.1.permute = 1
  ∧
  x.1.orient = 0
  ∧
  x.2.orient = 0
  →
  x * g = Solved
  := by sorry

  lemma lemma11
  :∃ g : RubiksSuperType,
  Reachable g
  ∧
  ∀ x : RubiksSuperType,
  IsThreeCycle x.2.permute
  ∧
  IsThreeCycle x.1.permute
  ∧
  x.1.orient = 0
  ∧
  x.2.orient = 0
  →
  x * g = Solved
  := by sorry

  /-- 1.（奇X奇) 2.(偶X偶）-/
  lemma condition1_restriction
  (x:RubiksSuperType)
  (h1:x ∈ ValidCube)
  :sign x.1.permute = sign x.2.permute
  ↔
  (sign x.1.permute = -1 ∧ -1 = sign x.2.permute)
  ∨
  (sign x.1.permute = 1 ∧ 1 = sign x.2.permute)
  := by sorry

  /-- （奇X奇) → (偶X偶）-/
  lemma oddXoddToEvenXEven
  (g:RubiksSuperType)
  (h1:Reachable g)
  :∀ x:RubiksSuperType,
  Reachable x
  ∧
  (sign x.1.permute = -1 ∧ -1 = sign x.2.permute)
  →
  (sign (g * x).1.permute = 1 ∧ 1 = sign (g * x).2.permute)
  := by sorry

-- 线索：1.mathlib的group theory 2.人工智能POE和AGI 3.MIL+其他课程+北大-关于群的描述
-- Alternating.lean
-- todo--
-- failed to synthesize 的问题通过再看一次北大的课应该可以解决。

-- 魔方第二基本定理的右推左部分：
theorem valid_reachable
: ∀x : RubiksSuperType, x ∈ ValidCube → Reachable x
:= by
  intro x hvx
  simp [ValidCube] at hvx
  -- 分类讨论1得到小引理1：假设有状态g∈H,且∑(8在上 i=1) vi(g) = 0 (mod 3),则=>, g能通过有限次作用G中的元素，得到新的性质：v(g)={0,0,...,0}。而且不改变棱块的方向数。
  -- 分类讨论2得到小引理2:假设有状态g∈H,且∑(12在上 i=1) wi(g) = 0 (mod 2) ， 则=>,g能通过有限次作用G中的元素，得到新的性质：w(g)={0,0,...,0}。并且不改变角块的方向数。
  -- 通用小引理4.6：假设n>=3，对于任意集合M，假设M包含Sn中全体3循环，则=>， M >= An
  -- 小引理3***(最复杂的一个引理): 从已知的某些复合操作，能够覆盖所有的棱3循环和角3循环（不改变棱和角的方向数）。
  -- 小引理11：由于小引理3，已覆盖所有3循环，再使用小引理4.6，因此可以得到 => 从已知的某些复合操作，能达到这个状态集合({A8},{A12},id,id)
  -- ValidCube的条件1，限制了当前状态x的范围，所以可以进行2种分类讨论：1.（奇X奇) 2.(偶X偶）
  -- 存在一个复合操作，作用一次到状态集合（奇X奇)上的某个元素后，新状态会属于新的状态集合(偶X偶）

  -- 以下就不是引理了，直接四行推理了：
  -- 因为对x的2种分类讨论都归化到了状态集合(偶X偶），即({A8},{A12},?,?)
  -- ValidCube的条件2, 然后使用小引理1，可以将({A8},{A12},?,?) 变成 ({A8},{A12},0,?)
  -- ValidCube的条件3, 然后使用小引理2，可以将({A8},{A12},0,?) 变成 ({A8},{A12},0,0)， 即({A8},{A12},id,id)
  -- 以上操作已经将状态x变成了这个状态集合里的某一个({A8},{A12},id,id)，因此直接使用小引理11，就可以直接证明x可以被复合得到。

  -- x经过有限次操作变成了y， y就是复原状态e。
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
  -- done

/-- 魔方第二基本定理 -/
theorem RubikCube_BasicRule_2
: ∀x : RubiksSuperType, Reachable x ↔ x ∈ ValidCube
:= by
  intro h
  constructor
  · exact reachable_valid h
  · exact valid_reachable h
  done



-- instance {n : ℕ} {α : Type*} [DecidableEq α] : DecidableEq (Fin n → α) :=
--   fun f g => Fintype.decidablePiFintype f g

def swaptest :Perm (Fin 8) := (swap 1 2) * (swap 2 6) * (swap 6 5)*(swap 1 2)*(swap 2 6)*(swap 6 5)*(swap 1 2)*
 (swap 2 6) * (swap 6 5) * (swap 1 2) * (swap 2 6) * (swap 6 5)
lemma computeSwapTest (i:Fin 8): swaptest i = i
  := by fin_cases i <;> rfl
lemma SwapDef (i: Fin 8): ((swap 1 2)
      ((swap 2 6)
        ((swap 6 5)
          ((swap 1 2)
            ((swap 2 6)
              ((swap 6 5) ((swap 1 2) ((swap 2 6) ((swap 6 5) ((swap 1 2) ((swap 2 6) ((swap 6 5) i)))))))))))) = i
  := by fin_cases i <;> rfl
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
      have h1 := SwapDef i
      -- swapTest2_1
      sorry
      -- done
    · -- orientTest2_1
      sorry
      -- done
  · simp only [mul_one, coe_mul]
    apply And.intro
    · ext i
      simp only [coe_mul, Function.comp_apply, coe_one, id_eq]
      -- swapTest2_2
      sorry
      -- done
    · -- orientTest2_2
      sorry
      -- done
  -- done

-- def swapTest2_1 :Perm (Fin 8) := (swap 1 2) * (swap 2 6) * (swap 6 5)*(swap 1 2)*(swap 2 6)*(swap 6 5)*(swap 1 2)*
--  (swap 2 6) * (swap 6 5) * (swap 1 2) * (swap 2 6) * (swap 6 5)
-- def swapTest2_2 :Perm (Fin 12) := (swap 1 6)*(swap 6 9)*(swap 9 5)*(swap 1 6)*(swap 6 9)*(swap 9 5)*(swap 1 6)*(swap 6 9)*(swap 9 5)*
--   (swap 1 6)*(swap 6 9)*(swap 9 5)
-- def swapTest2 :Perm (Fin 12) := (swap 1 6)*(swap 6 9)*(swap 9 5)*(swap 1 6)*(swap 6 9)*(swap 9 5)*(swap 1 6)*(swap 6 9)*(swap 9 5)*
--   (swap 1 6)*(swap 6 9)*(swap 9 5)
-- #eval swapTest2 0 -- 0
-- #eval swapTest2 1 -- 1
-- #eval swapTest2 2 -- 2
-- #eval swapTest2 3 -- 3
-- #eval swapTest2 4 -- 4
-- #eval swapTest2 5 -- 5
-- #eval swapTest2 6 -- 6
-- #eval swapTest2 7 -- 7
-- #eval swapTest2 8 -- 8
-- #eval swapTest2 9 -- 9
-- #eval swapTest2 10 -- 10
-- #eval swapTest2 11 -- 11
-- def orientTest2_1 : Fin 8 → Fin 3 := ((Orient 8 3 [(1, 2), (2, 1), (5, 1), (6, 2)] ∘ ⇑(swap 1 2) ∘ ⇑(swap 2 6) ∘ ⇑(swap 6 5) +
--             Orient 8 3 [(1, 2), (2, 1), (5, 1), (6, 2)]) ∘
--           ⇑(swap 1 2) ∘ ⇑(swap 2 6) ∘ ⇑(swap 6 5) +
--         Orient 8 3 [(1, 2), (2, 1), (5, 1), (6, 2)]) ∘
--       ⇑(swap 1 2) ∘ ⇑(swap 2 6) ∘ ⇑(swap 6 5) +
--     Orient 8 3 [(1, 2), (2, 1), (5, 1), (6, 2)]
-- def orientTest2_2 : Fin 12 → Fin 2 := ((Orient 12 2 [(1, 1), (5, 1), (6, 1), (9, 1)] ∘ ⇑(swap 1 6) ∘ ⇑(swap 6 9) ∘ ⇑(swap 9 5) +
--             Orient 12 2 [(1, 1), (5, 1), (6, 1), (9, 1)]) ∘
--           ⇑(swap 1 6) ∘ ⇑(swap 6 9) ∘ ⇑(swap 9 5) +
--         Orient 12 2 [(1, 1), (5, 1), (6, 1), (9, 1)]) ∘
--       ⇑(swap 1 6) ∘ ⇑(swap 6 9) ∘ ⇑(swap 9 5) +
--     Orient 12 2 [(1, 1), (5, 1), (6, 1), (9, 1)]
-- def orientTest2 : Fin 12 → Fin 2 := ((Orient 12 2 [(1, 1), (5, 1), (6, 1), (9, 1)] ∘ ⇑(swap 1 6) ∘ ⇑(swap 6 9) ∘ ⇑(swap 9 5) +
--             Orient 12 2 [(1, 1), (5, 1), (6, 1), (9, 1)]) ∘
--           ⇑(swap 1 6) ∘ ⇑(swap 6 9) ∘ ⇑(swap 9 5) +
--         Orient 12 2 [(1, 1), (5, 1), (6, 1), (9, 1)]) ∘
--       ⇑(swap 1 6) ∘ ⇑(swap 6 9) ∘ ⇑(swap 9 5) +
--     Orient 12 2 [(1, 1), (5, 1), (6, 1), (9, 1)]
-- #eval orientTest2 0 -- 0
-- #eval orientTest2 1 -- 0
-- #eval orientTest2 2 -- 0
-- #eval orientTest2 3 -- 0
-- #eval orientTest2 4 -- 0
-- #eval orientTest2 5 -- 0
-- #eval orientTest2 6 -- 0
-- #eval orientTest2 7 -- 0
-- #eval orientTest2 8 -- 0
-- #eval orientTest2 9 -- 0
-- #eval orientTest2 10 -- 0
-- #eval orientTest2 11 -- 0


lemma solved_is_solved
: IsSolved (Solved)
:= by
  simp only [IsSolved, CornersSolved, EdgesSolved, Solved]
  apply And.intro
  { simp only [and_self] }
  { simp only [and_self]}
  done

lemma four_rs_solved :
IsSolved (R * R * R * R)
:= by
  have h1:= four_rs_eq_solved
  rw [h1]
  exact solved_is_solved

-- #check Equiv.Perm.permGroup.mul_assoc







------ 以下是TW算法部分，(因为新开一个文件有问题)：
------ 每一个证明的右推左部分，其实就是还原的算法！！！
------
------
------
-- 三个降群的充要条件的证明
-- 1.∀g∈ G,
-- g∈G1 (G1 = <L^2,R^2,F,B,U,D>)
-- ↔
-- wi(g)=0 , ∀i , 1<=i<=12
def TWGroup1 :
  Set RubiksSuperType
  :=
  -- 这样的一个集合：所有满足后面这些条件的c
  {
    c |
    c ∈ RubiksGroup
    ∧
    c.2.orient = 0
  }

instance TWGroup1_instance : Subgroup RubiksSuperType := {
-- 如何写成这样的子群的子群呢 ??? instance TWGroup1_instance : Subgroup RubiksGroup := {
    carrier := TWGroup1
    mul_mem' := sorry -- 封闭性质
    one_mem' := sorry -- 单位1元素
    inv_mem' := sorry -- 逆元素
    -- 结合律不用证明，父群已经证明。
    -- 左乘1=本身不用证明
    -- 右乘1=本身不用证明
    -- 左乘逆=1不用证明
    -- 右乘逆=1不用证明
}
lemma TWGroup1_isSubGroupOf_RubiksGroup :
TWGroup1 ⊂ RubiksGroup := by sorry

theorem TWAlgorithm_TWGroup1_iff
: ∀x : RubiksSuperType, Reachable_TWGroup1 x ↔ x ∈ TWGroup1
:= by sorry

-- 2.∀g∈ G1,
-- g∈G2 (G2 = <L^2,R^2,F^2,B^2,U,D>)
-- ↔
-- {
--     1. vi(g)=0 , ∀i , 1<=i<=8
--     2. 棱块有1个保持轨道:意思是，σ(g)作用到 {5,6,7,8}这4个棱块后，这4个棱块仍然全都在位置{5,6,7,8}上，
--         换句话说，这4个棱块经过g变换后保持在（上下）中层里。
-- }
def remainsEdgeOrbit :RubiksSuperType → (List ℕ) → Prop := sorry
def remainsCornerOrbit :RubiksSuperType → (List ℕ) → Prop := sorry

def TWGroup2 :
  Set RubiksSuperType
  :=
  -- 这样的一个集合：所有满足后面这些条件的c
  {
    c |
    c ∈ RubiksGroup
    ∧
    c.2.orient = 0
    ∧
    c.1.orient = 0
    ∧
    remainsEdgeOrbit c {4,5,6,7}
  }

instance TWGroup2_instance : Subgroup RubiksSuperType := {
    carrier := TWGroup2
    mul_mem' := sorry -- 封闭性质
    one_mem' := sorry -- 单位1元素
    inv_mem' := sorry -- 逆元素
    -- 结合律不用证明，父群已经证明。
    -- 左乘1=本身不用证明
    -- 右乘1=本身不用证明
    -- 左乘逆=1不用证明
    -- 右乘逆=1不用证明
}
lemma TWGroup2_isSubGroupOf_TWGroup1 :
TWGroup2 ⊂ TWGroup1 := by sorry

theorem TWAlgorithm_TWGroup2_iff
: ∀x : RubiksSuperType, Reachable_TWGroup2 x ↔ x ∈ TWGroup2
:= by sorry

-- 3.∀g∈ G2,
-- g∈ G3 (<L^2,R^2,F^2,B^2,U^2,D^2>)
-- ↔
-- {
--     1.棱块有2个新的保持轨道：{1,3,9,11},{2,4,10,12}，当然也有G2就有的{5,6,7,8}
--     2.角块有2个保持轨道：{1,3,6,8},{2,4,5,7}
--     3.与这个白色面心块颜色不一样的角块的个数,记为Count,Count是偶数。这里先特指白色面中，和白色不一样的角块的（白色的）个数Count，Count是偶数个。
-- }
  -- 有一个额外的左推右的条件可以证明：
  --    (3错误的？.{1,3,6,8},{2,4,5,7}这两个角块的轨道中，不包含三轮换。
  --     换句话说，g的效果不能产生这些轨道内的3循环。
  --      换句话说，g不是单纯的棱块3循环（不变全体块的方向数，不变角块的位置）)

def TWGroup3 :
  Set RubiksSuperType
  :=
  -- 这样的一个集合：所有满足后面这些条件的c
  {
    c |
    c ∈ RubiksGroup
    ∧
    c.2.orient = 0
    ∧
    c.1.orient = 0
    ∧
    remainsEdgeOrbit c {4,5,6,7} ∧ remainsEdgeOrbit c {0,2,8,10} ∧ remainsEdgeOrbit c {1,3,9,11}
    ∧
    remainsCornerOrbit c {0,2,5,7} ∧ remainsCornerOrbit c {1,3,4,6}
    -- todo 这里先特指白色面中，和白色不一样的角块的（白色的）个数Count，Count是偶数个。
    -- 集合{1-8}（根据c.1.permute来分析）中,位于前4个位置中，数一下1-4的个数，这个个数为Even。
  }

instance TWGroup3_instance : Subgroup RubiksSuperType := {
    carrier := TWGroup3
    mul_mem' := sorry -- 封闭性质
    one_mem' := sorry -- 单位1元素
    inv_mem' := sorry -- 逆元素
    -- 结合律不用证明，父群已经证明。
    -- 左乘1=本身不用证明
    -- 右乘1=本身不用证明
    -- 左乘逆=1不用证明
    -- 右乘逆=1不用证明
}
lemma TWGroup3_isSubGroupOf_TWGroup2 :
TWGroup3 ⊂ TWGroup2 := by sorry

theorem TWAlgorithm_TWGroup3_iff
: ∀x : RubiksSuperType, Reachable_TWGroup3 x ↔ x ∈ TWGroup3
:= by sorry
