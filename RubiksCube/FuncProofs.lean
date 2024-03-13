import RubiksCube.RubiksCubeFunc
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Alternating

open Equiv Perm
open Equiv Equiv.Perm Subgroup Fintype
open alternatingGroup
open BigOperators
-- set_option maxHeartbeats 4000000

-- 注意：依赖文件RubiksCubeFunc改过的话，最好点一下这个文件的restrt File
-- 线索：1.mathlib的group theory 2.人工智能POE和AGI 3.MIL+其他课程+北大-关于群的描述
-- Alternating.lean



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


section RubikCube_BasicRule_2

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

  def G1Perm_element : RubiksSuperType
  := R' * D * D * R * B' * U * U * B
  /-- g1:
  方向：UFR和DBL以外的块的方向不变。
  位置：UFR和DBL以外的块的位置不变。
  可以保持UFR和DBL以外的块的方向和位置，只改变UFR和DBL的方向，
  分别是UFR的方向数+2，DBL的方向数+1。 -/
  def G1Perm : RubiksSuperType
  := G1Perm_element^2
  -- #eval G1Perm
--   ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 2, 0, 0, 0, 0, 0, 1] },
--  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })

  def UFL_index :Fin 8 := 0
  def UFR_index :Fin 8 := 1
  def UBR_index :Fin 8 := 2
  def UBL_index :Fin 8 := 3
  def DFL_index :Fin 8 := 4
  def DFR_index :Fin 8 := 5
  def DBR_index :Fin 8 := 6
  def DBL_index :Fin 8 := 7

    --Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} g.1.orient = 0
    -- → Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * F * G1Perm * F').1.orient = 0
    -- 这个结论是一个计算的结果吧？
    lemma lemma1_006
    (g:RubiksSuperType)
    :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} g.1.orient = 0
    →
    Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * F * G1Perm * F').1.orient = 0
    := by
      intro h1
      sorry

    -- 又是一个需要计算的结论，可以用calc模式吗？
    lemma lemma1_005
    :∀g : RubiksSuperType,
    (Corner_Absolute_Orient g.1 UFL_index) = 1
    →
    (Corner_Absolute_Orient (g*F*G1Perm*F').1 UFL_index) = 0
    := by
      sorry

    -- 这个引理要一般性一点：g和i如果中途相隔一个G中的元素h，也就是gh=i，则某个旧目标g可以达到，可以变成新目标i可以达到。
    -- 一个举例：
    -- g∈ RubiksSuperType, h ∈ RubiksGroup,-- 大前提
    -- (∃ x1 ∈ RubiksGroup, ((g) * x1).1.orient = 0)
    -- →
      -- (∃ x2 ∈ RubiksGroup, ((g*h) * x2).1.orient = 0)
      -- ∧
      -- ((g*h) * (h⁻¹*x1)).1.orient = 0
    -- 另一个例子：
    -- g∈ RubiksSuperType, h ∈ RubiksGroup,-- 大前提
    -- (∃ x1 ∈ RubiksGroup, ((g) * x1).1.orient有且仅有4个分量是0 )
    -- →
      -- (∃ x2 ∈ RubiksGroup, ((g*h) * x2).1.orient有且仅有4个分量是0)
      -- ∧
      -- ((g*h) * (h⁻¹*x1)).1.orient有且仅有4个分量是0
    -- g和i如果中途相隔一个G中的元素h，也就是gh=i，则某个旧目标g可以达到，可以变成新目标i可以达到。
    -- 一般的例子：
    -- g∈ RubiksSuperType, h ∈ RubiksGroup,-- 大前提
    -- (∃ x1 ∈ RubiksGroup, ((g) * x1)作为参数插入某个命题A成立 )
    -- →
      -- (∃ x2 ∈ RubiksGroup, ((g*h) * x2)作为参数插入命题A成立)
      -- ∧
      -- ((g*h) * (h⁻¹*x1))作为参数插入命题A成立
    lemma lemma1_004_2reachableMove_Exist_same_property
    (g : RubiksSuperType)
    (gInG : g ∈ RubiksGroup)
    (h : RubiksSuperType)
    (somePropA : RubiksSuperType →  Prop)
    :
    ∃ x1:RubiksSuperType,
    somePropA (g*h) -- “冒号”写成“属于号”就不行了，请注意
    →
      (∃ x2 ∈ RubiksGroup, somePropA ((g*h) * x2))
      ∧
      somePropA ((g*h) * (h⁻¹*x1))
    := by
      sorry

    -- 假设角块的方向数求和后，模3为0,假设8个角块的方向数中，有7个方向数被以上步骤还原为0以后，则=>,第8个角块的方向数也还原成0 ，为什么呢？：
    -- 其实这里隐藏了一些条件，“以上步骤”里面每一个操作必须保持某个性质才行。
    -- 还原操作涉及到的只有{F，B和g1},由于这3者之一，任意取一个记为X,都满足∑(8 i=1)v(X)_i=0 (mod 3)：
    --     F和B通过查v表可知，
    --     而g1则只需实际操作一次后，看到只修改了全体角块中2个角块的方向数，而且方向数一个+1，一个+2，所以也满足求和模3为0。
    -- 换句话说，初始状态经过上述{F，B和g1}任意操作后，增加v(X)的各个分量，因为每次操作变化后求和仍然是mod 3为0，因此还原7个以后仍然保持这个性质。
    --
    -- 命题描述就是：
    -- 某状态g满足角方向数求和模3为0（其实等价于：角方向数增加量求和为0），
    -- 经过集合A（满足角方向数增加量求和为0）中的任意复合操作x1后，
    -- 且如果(g*x1)的角方向数增加量的前7个分量都为0，
    -- 则第8个分量也为0。
    -- expected token 这种错误可能是没open这个符号，比如求和∑,要open BigOperators
    lemma lemma1_003_7Corners_eq_8Corners
    (g : RubiksSuperType)
    (SetA : Set RubiksSuperType := {a: RubiksSuperType | ∑ i in (Finset.range 8), (a.1.orient) i = 0})
    (x1: RubiksSuperType)
    :∑ i in (Finset.range 8), (g.1.orient) i = 0
    ∧
    x1 ∈ SetA
    ∧
    ∀ j : (Fin 7), (g*x1).1.orient j = 0 -- 注意：当这3个符号报错时 :,∈,in 三个都轮流试一下。
    →
    (g*x1).1.orient 7 = 0
    := sorry

    -- ...这里省略了所有角块的引理lemma1_00X还没写,后面写成lemma1_002_3,lemma1_002_4这样吧。
    lemma lemma1_002_DFL
    : ∀g : RubiksSuperType, -- RubiksSuperType即手写的H。
    Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0 --角块方形数求和后，模3为0。
    ∧ (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0
    →
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    := by sorry

    -- 任意H中的状态，满足角块方向数求和后模3为0,UFL的方向数为0
      -- 则=>存在G中操作h，(g*h)还原所有角块的方向数，且不改变全体棱块的方向数，且不改变所有块的位置。
    lemma lemma1_001_UFL
    (g : RubiksSuperType) -- RubiksSuperType即文字证明中的H。
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0) --角块方形数求和后，模3为0。
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
     ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    := by sorry
      -- intro g hs
      -- have hsum0 := hs.1
      -- have UFL0 := hs.2
      -- let h := Solved;
      -- by_cases ha0 : (Corner_Absolute_Orient g.1 DFL_index)=0
      -- {
      --   let h := h;
      --   exact lemma1_002 g { left := hsum0, right := { left := UFL0, right := ha0 } }
      -- }
      -- { by_cases (g.1.orient DFL_index)=1
      --   {
      --     sorry
      --   }
      --   {
      --     sorry
      --   }
      -- }


  #eval F*G1Perm*F'
  #eval F*(G1Perm^2)*F'

  -- 任意H中的状态，满足角块方向数求和后模3为0,
    -- 则=>存在G中操作h，(g*h)还原所有角块的方向数，且不改变全体棱块的方向数，且不改变所有块的位置。
  lemma lemma1
  : ∀g : RubiksSuperType, -- RubiksSuperType即手写的H。
  Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0 --角块方形数求和后，模3为0。
  →
  ∃ h ∈ RubiksGroup ,
  (g * h).fst.orient = 0
  ∧
  (g).2.orient = (g * h).2.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  := by
    intro g hsum0
    let h := Solved
    by_cases ha0 : (Corner_Absolute_Orient g.1 UFL_index)=0
    {
      let moveAction1 := Solved
      have h1 := lemma1_001_UFL g hsum0 ha0
      use Solved
      apply And.intro
      {exact { left := rfl, right := { left := rfl, right := rfl } }}
    }
    { by_cases ha1: (Corner_Absolute_Orient g.1 UFL_index) = 1
      { let moveAction2 := F*G1Perm*F'
        -- #eval F*G1Perm*F'
        -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![2, 0, 0, 0, 0, 0, 0, 1] },
        -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
        -- 如何说明g*moveAction2满足这个呢？：(Corner_Absolute_Orient (g*moveAction2).1 UFL_index) = 0
          -- 也就是要证明：UFL方向数为1,操作后为0.
        -- 关键引理证明1
        have h2_1: (g.1.orient + moveAction2.1.orient ∘ g.1.permute) (g.1.permute⁻¹ UFL_index)
        = g.1.orient (g.1.permute⁻¹ UFL_index) + moveAction2.1.orient (UFL_index)
        := by
          simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Pi.add_apply,
            Function.comp_apply, apply_inv_self]
          done
        simp only [Corner_Absolute_Orient] at ha1
        simp at ha1
        -- 关键引理证明2
        have h2_2: g.1.orient (g.1.permute⁻¹ UFL_index) + moveAction2.1.orient (UFL_index) = 0
        := by
          simp only [Inv.inv]
          rw [ha1]
          simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc]
          have h2_2_1: (ps_mul F.1 (ps_mul G1Perm.1 F'.1)).orient UFL_index = 2
          := by rfl
          rw [h2_2_1]
          rfl
          done
        have h2: (Corner_Absolute_Orient (g*moveAction2).1 UFL_index) = 0
        := by
          simp only [Corner_Absolute_Orient]
          simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, invFun_as_coe]
          sorry
        simp only [Prod.fst_mul, Prod.snd_mul]
        have h2_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * moveAction2).1.orient = 0
          := by sorry
        have h2_4 := lemma1_001_UFL (g * moveAction2) h2_3 h2
        obtain ⟨h2_4_1,h2_4_2,h2_4_3,h2_4_4,h2_4_5,h2_4_6⟩ := h2_4
        use (moveAction2 * h2_4_1)
        apply And.intro
        {simp only;
          -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
          --done
          sorry}
        apply And.intro
        { rw [← Prod.fst_mul]
          rw [← mul_assoc]
          exact h2_4_3
        }
        apply And.intro
        { rw [← Prod.snd_mul]
          rw [← mul_assoc]
          rw [← h2_4_4]
          --这个是直接计算结果，因为后者moveAction2的orient全零 --
          have h2_4_4_1: g.2.orient = (g * moveAction2).2.orient
            := by
            -- done
            sorry
          exact h2_4_4_1
        }
        apply And.intro
        { rw [← Prod.fst_mul]
          rw [← mul_assoc]
          rw [← h2_4_5]
          --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
          have h2_4_5_1:g.1.permute = (g * moveAction2).1.permute
            := by
            -- done
            sorry
          exact h2_4_5_1
        }
        { rw [← Prod.snd_mul]
          rw [← mul_assoc]
          rw [← h2_4_6]
          --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
          have h2_4_6_1: g.2.permute = (g * moveAction2).2.permute
            := by
            -- done
            sorry
          exact h2_4_6_1
        }
        done
      }
      { have ha2: Corner_Absolute_Orient g.1 UFL_index = 2
          := by
          -- 怎么使用排除法呢？很明显是对的,非0，1,就是2
          -- done
          sorry
        let moveAction3 := h*F*(G1Perm^2)*F'
        -- #eval F*(G1Perm^2)*F'
        -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![1, 0, 0, 0, 0, 0, 0, 2] },
        -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
        -- 如何说明g*h2满足这个呢？：(Corner_Absolute_Orient g.1 UFL_index) = 0
        -- 关键引理证明1
        have h3_1: (g.1.orient + moveAction3.1.orient ∘ g.1.permute) (g.1.permute⁻¹ UFL_index)
        = g.1.orient (g.1.permute⁻¹ UFL_index) + moveAction3.1.orient (UFL_index)
        := by
          simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Pi.add_apply,
            Function.comp_apply, apply_inv_self]
          done
        simp only [Corner_Absolute_Orient] at ha2
        simp at ha2
        -- 关键引理证明2
        have h3_2: g.1.orient (g.1.permute⁻¹ UFL_index) + moveAction3.1.orient (UFL_index) = 0
        := by
          simp only [Inv.inv]
          rw [ha2]
          simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc]
          have h3_2_1: (ps_mul Solved.1 (ps_mul F.1 (ps_mul (G1Perm ^ 2).1 F'.1))).orient UFL_index = 1
          := by rfl
          rw [h3_2_1]
          rfl
          done
        have h3: (Corner_Absolute_Orient (g*moveAction3).1 UFL_index) = 0
        := by
          simp only [Corner_Absolute_Orient]
          simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, invFun_as_coe]
          sorry
        simp only [Prod.fst_mul, Prod.snd_mul]
        have h3_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * moveAction3).1.orient = 0
          := by sorry
        have h3_4 := lemma1_001_UFL (g * moveAction3) h3_3 h3
        --todo
        obtain ⟨h3_4_1,h3_4_2,h3_4_3,h3_4_4,h3_4_5,h3_4_6⟩ := h3_4
        use (moveAction3 * h3_4_1)
        apply And.intro
        {simp only;
          -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
          --done
          sorry}
        apply And.intro
        { rw [← Prod.fst_mul]
          rw [← mul_assoc]
          exact h3_4_3
        }
        apply And.intro
        { rw [← Prod.snd_mul]
          rw [← mul_assoc]
          rw [← h3_4_4]
          --这个是直接计算结果，因为后者moveAction2的orient全零 --
          have h3_4_4_1: g.2.orient = (g * moveAction3).2.orient
            := by
            -- #eval F*G1Perm*F'
            -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![2, 0, 0, 0, 0, 0, 0, 1] },
            -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
            -- done
            sorry
          exact h3_4_4_1
        }
        apply And.intro
        { rw [← Prod.fst_mul]
          rw [← mul_assoc]
          rw [← h3_4_5]
          --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
          have h3_4_5_1:g.1.permute = (g * moveAction3).1.permute
            := by
            -- done
            sorry
          exact h3_4_5_1
        }
        { rw [← Prod.snd_mul]
          rw [← mul_assoc]
          rw [← h3_4_6]
          --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
          have h3_4_6_1: g.2.permute = (g * moveAction3).2.permute
            := by
            -- done
            sorry
          exact h3_4_6_1
        }
        sorry
      }
    }

      --给出详细的步骤h，使得(g * h).1.orient = 0成立：
      -- 1.首先还原F面的3个角块:UFL,DFL,DFR：
        -- 1.还原UFL的方向数：分类讨论：
          -- 1.UFL的方向数为0,h=h
          -- 2.UFL的方向数为1,h=h*F*G1*F'
          -- 3.UFL的方向数为2,h=h*F*(G1^2)*F'
        -- 2.还原DFL的方向数：分类讨论：
          -- 1.DFL的方向数为0,h=h
          -- 2.DFL的方向数为1,h=h*F^2*G1*F^2
          -- 3.DFL的方向数为2,h=h*F^2*(G1^2)*F^2
        -- ...

  -- 还原所有棱块的方向数,且不改变全体角块的方向数，且不改变所有块的位置。
  lemma lemma2
  : ∀g : RubiksSuperType,
  Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.snd.orient = 0
  →
  ∃ h ∈ RubiksGroup ,
  (g * h).snd.orient = 0
  ∧
  g.1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  := by sorry


    -- 涉及定理：closure_three_cycles_eq_alternating
    -- 涉及定义：3循环： IsThreeCycle
  -- 通用小引理4.6：假设n>=3，对于任意集合M，假设M包含Sn中全体3循环，则=>， M >= An
  lemma lemma46
  (M:Subgroup (Perm α)):
  ∀ σ:Perm α,
    IsThreeCycle σ
    ∧
    σ ∈ M
  →
  ∀ al ∈ alternatingGroup α,
  al ∈ M
  := by
    have h1:= closure { σ : Perm α | σ ∈ M}
    sorry

  -- #check alternatingGroup α


  -- 应该写成参数好一点
  -- 下面31和32是最关键的最重要的定理
  -- 魔方群能生成所有角块的位置三循环（方向数不改变）。
  lemma lemma31
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

  -- 魔方群能生成所有棱块的位置三循环（方向数不改变）。
  lemma lemma32
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

  -- 其实就是lemma31和lemma32的简单结合，由于角块和棱块可以分别互不影响地完成，这个引理应该很容易证明。
  lemma lemma11
  :∀ x : RubiksSuperType,
  IsThreeCycle x.2.permute
  ∧
  IsThreeCycle x.1.permute
  ∧
  x.1.orient = 0
  ∧
  x.2.orient = 0
  →
  ∃ g : RubiksSuperType,
  Reachable g
  ∧
  x * g = Solved
  := by sorry

  -- 右推左的限制条件1使得只能选这2种情况进行分类讨论。
  /-- 1.（奇X奇) 2.(偶X偶）-/
  lemma lemma12_condition1_restriction
  (x:RubiksSuperType)
  (h1:x ∈ ValidCube)
  :sign x.1.permute = sign x.2.permute
  ↔
  (sign x.1.permute = -1 ∧ -1 = sign x.2.permute)
  ∨
  (sign x.1.permute = 1 ∧ 1 = sign x.2.permute)
  := by sorry

  -- 化归思想，所有lemma12_condition1_restriction中的情况1可以通过魔方群操作变成情况2。
  /-- （奇X奇) → (偶X偶）-/
  lemma lemma13_oddXoddToEvenXEven
  (g:RubiksSuperType)
  (h1:Reachable g)
  :∀ x:RubiksSuperType,
  Reachable x
  ∧
  (sign x.1.permute = -1 ∧ -1 = sign x.2.permute)
  →
  (sign (g * x).1.permute = 1 ∧ 1 = sign (g * x).2.permute)
  := by sorry

  -- 对于任意g状态角块位置置换属于偶置换的状态，
    -- 则存在操作x1使得(g*x1)的角块位置置换变成1，而且保持(g*x1)的棱块位置不变，而且所有块的方向数不变。
  lemma lemma14
  (g:RubiksSuperType)
  (h1:g.1.permute ∈ alternatingGroup (Fin 8))
  :∃ x1 : RubiksSuperType,
  Reachable x1
  ∧
  (g*x1).1.permute = 1
  ∧
  (g*x1).2.permute = (g).2.permute
  ∧
  ((g*x1).1.orient = (g).1.orient ∧ (g*x1).2.orient = (g).2.orient )
  := by sorry

  -- 对于任意g状态棱块位置置换属于偶置换的状态，
    -- 则存在操作x1使得(g*x1)的棱块位置置换变成1，而且保持(g*x1)的角块位置不变，而且所有块的方向数不变。
  lemma lemma15
  (g:RubiksSuperType)
  (h1:g.2.permute ∈ alternatingGroup (Fin 12))
  :∃ x1 : RubiksSuperType,
  Reachable x1
  ∧
  (g*x1).2.permute = 1
  ∧
  (g*x1).1.permute = (g).1.permute
  ∧
  ((g*x1).1.orient = (g).1.orient ∧ (g*x1).2.orient = (g).2.orient )
  := by sorry

  -- 就是lemma14+15的简单结合
  -- 对于任意g状态角块位置置换属于偶置换的状态，且棱块位置置换属于偶置换的状态，
    -- 则存在操作x1使得(g*x1)的棱块位置置换变成1，而且角块位置置换变成1，而且所有块的方向数不变。
  lemma lemma16
  (g:RubiksSuperType)
  (h1:g.1.permute ∈ alternatingGroup (Fin 8))
  (h2:g.2.permute ∈ alternatingGroup (Fin 12))
  :∃ x1 : RubiksSuperType,
  Reachable x1
  ∧
  ((g*x1).1.permute = 1 ∧ (g*x1).2.permute = 1)
  ∧
  ((g*x1).1.orient = (g).1.orient ∧ (g*x1).2.orient = (g).2.orient )
  := by sorry


-- 魔方第二基本定理的右推左部分：
theorem valid_reachable
: ∀x : RubiksSuperType, x ∈ ValidCube → Reachable x
:= by
  intro x hvx
  simp [ValidCube] at hvx
  let currStat := x
  -- 分类讨论1得到小引理1：假设有状态g∈H,且∑(8在上 i=1) vi(g) = 0 (mod 3),则=>, g能通过有限次作用G中的元素，得到新的性质：v(g)={0,0,...,0}。而且不改变棱块的方向数。
  have h1 := lemma1 x hvx.2.1
  obtain ⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7⟩ := h1
  let currStat := x * h1_2
  let currStat_satisfy := h1_4
  -- 分类讨论2得到小引理2:假设有状态g∈H,且∑(12在上 i=1) wi(g) = 0 (mod 2) ， 则=>,g能通过有限次作用G中的元素，得到新的性质：w(g)={0,0,...,0}。并且不改变角块的方向数。
  have h2 := lemma2 (x * h1_2)
  have h2_2 := hvx.2.2
  rw [h1_5] at h2_2
  have h2 := lemma2 (x * h1_2) h2_2
  obtain ⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8⟩ := h2
  have h2_8 := h1_4
  rw [h2_6] at h2_8
  let currStat := x * h1_2 * h2_3
  let currStat_satisfy: ((x * h1_2 * h2_3).2.orient = 0) ∧ ((x * h1_2 * h2_3).1.orient = 0)
    := { left := h2_5, right := h2_8 }
  -- ValidCube的条件1，限制了当前状态x的范围，所以可以进行2种分类讨论：1.（奇X奇) 2.(偶X偶）
  have h3 := hvx.1
  rw [lemma12_condition1_restriction] at h3
  cases h3 with
  | inl h3_1 =>
    -- 某个过程，存在一个复合操作，作用一次到状态集合（奇X奇)上的某个元素后，新状态会属于新的状态集合(偶X偶），归化成inr
    -- lemma13_oddXoddToEvenXEven
    -- 和inr一样的证明过程
    sorry
  | inr h3_2 =>
    -- 根据h3_2推出x.1,x.2属于偶置换
    have h3_2_1 : (x * h1_2 * h2_3).1.permute ∈ alternatingGroup (Fin 8) := sorry
    have h3_2_2 : (x * h1_2 * h2_3).2.permute ∈ alternatingGroup (Fin 12) := sorry
    -- 使用lemma16使得新状态获得保持旧属性：方向数不变，获取新属性：角块+棱块的位置都变成1。
    have h3_2_3 := lemma16 (x * h1_2 * h2_3) h3_2_1 h3_2_2
    -- 很明显新状态就是还原状态Solved了，也就是已知下面这个y。
    obtain ⟨h3_2_4,h3_2_5,h3_2_6,h3_2_7,h3_2_8⟩ := h3_2_3
    obtain ⟨h3_2_9,h3_2_10⟩ := h3_2_6
    rw [h2_5] at h3_2_8
    rw [h2_8] at h3_2_7
    let currStat := x * h1_2 * h2_3 * h3_2_4
    let currStat_satisfy: (x * h1_2 * h2_3 * h3_2_4).1.orient = 0 ∧ (x * h1_2 * h2_3 * h3_2_4).2.orient = 0
    ∧ (x * h1_2 * h2_3 * h3_2_4).1.permute = 1 ∧ (x * h1_2 * h2_3 * h3_2_4).2.permute = 1 :=
    {
      left := h3_2_7
      right := {
        left := h3_2_8
        right := {
          left := h3_2_9
          right := h3_2_10
        }
      }
    }
    -- 所以还需要证明Reachable y即可。很明显因为都是G里面的6个元素之一FaceTurn，肯定是Reachable。
    -- 将目标Reachable x变成  ∃ y, (Reachable y) ∧ (x * y = Solved)
    -- x经过有限次操作变成了y， y就是复原状态e。
    let y : RubiksSuperType := h1_2 * h2_3 * h3_2_4
    have h101 : Reachable y := sorry
    have h102 : x * y = Solved
      := by
      simp only [y]
      have h102_1 := Solved_iff (x * h1_2 * h2_3 * h3_2_4)
      rw [← mul_assoc]
      rw [← mul_assoc]
      have hh : x * h1_2 * h2_3 * h3_2_4 = (x * h1_2 * h2_3 * h3_2_4)
      := by exact rfl
      rw [hh]
      simp only [RubiksSuperType]
      symm
      apply h102_1.2
      apply And.intro
      {exact h3_2_9}
      apply And.intro
      {exact h3_2_10}
      apply And.intro
      {exact h3_2_7}
      {exact h3_2_8}
    have h105 (y : RubiksSuperType):
    (Reachable y) ∧ (x * y = Solved)
    → Reachable x
    := by
      intro hs
      have h105_1 : x = Solved * y⁻¹
        := by
        rw [hs.2.symm]
        rw [mul_assoc]
        simp only [mul_right_inv, mul_one]
      rw [h105_1]
      apply Reachable.mul
      · exact Reachable.Solved
      · apply Reachable.inv
        exact hs.1
    apply h105 y
    exact { left := h101, right := h102 }
    done
  sorry
  done


-- 魔方第二基本定理的左推右部分：done
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
  | inv c hc hc2 =>
    simp only [Solved, ValidCube]
    simp only [Set.mem_setOf_eq, Prod.fst_inv, PieceState.inv_def, Prod.snd_inv]
    apply And.intro
    {
      simp only [ps_inv]
      simp only [ValidCube] at hc2
      simp only [map_inv, Int.units_inv_eq_self]
      obtain ⟨hc3,hc4⟩:= hc2
      exact hc3
    }
    { apply And.intro
      {
        simp only [ps_inv]
        simp only [Pi.neg_apply, Finset.sum_neg_distrib, neg_eq_zero]
        simp only [ValidCube] at hc2
        obtain ⟨hc3,hc4,hc5⟩:= hc2
        -- hc4 -- 很明显的重排求和不变
        sorry
        done
      }
      { simp only [ps_inv]
        simp only [Pi.neg_apply, Finset.sum_neg_distrib, neg_eq_zero]
        simp only [ValidCube] at hc2
        obtain ⟨hc3,hc4,hc5⟩:= hc2
        -- hc5 -- 很明显的重排求和不变
        sorry
        done
      }
  --

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

/-- done -/
lemma four_rs_eq_solved
: (R * R * R * R) = Solved
:= by
  simp only [R, Solved]
  simp only [Prod.mk_mul_mk, PieceState.mul_def, ps_mul_assoc, Prod.mk_eq_one]
  simp only [ps_mul]
  simp only [Prod.mk.injEq, PieceState.mk.injEq]
  simp only [cyclePieces]
  simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one, Perm.coe_mul]
  apply And.intro
  · apply And.intro
    · ext i
      simp only [Perm.coe_mul, Function.comp_apply, Perm.coe_one, id_eq]
      have h1 := SwapDef i
      -- swapTest2_1
      sorry
      -- done
    · -- orientTest2_1
      sorry
      -- done
  · apply And.intro
    · ext i
      simp only [Perm.coe_mul, Function.comp_apply, Perm.coe_one, id_eq]
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


end RubikCube_BasicRule_2




-- 下面的算法有时间再写一下，感觉是体力活～～
------------------------------------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------------------------------------

-- section ThistlethwaiteAlgorithm

-- ------ 以下是TW算法部分，(因为新开一个文件有点问题，先写在同一个文件吧)：
-- ------ 每一个证明的右推左部分，其实就是还原的算法！！！
-- ------
-- ------
-- ------
-- -- 三个降群的充要条件的证明
-- -- 1.∀g∈ G,
-- -- g∈G1 (G1 = <L^2,R^2,F,B,U,D>)
-- -- ↔
-- -- wi(g)=0 , ∀i , 1<=i<=12
-- def TWGroup1 :
--   Set RubiksSuperType
--   :=
--   -- 这样的一个集合：所有满足后面这些条件的c
--   {
--     c |
--     c ∈ RubiksGroup
--     ∧
--     c.2.orient = 0
--   }

-- instance TWGroup1_instance : Subgroup RubiksSuperType := {
-- -- 如何写成这样的子群的子群呢 ??? instance TWGroup1_instance : Subgroup RubiksGroup := {
--     carrier := TWGroup1
--     mul_mem' := sorry -- 封闭性质
--     one_mem' := sorry -- 单位1元素
--     inv_mem' := sorry -- 逆元素
--     -- 结合律不用证明，父群已经证明。
--     -- 左乘1=本身不用证明
--     -- 右乘1=本身不用证明
--     -- 左乘逆=1不用证明
--     -- 右乘逆=1不用证明
-- }

-- lemma TWGroup1_isSubGroupOf_RubiksGroup :
-- TWGroup1 ⊂ RubiksGroup := by sorry

-- theorem TWAlgorithm_TWGroup1_iff
-- : ∀x : RubiksSuperType, Reachable_TWGroup1 x ↔ x ∈ TWGroup1
-- := by sorry
--   -- 左推右之前没用归纳法，用的是定义的cases就可以了，一样的意思。

-- -- 2.∀g∈ G1,
-- -- g∈G2 (G2 = <L^2,R^2,F^2,B^2,U,D>)
-- -- ↔
-- -- {
-- --     1. vi(g)=0 , ∀i , 1<=i<=8
-- --     2. 棱块有1个保持轨道:意思是，σ(g)作用到 {5,6,7,8}这4个棱块后，这4个棱块仍然全都在位置{5,6,7,8}上，
-- --         换句话说，这4个棱块经过g变换后保持在（上下）中层里。
-- -- }
-- def remainsEdgeOrbit :RubiksSuperType → (List ℕ) → Prop := sorry
-- def remainsCornerOrbit :RubiksSuperType → (List ℕ) → Prop := sorry

-- /-- 这里先特指白色面中，和白色不一样的角块的（白色的）个数Count，Count是偶数个。
--     -- 集合{1-8}（根据c.1.permute来分析）中,位于前4个位置中，数一下1-4的个数，这个个数为Even。-/
-- def CornerUpWrongColorCountEven :RubiksSuperType → Prop := sorry


-- def TWGroup2 :
--   Set RubiksSuperType
--   :=
--   -- 这样的一个集合：所有满足后面这些条件的c
--   {
--     c |
--     c ∈ RubiksGroup
--     ∧
--     c.2.orient = 0
--     ∧
--     c.1.orient = 0
--     ∧
--     remainsEdgeOrbit c {4,5,6,7}
--   }

-- instance TWGroup2_instance : Subgroup RubiksSuperType := {
--     carrier := TWGroup2
--     mul_mem' := sorry -- 封闭性质
--     one_mem' := sorry -- 单位1元素
--     inv_mem' := sorry -- 逆元素
--     -- 结合律不用证明，父群已经证明。
--     -- 左乘1=本身不用证明
--     -- 右乘1=本身不用证明
--     -- 左乘逆=1不用证明
--     -- 右乘逆=1不用证明
-- }

-- lemma TWGroup2_isSubGroupOf_TWGroup1 :
-- TWGroup2 ⊂ TWGroup1 := by sorry

-- theorem TWAlgorithm_TWGroup2_iff
-- : ∀x : RubiksSuperType, Reachable_TWGroup2 x ↔ x ∈ TWGroup2
-- := by sorry

-- -- 3.∀g∈ G2,
-- -- g∈ G3 (<L^2,R^2,F^2,B^2,U^2,D^2>)
-- -- ↔
-- -- {
-- --     1.棱块有2个新的保持轨道：{1,3,9,11},{2,4,10,12}，当然也有G2就有的{5,6,7,8}
-- --     2.角块有2个保持轨道：{1,3,6,8},{2,4,5,7}
-- --     3.与这个白色面心块颜色不一样的角块的个数,记为Count,Count是偶数。这里先特指白色面中，和白色不一样的角块的（白色的）个数Count，Count是偶数个。
-- -- }
--   -- 这个先忽略：有一个额外的左推右的可以证明：
--   --    (4.{1,3,6,8},{2,4,5,7}这两个角块的轨道中，不包含三轮换。
--   --     换句话说，g的效果不能产生这些轨道内的3循环。
--   --      换句话说，g不是单纯的棱块3循环（不变全体块的方向数，不变角块的位置）)

-- def TWGroup3 :
--   Set RubiksSuperType
--   :=
--   -- 这样的一个集合：所有满足后面这些条件的c
--   {
--     c |
--     c ∈ RubiksGroup
--     ∧
--     c.2.orient = 0
--     ∧
--     c.1.orient = 0
--     ∧
--     remainsEdgeOrbit c {4,5,6,7} ∧ remainsEdgeOrbit c {0,2,8,10} ∧ remainsEdgeOrbit c {1,3,9,11}
--     ∧
--     remainsCornerOrbit c {0,2,5,7} ∧ remainsCornerOrbit c {1,3,4,6}
--     ∧
--     CornerUpWrongColorCountEven c
--   }

-- instance TWGroup3_instance : Subgroup RubiksSuperType := {
--     carrier := TWGroup3
--     mul_mem' := sorry -- 封闭性质
--     one_mem' := sorry -- 单位1元素
--     inv_mem' := sorry -- 逆元素
--     -- 结合律不用证明，父群已经证明。
--     -- 左乘1=本身不用证明
--     -- 右乘1=本身不用证明
--     -- 左乘逆=1不用证明
--     -- 右乘逆=1不用证明
-- }

-- lemma TWGroup3_isSubGroupOf_TWGroup2 :
-- TWGroup3 ⊂ TWGroup2 := by sorry

-- theorem TWAlgorithm_TWGroup3_iff
-- : ∀x : RubiksSuperType, Reachable_TWGroup3 x ↔ x ∈ TWGroup3
-- := by sorry

-- def idSuperTypeFunc : RubiksSuperType → RubiksSuperType :=
--   fun x => x

-- -- 存在一个算法（比如ThistlethwaiteAlgorithm）的步数小于等于52步。
-- theorem ActionsLessThan52 [CommMonoid RubiksSuperType]:
-- ∀ g :RubiksSuperType,
-- ∃ pset : (Finset RubiksSuperType) ,
-- -- pset.prod idSuperTypeFunc
-- -- (pset.1.map idSuperTypeFunc)
-- pset.prod idSuperTypeFunc = Solved
-- ∧ (Multiset.toList pset.1).length <= 52
-- := by sorry


-- end ThistlethwaiteAlgorithm
