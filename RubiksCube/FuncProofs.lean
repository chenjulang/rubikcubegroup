import RubiksCube.RubiksCubeFunc
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Alternating

open Equiv Perm
open Equiv Equiv.Perm Subgroup Fintype
open alternatingGroup
open BigOperators
-- set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

-- 注意：依赖文件RubiksCubeFunc改过的话，最好点一下这个文件的restrt File
-- 线索：1.mathlib的group theory 2.人工智能POE和AGI 3.MIL+其他课程+北大-关于群的描述
-- Alternating.lean
variable (α : Type*) [Fintype α] [DecidableEq α]



section ValidityChecks
  --例子：
  @[simp]
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


  @[simp]
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
      -- done

  @[simp]
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

  @[simp]
  lemma CornerTwistInvalid : CornerTwist ∉ ValidCube
  := by
      simp only [CornerTwist, ValidCube]
      simp only [Fin.zero_eta, imp_false, Finset.mem_singleton, Finset.mem_insert, zero_ne_one,
        false_or, Set.mem_setOf_eq, map_one, forall_true_left, Pi.zero_apply, Finset.sum_const_zero,
        and_true, true_and]
      exact Fin.pos_iff_ne_zero.mp Nat.le.refl
      done

  @[simp]
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
  @[simp]
  lemma solved_reachable
  (x : RubiksSuperType)
  (h : x = Solved)
  : Reachable x
  := by
    rw [h]
    exact Reachable.Solved

  section rubikCubeFormula

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
  def G2Perm_element1 : RubiksSuperType
  := L*F*R'*F'*L'
  def G2Perm_element2 : RubiksSuperType
  := U^2*R*U*R*U'*R^2*U^2
  /-- 可以保持其他块的方向和位置，只改变UF和UR的方向，分别是UF的方向+1，UR的方向的方向+1。-/
  def G2Perm : RubiksSuperType
  := G2Perm_element1 * G2Perm_element2 * R
  -- #eval G2Perm
  --   ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
  --  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
  -- 如何定义G2的“L,R,B”变式呢？直接推算，还是写一个函数映射呢？
    -- 先写3个映射，然后列表映射即可。
    def VariantFaceTurn_L : RubiksSuperType → RubiksSuperType :=
    fun x =>
      if x = U then U
      else if x = D then D
      else if x = R then F
      else if x = L then B
      else if x = F then L
      else if x = B then R
      else if x = U2 then U2
      else if x = D2 then D2
      else if x = R2 then F2
      else if x = L2 then B2
      else if x = F2 then L2
      else if x = B2 then R2
      else if x = U' then U'
      else if x = D' then D'
      else if x = R' then F'
      else if x = L' then B'
      else if x = F' then L'
      else if x = B' then R'
      else 1

    def VariantFaceTurn_R : RubiksSuperType → RubiksSuperType :=
    fun x =>
      if x = U then U
      else if x = D then D
      else if x = R then B
      else if x = L then F
      else if x = F then R
      else if x = B then L
      else if x = U2 then U2
      else if x = D2 then D2
      else if x = R2 then B2
      else if x = L2 then F2
      else if x = F2 then R2
      else if x = B2 then L2
      else if x = U' then U'
      else if x = D' then D'
      else if x = R' then B'
      else if x = L' then F'
      else if x = F' then R'
      else if x = B' then L'
      else 1

    def VariantFaceTurn_B : RubiksSuperType → RubiksSuperType :=
    fun x =>
      if x = U then U
      else if x = D then D
      else if x = R then L
      else if x = L then R
      else if x = F then B
      else if x = B then F
      else if x = U2 then U2
      else if x = D2 then D2
      else if x = R2 then L2
      else if x = L2 then R2
      else if x = F2 then B2
      else if x = B2 then F2
      else if x = U' then U'
      else if x = D' then D'
      else if x = R' then L'
      else if x = L' then R'
      else if x = F' then B'
      else if x = B' then F'
      else 1

    -- def G1Perm_L : Array RubiksSuperType := #[R' ,D ,D ,R ,B' ,U ,U ,B,R' ,D ,D ,R ,B' ,U ,U ,B]
    -- -- #eval toString $ G1Perm_L.toList.toArray.toList
    -- -- #eval toString $ (G1Perm_L.map VariantFaceTurn_L).toList
    -- #eval (G1Perm_L.map VariantFaceTurn_L).toList.prod --注意，这样toList不会去掉重复？
    -- -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![2, 0, 0, 0, 0, 0, 1, 0] },
    -- --  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })

    -- def testG1Perm_L : List RubiksSuperType := [R' ,D ,D ,R ,B' ,U ,U ,B,R' ,D ,D ,R ,B' ,U ,U ,B]
    def VariantFaceTurn_L_List : (l:List RubiksSuperType) → RubiksSuperType
    := fun l => (l.map VariantFaceTurn_L).prod
    -- #eval VariantFaceTurn_L_List testG1Perm_L
    -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![2, 0, 0, 0, 0, 0, 1, 0] },
    -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
    def VariantFaceTurn_R_List : (l:List RubiksSuperType) → RubiksSuperType
    := fun l => (l.map VariantFaceTurn_R).prod
    def VariantFaceTurn_B_List : (l:List RubiksSuperType) → RubiksSuperType
    := fun l => (l.map VariantFaceTurn_B).prod

  def G5Perm_element1 : RubiksSuperType
  := R*U*R'*U'*R'*F*R*R*U'*R'
  /-- 是2个2循环:2个角块的2循环+2个棱块的2循环,详细: 角块ρ(g5) =(2,3)， 棱块σ(g5) =(1,2) -/
  def G5Perm : RubiksSuperType -- R U R' F' R U R' U' R' F R R U' R' U'
  := R*U*R'*F'*G5Perm_element1*U'
  -- #eval G5Perm
  -- ({ permute := ![0, 2, 1, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
  -- { permute := ![1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })

  /-- 是一个角块3循环 ρ(g4) =(2,4,3) 这里指绝对位置2的块的新位置是绝对位置4；相当于顺时针 -/
  def G4Perm : RubiksSuperType -- [R',F',F',F',R',B,B,R',R',R',F',R',B,B,R',R']
  := R'*F'*F'*F'*R'*B*B*R'*R'*R'*F'*R'*B*B*R'*R'
  -- #eval G4Perm
  -- ({ permute := ![0, 3, 1, 2, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
  --  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })

  /-- 是一个棱块3循环 ρ(g4) =(1,2,4) 这里指绝对位置1的块的新位置是绝对位置2；相当于逆时针 -/
  def G3Perm : RubiksSuperType -- [R,U',R,U,R,U,R,U',R',U',R,R]
  := R*U'*R*U*R*U*R*U'*R'*U'*R*R
  -- #eval G3Perm
  --   ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
  --  { permute := ![1, 3, 2, 0, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })


  /-- 创建一阶交换子公式。不强制要求：r1影响到的块的集合A，与r2影响到的块的集合B，交集有且仅有1个（这就是为什么称作一阶）。 -/
  def conjugate_formula : RubiksSuperType → RubiksSuperType → RubiksSuperType
  := fun r1 r2 => r1 * r2 * r1⁻¹
  -- #eval conjugate_formula (D'*L*L) G4Perm  -- 比如：(2,3,6)交换子
  -- ({ permute := ![0, 5, 1, 3, 4, 2, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
  -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })


  end rubikCubeFormula

  -- 说白了，只需要倒腾这20个块就能还原，不多也不少：
  -- 角块的排位：8个
  def UFL_index :Fin 8 := 0
  def UFR_index :Fin 8 := 1
  def UBR_index :Fin 8 := 2
  def UBL_index :Fin 8 := 3
  def DFL_index :Fin 8 := 4
  def DFR_index :Fin 8 := 5
  def DBR_index :Fin 8 := 6
  def DBL_index :Fin 8 := 7
  -- 棱块的排位：12个
  def UF_index :Fin 12 := 0
  def UR_index:Fin 12 := 1
  def UB_index :Fin 12 := 2
  def UL_index :Fin 12 := 3
  def FL_index :Fin 12 := 4
  def FR_index :Fin 12 := 5
  def RB_index :Fin 12 := 6
  def LB_index :Fin 12 := 7
  def FD_index :Fin 12 := 8
  def RD_index :Fin 12 := 9
  def BD_index :Fin 12 := 10
  def LD_index :Fin 12 := 11


  section lemma1TrashCode

    lemma lemma1_013:(F * G1Perm * F').2.orient = 0
    := by
      decide
      done

    lemma lemma1_012
    (g:RubiksSuperType)
    :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} g.1.orient = 0
    →
    Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * (F^2 * G1Perm^2 * F^2)).1.orient = 0
    := by
      sorry -- 计算结果可知
      -- 这个在社区解决了等待写
      -- done

    lemma lemma1_011:(F^2 * G1Perm^2 * F^2).1.permute = 1
    := by
      decide
      done

    -- 这个结论是一个计算的结果吧？
    lemma lemma1_010
    (g:RubiksSuperType)
    :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} g.1.orient = 0
    →
    Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * (F^2 * G1Perm * F^2)).1.orient = 0
    := by
      -- #eval F*G1Perm*F'
      -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![2, 0, 0, 0, 0, 0, 0, 1] },
      -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
      intro h1
      simp only [Prod.fst_mul]
      have h2: (F^2).1 * G1Perm.1 * (F^2).1 = (F^2 * G1Perm * F^2).1 := by rfl
      simp only [h2]
      simp only [PieceState.mul_def,ps_mul]
      -- Goal: ∑ x in {0, 1, 2, 3, 4, 5, 6, 7}, ((F^2 * G1Perm * F^2).1.orient ∘ g.1.permute + g.1.orient) x = 0
      -- 直接看计算结果就知道了
      -- (F * G1Perm * F').1.orient = ![2, 0, 0, 0, 0, 0, 0, 1]，求和模3也为0
      -- (F * G1Perm * F').1.orient ∘ ⇑g.1.permute ，只是重新排列了，求和模3也为0
      -- g.1.orient的话由h1知道也是求和为0。
      -- 这个在社区解决了等待写
      sorry
      -- done

    lemma lemma1_009:(F^2 * G1Perm * F^2).1.permute = 1
    := by
      decide
      done

    lemma lemma1_008
    (g:RubiksSuperType)
    :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} g.1.orient = 0
    →
    Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * (F * G1Perm^2 * F')).1.orient = 0
    := by
      -- #eval F*G1Perm*F'
      -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![2, 0, 0, 0, 0, 0, 0, 1] },
      -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
      intro h1
      simp only [Prod.fst_mul]
      have h2: F.1 * (G1Perm^2).1 * F'.1 = (F * G1Perm^2 * F').1 := by exact rfl
      simp only [h2]
      simp only [PieceState.mul_def,ps_mul]
      -- Goal: ∑ x in {0, 1, 2, 3, 4, 5, 6, 7}, ((F * G1Perm ^ 2 * F').1.orient ∘ ⇑g.1.permute + g.1.orient) x = 0
      -- 直接看计算结果就知道了
      -- (F * G1Perm * F').1.orient = ![2, 0, 0, 0, 0, 0, 0, 1]，求和模3也为0
      -- (F * G1Perm * F').1.orient ∘ ⇑g.1.permute ，只是重新排列了，求和模3也为0
      -- g.1.orient的话由h1知道也是求和为0。
      -- 这个在社区解决了等待写
      sorry
      -- done

    lemma lemma1_007:(F * G1Perm^2 * F').1.permute = 1
    := by
      decide
      done

    lemma lemma1_006:(F * G1Perm * F').1.permute = 1
    := by
      decide
      done

    --Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} g.1.orient = 0
    -- → Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * F * G1Perm * F').1.orient = 0
    -- 这个结论是一个计算的结果吧？
    lemma lemma1_005
    (g:RubiksSuperType)
    :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} g.1.orient = 0
    →
    Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * (F * G1Perm * F')).1.orient = 0
    := by
      -- #eval F*G1Perm*F'
      -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![2, 0, 0, 0, 0, 0, 0, 1] },
      -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
      intro h1
      simp only [Prod.fst_mul]
      have h2: F.1 * G1Perm.1 * F'.1 = (F * G1Perm * F').1 := by exact rfl
      simp only [h2]
      simp only [PieceState.mul_def,ps_mul]
      -- Goal: ∑ x in {0, 1, 2, 3, 4, 5, 6, 7}, ((F * G1Perm * F').1.orient ∘ g.1.permute + g.1.orient) x = 0
      -- 直接看计算结果就知道了
      -- (F * G1Perm * F').1.orient = ![2, 0, 0, 0, 0, 0, 0, 1]，求和模3也为0
      -- (F * G1Perm * F').1.orient ∘ ⇑g.1.permute ，只是重新排列了，求和模3也为0
      -- g.1.orient的话由h1知道也是求和为0。
      -- 这个在社区解决了等待写
      have h3: ∑ x in {0, 1, 2, 3, 4, 5, 6, 7}, (F * G1Perm * F').1.orient x = 0 := sorry
      simp only [Pi.add_apply]
      have h4: ∑ x in {0, 1, 2, 3, 4, 5, 6, 7}, (((F * G1Perm * F').1.orient ∘ ⇑g.1.permute) x + g.1.orient x)
      = ∑ x in {0, 1, 2, 3, 4, 5, 6, 7}, ((F * G1Perm * F').1.orient ∘ g.1.permute) x
        + ∑ x in {0, 1, 2, 3, 4, 5, 6, 7},g.1.orient x := sorry
      rw [h4]
      rw [h1]
      clear h1 h4
      rw [add_zero]
      have h5: ∑ x in {0, 1, 2, 3, 4, 5, 6, 7}, ((F * G1Perm * F').1.orient ∘ g.1.permute) x = 0 := by sorry
      exact h5
      done


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
    /-- 这个引理理应频繁使用的，不知道为什么这里没用到呢？感觉应该可以比较抽象的解决很多重复代码。 -/
    -- lemma lemma1_2reachableMove_Exist_same_property
    -- (g : RubiksSuperType)
    -- (h : RubiksSuperType)
    -- (hInG : h ∈ RubiksGroup)
    -- (somePropA : RubiksSuperType →  Prop)
    -- :
    -- ∃ x1:RubiksGroup,
    -- somePropA ((g) * x1) -- “冒号”写成“属于号”就不行了，请注意
    -- →
    --   (∃ x2 ∈ RubiksGroup, somePropA ((g*h) * x2))
    --   ∧
    --   somePropA ((g*h) * (h⁻¹*x1))
    -- := by
    --

    -- 这个应该可以去掉，暂时保留注释：
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
    -- lemma lemma1_008_7Corners_eq_8Corners
    -- (g : RubiksSuperType)
    -- (SetA : Set RubiksSuperType := {a: RubiksSuperType | ∑ i in (Finset.range 8), (a.1.orient) i = 0})
    -- (x1: RubiksSuperType)
    -- :∑ i in (Finset.range 8), (g.1.orient) i = 0
    -- ∧
    -- x1 ∈ SetA
    -- ∧
    -- ∀ j : (Fin 7),  (g*x1).1.orient j = 0 -- 注意：当这3个符号报错时 :,∈,in 三个都轮流试一下。
    -- →
    -- (g*x1).1.orient 7 = 0
    -- :=

    -- 由于前几个角块的证明过分类似，还没找到复写代码的巧妙方法，直接跳到最后一个引理进行证明，看看如何收尾即可。
    -- 想不到引理1最后一步这么简单，推出矛盾即可。
    lemma lemma1_007_UFR_and008DBL
    (g : RubiksSuperType) -- RubiksSuperType即手写的H。
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFR_index) = 0
      ∧ (Corner_Absolute_Orient g.1 UBL_index) = 0 ∧ (Corner_Absolute_Orient g.1 UBR_index) = 0 ∧ (Corner_Absolute_Orient g.1 DBR_index) = 0
      ∧ (Corner_Absolute_Orient g.1 UFR_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    ∧
    (Corner_Absolute_Orient g.1 DBL_index) = 0
    := by
      let h := Solved
      have h_CAO_DBL_is0: Corner_Absolute_Orient g.1 DBL_index = 0
      := by
        -- 用h1 , h2即可
        simp only [Corner_Absolute_Orient] at h2 ⊢
        -- 这个在社区解决了等待写
        sorry
        -- done
      by_cases ha0 : (Corner_Absolute_Orient g.1 DBL_index)=0
      {
        let moveAction1 : RubiksSuperType := 1
        use moveAction1
        simp only [moveAction1]
        rw [mul_one]
        sorry
        -- 这个在社区解决了等待写
        -- done -- 很明显了,目标本身一堆rfl的，然后0那个就是展开即可
      }
      { by_cases ha1: (Corner_Absolute_Orient g.1 DBL_index) = 1
        {
          -- 这时候要推出矛盾才行，换句话说，这种情况是不成立的；换句话说，不需要被讨论的。
          -- 应该也是明显的，矛盾点在h1+h2可以推出Corner_Absolute_Orient g.1 DBL_index 只能= 0
          -- Corner_Absolute_Orient g.1 DBL_index 只能= 0与ha1矛盾
          exact (ha0 h_CAO_DBL_is0).elim
        }
        { have ha2: Corner_Absolute_Orient g.1 DBL_index = 2
            := by
            -- 怎么使用排除法呢？很明显是对的,非0，1,就是2
            -- Kyle Miller: You can use the generalize tactic in your original goal to turn Corner_Absolute_Orient g.1 UFL_index into a, and then
            -- example (a : Fin 3) (h0 : ¬ a = 0) (h1 : ¬ a = 1) : a = 2 := by
            --   fin_cases a <;> simp at *
            -- Kyle Miller: There's also this magic:
            -- example (a : Fin 3) (h0 : ¬ a = 0) (h1 : ¬ a = 1) : a = 2 := by
            --   match a with
            --   | 2 => rfl
            -- done
            -- 这个在社区解决了等待写
            sorry
          -- 这里矛盾点在哪呢？一开始的分类讨论非0就能和0推出矛盾，所以不需要考虑当前情况。
          exact (ha0 h_CAO_DBL_is0).elim
        }
      }
      done

    lemma lemma1_006_DBR
    (g : RubiksSuperType) -- RubiksSuperType即手写的H。
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFR_index) = 0
      ∧ (Corner_Absolute_Orient g.1 UBL_index) = 0 ∧ (Corner_Absolute_Orient g.1 UBR_index) = 0 ∧ (Corner_Absolute_Orient g.1 DBR_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    := by sorry

    lemma lemma1_005_UBR
    (g : RubiksSuperType) -- RubiksSuperType即手写的H。
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFR_index) = 0
      ∧ (Corner_Absolute_Orient g.1 UBL_index) = 0 ∧ (Corner_Absolute_Orient g.1 UBR_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    := by sorry --

    lemma lemma1_004_UBL
    (g : RubiksSuperType) -- RubiksSuperType即手写的H。
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFR_index) = 0
      ∧ (Corner_Absolute_Orient g.1 UBL_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    := by sorry --

    lemma lemma1_003_DFR
    (g : RubiksSuperType) -- RubiksSuperType即手写的H。
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFR_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    := by sorry --

    lemma lemma1_002_DFL
    (g : RubiksSuperType) -- RubiksSuperType即手写的H。
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    := by sorry --

    -- lemma1的主要证明依赖本引理lemma1_001_UFL，本引理主要证明依赖lemma1_002_DFL
    -- 任意H中的状态，满足：角块方向数求和后模3为0,UFL的方向数为0
      -- 则=>存在G中操作h，(g*h)还原所有角块的方向数，且不改变全体棱块的方向数，且不改变所有块的位置。
    -- 思路：还原DFL的方向数后，使用lemma1_002_DFL即可。
    lemma lemma1_001_UFL
    (g : RubiksSuperType)
    (hsum0: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (hCAO_UFL_0: (Corner_Absolute_Orient g.1 UFL_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    := by
      let h := Solved
      by_cases ha0 : (Corner_Absolute_Orient g.1 DFL_index)=0
      {
        let moveAction1 := Solved
        have h1 := lemma1_002_DFL g hsum0 ({
          left := hCAO_UFL_0
          right := ha0
        })
        obtain ⟨h1_1,h1_2,h1_3,h1_4,h1_5,h1_6⟩ := h1
        use h1_1
        done
      }
      { by_cases ha1: (Corner_Absolute_Orient g.1 DFL_index) = 1
        { let moveAction2 := F^2*G1Perm*F^2
          -- #eval F^2*G1Perm*F^2
          -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 2, 0, 0, 1] },
          --  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
          -- 关键引理证明1:先找出从ha1发掘出的这个索引有什么用。
          have h2_1: (g.1.orient + moveAction2.1.orient ∘ g.1.permute) (g.1.permute⁻¹ DFL_index)
          = g.1.orient (g.1.permute⁻¹ DFL_index) + moveAction2.1.orient (DFL_index)
          := by
            simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Pi.add_apply,
              Function.comp_apply, apply_inv_self]
            done
          simp only [Corner_Absolute_Orient] at ha1
          simp at ha1
          -- 关键引理证明2：先找出从ha1发掘出的这个索引有什么用。原来已知的是这样的。
          have h2_2: g.1.orient (g.1.permute⁻¹ DFL_index) + moveAction2.1.orient (DFL_index) = 0
          := by
            simp only [Inv.inv]
            rw [ha1]
            simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc]
            have h2_2_1: (ps_mul (F ^ 2).1 (ps_mul G1Perm.1 (F ^ 2).1)).orient DFL_index = 2
            := by rfl
            rw [h2_2_1]
            rfl
            done
          have h2: (Corner_Absolute_Orient (g*moveAction2).1 DFL_index) = 0
          := by
            have _h2_1: (g.1.orient + moveAction2.1.orient ∘ ⇑g.1.permute) (g.1.permute⁻¹ DFL_index) = 0 := h2_1.trans h2_2
            simp only [Corner_Absolute_Orient]
            have _h2_3: (g * (F^2 * G1Perm * F^2)).1.permute = (g).1.permute
              := by
              simp only [Prod.fst_mul]
              rw [permute_mul]
              rw [← Prod.fst_mul]
              rw [← Prod.fst_mul]
              rw [lemma1_009]
              rfl
            rw [_h2_3]
            have _h2_4: (g.1.orient + moveAction2.1.orient ∘ g.1.permute) = (g * (F^2 * G1Perm * F^2)).1.orient
              := by
              have _h2_4_1 := PieceState.mul_def g.1 (F^2 * G1Perm * F^2).1
              simp only [ps_mul] at _h2_4_1
              simp only [← Prod.fst_mul] at _h2_4_1
              rw [_h2_4_1]
              simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc]
              rw [add_comm]
              done
            rw [← _h2_4]
            exact _h2_1
            done
          simp only [Prod.fst_mul, Prod.snd_mul]
          have h2_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * moveAction2).1.orient = 0
            := by
            have h2_3_1 := lemma1_010 g hsum0
            simp only [moveAction2]
            exact h2_3_1
            done
          -- 这个引理h_b_2_4'需要分类讨论，代码将是很深的嵌套，想想怎么解决。应该要统一一个引理解决，or，一个通用的引理到处用。
          -- 否则每次都要证明对前面已还原的角块的绝对方向数是不变的。
          have h_b_2_4': Corner_Absolute_Orient (g * moveAction2).1 UFL_index = 0
            := by sorry -- 待办，证明类似lemma1中的h2
          have h2_4 := lemma1_002_DFL (g * moveAction2) h2_3 {
            left := h_b_2_4' -- Corner_Absolute_Orient (g * moveAction2).1 UFL_index = 0
            right := h2
          }
          obtain ⟨h2_4_1,h2_4_2,h2_4_3,h2_4_4,h2_4_5,h2_4_6⟩ := h2_4
          use (moveAction2 * h2_4_1)
          apply And.intro
          {simp only;
            -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
            sorry
            --done
          }
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
              sorry
              -- done
            exact h2_4_4_1
          }
          apply And.intro
          { rw [← Prod.fst_mul]
            rw [← mul_assoc]
            rw [← h2_4_5]
            --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
            have h2_4_5_1:g.1.permute = (g * moveAction2).1.permute
              := by
              sorry
              -- done
            exact h2_4_5_1
          }
          { rw [← Prod.snd_mul]
            rw [← mul_assoc]
            rw [← h2_4_6]
            --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
            have h2_4_6_1: g.2.permute = (g * moveAction2).2.permute
              := by
              sorry
              -- done
            exact h2_4_6_1
          }
          done
        }
        { have ha2: Corner_Absolute_Orient g.1 DFL_index = 2
            := by
            -- 怎么使用排除法呢？很明显是对的,非0，1,就是2
            -- Kyle Miller: You can use the generalize tactic in your original goal to turn Corner_Absolute_Orient g.1 UFL_index into a, and then
            -- example (a : Fin 3) (h0 : ¬ a = 0) (h1 : ¬ a = 1) : a = 2 := by
            --   fin_cases a <;> simp at *
            -- Kyle Miller: There's also this magic:
            -- example (a : Fin 3) (h0 : ¬ a = 0) (h1 : ¬ a = 1) : a = 2 := by
            --   match a with
            --   | 2 => rfl
            -- done
            -- 这个在社区解决了等待写
            sorry
          let moveAction3 := (F^2)*(G1Perm^2)*(F^2)
          have h3_1: (g.1.orient + moveAction3.1.orient ∘ g.1.permute) (g.1.permute⁻¹ DFL_index)
          = g.1.orient (g.1.permute⁻¹ DFL_index) + moveAction3.1.orient (DFL_index)
          := by
            simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Pi.add_apply,
              Function.comp_apply, apply_inv_self]
            done
          simp only [Corner_Absolute_Orient] at ha2
          simp at ha2
          -- 关键引理证明2
          have h3_2: g.1.orient (g.1.permute⁻¹ DFL_index) + moveAction3.1.orient (DFL_index) = 0
          := by
            simp only [Inv.inv]
            rw [ha2]
            simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc]
            have h3_2_1: (ps_mul (F ^ 2).1 (ps_mul (G1Perm ^ 2).1 (F ^ 2).1)).orient DFL_index = 1
            := by rfl
            -- rw [h3_2_1] -- 不写也可以
            rfl
            done
          have h3: (Corner_Absolute_Orient (g*moveAction3).1 DFL_index) = 0
          := by
            have _h3_1: (g.1.orient + moveAction3.1.orient ∘ g.1.permute) (g.1.permute⁻¹ DFL_index) = 0 := h3_1.trans h3_2
            simp only [Corner_Absolute_Orient]
            -- have _h3_2: (F^2 * G1Perm^2 * F^2).1.permute = 1
            -- 下面用lemma1_00?代替
            have _h3_3: (g * (F^2 * G1Perm^2  * F^2)).1.permute = (g).1.permute
              := by
              simp only [Prod.fst_mul]
              rw [permute_mul]
              rw [← Prod.fst_mul]
              rw [← Prod.fst_mul]
              rw [lemma1_011]
              rfl
            rw [_h3_3]
            have _h3_4: (g.1.orient + moveAction3.1.orient ∘ g.1.permute) = (g * (F^2 * G1Perm^2 * F^2)).1.orient
              := by
              have _h3_4_1 := PieceState.mul_def g.1 (F^2 * G1Perm^2 * F^2).1
              simp only [ps_mul] at _h3_4_1
              simp only [← Prod.fst_mul] at _h3_4_1
              rw [_h3_4_1]
              simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc]
              rw [add_comm]
              done
            rw [← _h3_4]
            exact _h3_1
            done
          simp only [Prod.fst_mul, Prod.snd_mul]
          have h3_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * moveAction3).1.orient = 0
            := by
            have h3_3_1 := lemma1_012 g hsum0
            simp only [moveAction3]
            exact h3_3_1
            done
          have h_b_3:Corner_Absolute_Orient (g * moveAction3).1 UFL_index = 0
            := by
            simp only [Corner_Absolute_Orient]
            sorry --待办 -- 类似于 (Corner_Absolute_Orient (g*moveAction3).1 DFL_index) = 0的证明，需要从已知出发，先证明两个关键引理。
          have h3_4 := lemma1_002_DFL (g * moveAction3) h3_3 {
            left := h_b_3
            right := h3
          }
          obtain ⟨h3_4_1,h3_4_2,h3_4_3,h3_4_4,h3_4_5,h3_4_6⟩ := h3_4
          use (moveAction3 * h3_4_1)
          apply And.intro
          {simp only;
            -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
            sorry
            --done
          }
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
              -- done
              sorry
            exact h3_4_4_1
          }
          apply And.intro
          { rw [← Prod.fst_mul]
            rw [← mul_assoc]
            rw [← h3_4_5]
            have h3_4_5_1:g.1.permute = (g * moveAction3).1.permute
              := by
              --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
              -- done
              sorry
            exact h3_4_5_1
          }
          { rw [← Prod.snd_mul]
            rw [← mul_assoc]
            rw [← h3_4_6]
            have h3_4_6_1: g.2.permute = (g * moveAction3).2.permute
              := by
              --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
              -- done
              sorry
            exact h3_4_6_1
          }
        }
      }
      done

  #eval (F*G1Perm*F').1.permute = 1
  #eval F^2*G1Perm*F^2


  -- done
  -- 任意H中的状态，满足角块方向数求和后模3为0,
    -- 则=>存在G中操作h，(g*h)还原所有角块的方向数，且不改变全体棱块的方向数，且不改变所有块的位置。
  @[simp]
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
      obtain ⟨h1_1,h1_2,h1_3,h1_4,h1_5,h1_6⟩ := h1
      use h1_1
      done
    }
    { by_cases ha1: (Corner_Absolute_Orient g.1 UFL_index) = 1
      { let moveAction2 := F*G1Perm*F'
        -- #eval F*G1Perm*F'
        -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![2, 0, 0, 0, 0, 0, 0, 1] },
        -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
        -- 如何说明g*moveAction2满足这个呢？：(Corner_Absolute_Orient (g*moveAction2).1 UFL_index) = 0
          -- 也就是要证明：UFL方向数为1,操作后为0.
        -- 关键引理证明1:先找出从ha1发掘出的这个索引有什么用。
        have h2_1: (g.1.orient + moveAction2.1.orient ∘ g.1.permute) (g.1.permute⁻¹ UFL_index)
        = g.1.orient (g.1.permute⁻¹ UFL_index) + moveAction2.1.orient (UFL_index)
        := by
          simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Pi.add_apply,
            Function.comp_apply, apply_inv_self]
          done
        simp only [Corner_Absolute_Orient] at ha1
        simp at ha1
        -- 关键引理证明2：先找出从ha1发掘出的这个索引有什么用。原来已知的是这样的。
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
          have _h2_1: (g.1.orient + moveAction2.1.orient ∘ ⇑g.1.permute) (g.1.permute⁻¹ UFL_index) = 0 := h2_1.trans h2_2
          simp only [Corner_Absolute_Orient]
          have _h2_3: (g * (F * G1Perm * F')).1.permute = (g).1.permute
            := by
            simp only [Prod.fst_mul]
            rw [permute_mul]
            rw [← Prod.fst_mul]
            rw [← Prod.fst_mul]
            rw [lemma1_006]
            rfl
          rw [_h2_3]
          have _h2_4: (g.1.orient + moveAction2.1.orient ∘ g.1.permute) = (g * (F * G1Perm * F')).1.orient
            := by
            have _h2_4_1 := PieceState.mul_def g.1 (F * G1Perm * F').1
            simp only [ps_mul] at _h2_4_1
            simp only [← Prod.fst_mul] at _h2_4_1
            rw [_h2_4_1]
            simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc]
            rw [add_comm]
            done
          rw [← _h2_4]
          exact _h2_1
          done
        simp only [Prod.fst_mul, Prod.snd_mul]
        have h2_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * moveAction2).1.orient = 0
          := by
          have h2_3_1 := lemma1_005 g hsum0
          simp only [moveAction2]
          exact h2_3_1
          done
        have h2_4 := lemma1_001_UFL (g * moveAction2) h2_3 h2
        obtain ⟨h2_4_1,h2_4_2,h2_4_3,h2_4_4,h2_4_5,h2_4_6⟩ := h2_4
        use (moveAction2 * h2_4_1)
        apply And.intro
        {simp only;
          -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
          sorry
          --done
        }
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
            rw [Prod.snd_mul]
            simp only [PieceState.mul_def,ps_mul]
            rw [lemma1_013]
            simp only [Pi.zero_comp, zero_add]
            done
          exact h2_4_4_1
        }
        apply And.intro
        { rw [← Prod.fst_mul]
          rw [← mul_assoc]
          rw [← h2_4_5]
          --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
          have h2_4_5_1:g.1.permute = (g * moveAction2).1.permute
            := by
            sorry
            -- done
          exact h2_4_5_1
        }
        { rw [← Prod.snd_mul]
          rw [← mul_assoc]
          rw [← h2_4_6]
          --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
          have h2_4_6_1: g.2.permute = (g * moveAction2).2.permute
            := by
            sorry
            -- done
          exact h2_4_6_1
        }
        done
      }
      { have ha2: Corner_Absolute_Orient g.1 UFL_index = 2
          := by
          -- 怎么使用排除法呢？很明显是对的,非0，1,就是2
          -- Kyle Miller: You can use the generalize tactic in your original goal to turn Corner_Absolute_Orient g.1 UFL_index into a, and then
          -- example (a : Fin 3) (h0 : ¬ a = 0) (h1 : ¬ a = 1) : a = 2 := by
          --   fin_cases a <;> simp at *
          -- Kyle Miller: There's also this magic:
          -- example (a : Fin 3) (h0 : ¬ a = 0) (h1 : ¬ a = 1) : a = 2 := by
          --   match a with
          --   | 2 => rfl
          -- done
          -- 这个在社区解决了等待写
          sorry
        let moveAction3 := F*(G1Perm^2)*F'
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
          have h3_2_1: (ps_mul F.1 (ps_mul (G1Perm ^ 2).1 F'.1)).orient UFL_index = 1
          := by rfl
          rw [h3_2_1]
          rfl
          done
        have h3: (Corner_Absolute_Orient (g*moveAction3).1 UFL_index) = 0
        := by
          have _h3_1: (g.1.orient + moveAction3.1.orient ∘ g.1.permute) (g.1.permute⁻¹ UFL_index) = 0 := h3_1.trans h3_2
          simp only [Corner_Absolute_Orient]
          -- have _h3_2: (F * G1Perm^2 * F').1.permute = 1
          -- 下面用lemma1_007代替
          -- simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, invFun_as_coe]
          have _h3_3: (g * (F * G1Perm^2  * F')).1.permute = (g).1.permute
            := by
            simp only [Prod.fst_mul]
            rw [permute_mul]
            rw [← Prod.fst_mul]
            rw [← Prod.fst_mul]
            rw [lemma1_007]
            rfl
          rw [_h3_3]
          have _h3_4: (g.1.orient + moveAction3.1.orient ∘ g.1.permute) = (g * (F * G1Perm^2 * F')).1.orient
            := by
            have _h3_4_1 := PieceState.mul_def g.1 (F * G1Perm^2 * F').1
            simp only [ps_mul] at _h3_4_1
            simp only [← Prod.fst_mul] at _h3_4_1
            rw [_h3_4_1]
            simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc]
            rw [add_comm]
            done
          rw [← _h3_4]
          exact _h3_1
          done
        simp only [Prod.fst_mul, Prod.snd_mul]
        have h3_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * moveAction3).1.orient = 0
          := by
          have h3_3_1 := lemma1_008 g hsum0
          simp only [moveAction3]
          exact h3_3_1
          done
        have h3_4 := lemma1_001_UFL (g * moveAction3) h3_3 h3
        obtain ⟨h3_4_1,h3_4_2,h3_4_3,h3_4_4,h3_4_5,h3_4_6⟩ := h3_4
        use (moveAction3 * h3_4_1)
        apply And.intro
        {simp only;
          -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
          sorry
          --done
        }
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
          have h3_4_5_1:g.1.permute = (g * moveAction3).1.permute
            := by
            --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
            -- done
            sorry
          exact h3_4_5_1
        }
        { rw [← Prod.snd_mul]
          rw [← mul_assoc]
          rw [← h3_4_6]
          have h3_4_6_1: g.2.permute = (g * moveAction3).2.permute
            := by
            --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
            -- done
            sorry
          exact h3_4_6_1
        }
      }
    }
    done

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

  end lemma1TrashCode


  section lemma2TrashCode

  lemma lemma2_006
  (g:RubiksSuperType)
  :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} g.2.orient = 0
  →
  Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} (g * (R * G2Perm * R')).2.orient = 0
  := by
    sorry -- 计算结果可知
    -- done

  lemma lemma2_005:(R * G2Perm * R').2.permute = 1
  := by
    decide
    done

  lemma lemma2_004
  (g:RubiksSuperType)
  :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} g.2.orient = 0
  →
  Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} (g*G2Perm).2.orient = 0
  := by
    -- #eval F*G1Perm*F'
    -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![2, 0, 0, 0, 0, 0, 0, 1] },
    -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
    intro h1
    -- simp only [Prod.snd_mul]
    have h2: (G2Perm).2 = (G2Perm).2 := by exact rfl
    -- rw [h2]
    -- simp only [PieceState.mul_def,ps_mul]
    -- Goal: ∑ x in {0, 1, 2, 3, 4, 5, 6, 7}, ((F * G1Perm ^ 2 * F').1.orient ∘ ⇑g.1.permute + g.1.orient) x = 0
    -- 直接看计算结果就知道了
    -- (F * G1Perm * F').1.orient = ![2, 0, 0, 0, 0, 0, 0, 1]，求和模3也为0
    -- (F * G1Perm * F').1.orient ∘ ⇑g.1.permute ，只是重新排列了，求和模3也为0
    -- g.1.orient的话由h1知道也是求和为0。
    sorry
    -- done

  lemma lemma2_003:(G2Perm).2.permute = 1 := by decide

  lemma lemma2_010_UL_and_011_UF
  (g : RubiksSuperType) -- RubiksSuperType即手写的H。
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0 ∧ (Edge_Absolute_Orient g.2 BD_index) = 0 ∧ (Edge_Absolute_Orient g.2 LB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 LD_index) = 0
  ∧ (Edge_Absolute_Orient g.2 FL_index) = 0
  ∧ (Edge_Absolute_Orient g.2 FD_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UL_index) = 0)
  :
  ∃ h ∈ RubiksGroup,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  (Edge_Absolute_Orient g.2 UF_index) = 0
  := by
    let h := Solved
    have h_EAO_UF_is0: Edge_Absolute_Orient g.2 UF_index = 0
    := by
      -- 用h1 , h2即可
      simp only [Edge_Absolute_Orient] at h2 ⊢
      -- 这个在社区解决了等待写
      sorry
      -- done
    by_cases ha0 : Edge_Absolute_Orient g.2 UF_index = 0
    {
      let moveAction1 : RubiksSuperType := 1
      use moveAction1
      simp only [moveAction1]
      rw [mul_one]
      sorry
      -- done -- 很明显了,Goal很多rfl-- 这个在社区解决了等待写
    }
    { have ha2: Edge_Absolute_Orient g.2 UF_index = 1
      := by
        -- 怎么使用排除法呢？很明显是对的,非0，1,就是2
        -- Kyle Miller: You can use the generalize tactic in your original goal to turn Corner_Absolute_Orient g.1 UFL_index into a, and then
        -- example (a : Fin 3) (h0 : ¬ a = 0) (h1 : ¬ a = 1) : a = 2 := by
        --   fin_cases a <;> simp at *
        -- Kyle Miller: There's also this magic:
        -- example (a : Fin 3) (h0 : ¬ a = 0) (h1 : ¬ a = 1) : a = 2 := by
        --   match a with
        --   | 2 => rfl
        -- done
        -- 这个在社区解决了等待写
        sorry
      exact (ha0 h_EAO_UF_is0).elim
    }
    done


  lemma lemma2_009_FD
  (g : RubiksSuperType) -- RubiksSuperType即手写的H。
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0 ∧ (Edge_Absolute_Orient g.2 BD_index) = 0 ∧ (Edge_Absolute_Orient g.2 LB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 LD_index) = 0
  ∧ (Edge_Absolute_Orient g.2 FL_index) = 0
  ∧ (Edge_Absolute_Orient g.2 FD_index) = 0)
  :
  ∃ h ∈ RubiksGroup,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  := by sorry --

  lemma lemma2_008_FL
  (g : RubiksSuperType) -- RubiksSuperType即手写的H。
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0 ∧ (Edge_Absolute_Orient g.2 BD_index) = 0 ∧ (Edge_Absolute_Orient g.2 LB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 LD_index) = 0
  ∧ (Edge_Absolute_Orient g.2 FL_index) = 0)
  :
  ∃ h ∈ RubiksGroup,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  := by sorry --

  lemma lemma2_007_LD
  (g : RubiksSuperType) -- RubiksSuperType即手写的H。
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0 ∧ (Edge_Absolute_Orient g.2 BD_index) = 0 ∧ (Edge_Absolute_Orient g.2 LB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 LD_index) = 0)
  :
  ∃ h ∈ RubiksGroup,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  := by sorry --

  lemma lemma2_006_LB
  (g : RubiksSuperType) -- RubiksSuperType即手写的H。
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0 ∧ (Edge_Absolute_Orient g.2 BD_index) = 0 ∧ (Edge_Absolute_Orient g.2 LB_index) = 0)
  :
  ∃ h ∈ RubiksGroup,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  := by sorry --

  lemma lemma2_005_BD
  (g : RubiksSuperType) -- RubiksSuperType即手写的H。
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0 ∧ (Edge_Absolute_Orient g.2 BD_index) = 0)
  :
  ∃ h ∈ RubiksGroup ,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  := by sorry --

  lemma lemma2_004_UB
  (g : RubiksSuperType) -- RubiksSuperType即手写的H。
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0)
  :
  ∃ h ∈ RubiksGroup ,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  := by sorry--

  lemma lemma2_003_RB
  (g : RubiksSuperType) -- RubiksSuperType即手写的H。
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0)
  :
  ∃ h ∈ RubiksGroup ,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  := by sorry--

  lemma lemma2_002_RD
  (g : RubiksSuperType) -- RubiksSuperType即手写的H。
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0)
  :
  ∃ h ∈ RubiksGroup ,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  := by sorry--

  lemma lemma2_002_FR
  (g : RubiksSuperType) -- RubiksSuperType即手写的H。
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0)
  :
  ∃ h ∈ RubiksGroup ,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  := by sorry--

  -- 任意H中的状态，满足：棱块方向数求和后模2为0,UR的方向数为0
    -- 则=>存在G中操作h，(g*h)还原所有棱块的方向数，且不改变全体角块的方向数，且不改变所有块的位置。
  -- 思路：还原FR
  lemma lemma2_001_UR
  (g : RubiksSuperType)
  (hsum0: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.snd.orient = 0)
  (h_EAO_UR_0: (Edge_Absolute_Orient g.2 UR_index) = 0)
  :
  ∃ h ∈ RubiksGroup ,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  := by
    let h := Solved
    by_cases ha0 : (Edge_Absolute_Orient g.2 FR_index)=0
    {
      let moveAction1 := Solved
      have h1 := lemma2_002_FR g hsum0 ({
        left := h_EAO_UR_0
        right := ha0
      })
      obtain ⟨h1_1,h1_2,h1_3,h1_4,h1_5,h1_6⟩ := h1
      use h1_1
      done
    }
    { have ha2: (Edge_Absolute_Orient g.2 FR_index) = 1
        := by
        -- 怎么使用排除法呢？很明显是对的,非0，1,就是2
        -- Kyle Miller: You can use the generalize tactic in your original goal to turn Corner_Absolute_Orient g.1 UFL_index into a, and then
        -- example (a : Fin 3) (h0 : ¬ a = 0) (h1 : ¬ a = 1) : a = 2 := by
        --   fin_cases a <;> simp at *
        -- Kyle Miller: There's also this magic:
        -- example (a : Fin 3) (h0 : ¬ a = 0) (h1 : ¬ a = 1) : a = 2 := by
        --   match a with
        --   | 2 => rfl
        -- done
        sorry
      let moveAction3 := (R)*(G2Perm)*(R')
      have h3_1: (g.2.orient + moveAction3.2.orient ∘ g.2.permute) (g.2.permute⁻¹ FR_index)
      = g.2.orient (g.2.permute⁻¹ FR_index) + moveAction3.2.orient (FR_index)
      := by
        simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Pi.add_apply,
          Function.comp_apply, apply_inv_self]
        done
      simp only [Edge_Absolute_Orient] at ha2
      simp at ha2
      have h3_2: g.2.orient (g.2.permute⁻¹ FR_index) + moveAction3.2.orient (FR_index) = 0
      := by
        simp only [Inv.inv]
        rw [ha2]
        simp only [Prod.snd_mul, PieceState.mul_def, ps_mul_assoc]
        have h3_2_1: (ps_mul R.2 (ps_mul G2Perm.2 R'.2)).orient FR_index = 1
        := by rfl
        -- rw [h3_2_1] -- 不写也可以
        rfl
        done
      have h3: (Edge_Absolute_Orient (g*moveAction3).2 FR_index) = 0
      := by
        have _h3_1: (g.2.orient + moveAction3.2.orient ∘ g.2.permute) (g.2.permute⁻¹ FR_index) = 0 := h3_1.trans h3_2
        simp only [Edge_Absolute_Orient]
        -- have _h3_2: (F^2 * G1Perm^2 * F^2).2.permute = 1
        -- 下面用lemma1_00?代替
        have _h3_3: (g * (R * G2Perm * R')).2.permute = (g).2.permute
          := by
          simp only [Prod.snd_mul]
          rw [permute_mul]
          rw [← Prod.snd_mul]
          rw [← Prod.snd_mul]
          rw [lemma2_005]
          rfl
        rw [_h3_3]
        have _h3_4: (g.2.orient + moveAction3.2.orient ∘ g.2.permute) = (g * (R * G2Perm * R')).2.orient
          := by
          have _h3_4_1 := PieceState.mul_def g.2 (R * G2Perm * R').2
          simp only [ps_mul] at _h3_4_1
          simp only [← Prod.snd_mul] at _h3_4_1
          rw [_h3_4_1]
          simp only [Prod.snd_mul, PieceState.mul_def, ps_mul_assoc]
          rw [add_comm]
          done
        rw [← _h3_4]
        exact _h3_1
        done
      simp only [Prod.fst_mul, Prod.snd_mul]
      have h3_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} (g * moveAction3).2.orient = 0
        := by
        have h3_3_1 := lemma2_006 g hsum0
        simp only [moveAction3]
        exact h3_3_1
        done
      have h_b_3:Edge_Absolute_Orient (g * moveAction3).2 UR_index = 0
        := by sorry --待办--
      have h3_4 := lemma2_002_FR (g * moveAction3) h3_3 {
        left := h_b_3
        right := h3
      }
      obtain ⟨h3_4_1,h3_4_2,h3_4_3,h3_4_4,h3_4_5,h3_4_6⟩ := h3_4
      use (moveAction3 * h3_4_1)
      apply And.intro
      {simp only;
        -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
        sorry
        --done
      }
      apply And.intro
      { rw [← Prod.snd_mul]
        rw [← mul_assoc]
        exact h3_4_3
      }
      apply And.intro
      { rw [← Prod.fst_mul]
        rw [← mul_assoc]
        rw [← h3_4_4]
        --这个是直接计算结果，因为后者moveAction2的orient全零 --
        have h3_4_4_1: g.1.orient = (g * moveAction3).1.orient
          := by
          -- done
          sorry
        exact h3_4_4_1
      }
      apply And.intro
      { rw [← Prod.fst_mul]
        rw [← mul_assoc]
        rw [← h3_4_5]
        have h3_4_5_1:g.1.permute = (g * moveAction3).1.permute
          := by
          --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
          -- done
          sorry
        exact h3_4_5_1
      }
      { rw [← Prod.snd_mul]
        rw [← mul_assoc]
        rw [← h3_4_6]
        have h3_4_6_1: g.2.permute = (g * moveAction3).2.permute
          := by
          --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
          -- done
          sorry
        exact h3_4_6_1
      }
    }
    done



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
  := by
    intro g hsum0
    let h:= Solved
    by_cases ha0 : (Edge_Absolute_Orient g.2 UR_index)=0
    {
      let moveAction1 := Solved
      have h1 := lemma2_001_UR g hsum0 ha0
      obtain ⟨h1_1,h1_2,h1_3,h1_4,h1_5,h1_6⟩ := h1
      use h1_1
      done
    }
    { have ha2: (Edge_Absolute_Orient g.2 UR_index)=1
        := by
        -- 怎么使用排除法呢？很明显是对的,非0，1,就是2
        -- Kyle Miller: You can use the generalize tactic in your original goal to turn Corner_Absolute_Orient g.2 UFL_index into a, and then
        -- example (a : Fin 3) (h0 : ¬ a = 0) (h1 : ¬ a = 1) : a = 2 := by
        --   fin_cases a <;> simp at *
        -- Kyle Miller: There's also this magic:
        -- example (a : Fin 3) (h0 : ¬ a = 0) (h1 : ¬ a = 1) : a = 2 := by
        --   match a with
        --   | 2 => rfl
        -- done
        sorry
      let moveAction3 := (G2Perm)
      -- #eval G2Perm
      --   ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
      --  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
      have h3_1: (g.2.orient + moveAction3.2.orient ∘ g.2.permute) (g.2.permute⁻¹ UR_index)
      = g.2.orient (g.2.permute⁻¹ UR_index) + moveAction3.2.orient (UR_index)
      := by
        simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Pi.add_apply,
          Function.comp_apply, apply_inv_self]
        done
      simp only [Edge_Absolute_Orient] at ha2
      simp at ha2
      have h3_2: g.2.orient (g.2.permute⁻¹ UR_index) + moveAction3.2.orient (UR_index) = 0
      := by
        simp only [Inv.inv]
        rw [ha2]
        -- simp only [Prod.snd_mul, PieceState.mul_def, ps_mul_assoc]
        have h3_2_1: G2Perm.2.orient UR_index = 1
        := by rfl
        rw [h3_2_1]
        rfl
        done
      have h3: (Edge_Absolute_Orient (g*moveAction3).2 UR_index) = 0
        := by
          have _h3_1: (g.2.orient + moveAction3.2.orient ∘ g.2.permute) (g.2.permute⁻¹ UR_index) = 0 := h3_1.trans h3_2
          simp only [Edge_Absolute_Orient]
          -- have _h3_2: (G2Perm).2.permute = 1
          -- 下面用lemma1_007代替
          -- simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, invFun_as_coe]
          have _h3_3: (g * (G2Perm)).2.permute = (g).2.permute
            := by
            simp only [Prod.snd_mul]
            rw [permute_mul]
            -- rw [← Prod.snd_mul]
            -- rw [← Prod.snd_mul]
            rw [lemma2_003]
            rfl
          rw [_h3_3]
          have _h3_4: (g.2.orient + moveAction3.2.orient ∘ g.2.permute) = (g * (G2Perm)).2.orient
            := by
            have _h3_4_1 := PieceState.mul_def g.2 (G2Perm).2
            simp only [ps_mul] at _h3_4_1
            simp only [← Prod.snd_mul] at _h3_4_1
            rw [_h3_4_1]
            simp only [Prod.snd_mul, PieceState.mul_def, ps_mul_assoc]
            rw [add_comm]
            done
          rw [← _h3_4]
          exact _h3_1
          done
      simp only [Prod.fst_mul, Prod.snd_mul]
      have h3_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} (g * moveAction3).2.orient = 0
        := by
        have h3_3_1 := lemma2_004 g hsum0
        simp only [moveAction3]
        exact h3_3_1
        done
      have h3_4 := lemma2_001_UR (g * moveAction3) h3_3 h3
      obtain ⟨h3_4_1,h3_4_2,h3_4_3,h3_4_4,h3_4_5,h3_4_6⟩ := h3_4
      use (moveAction3 * h3_4_1)
      apply And.intro
      {simp only;
        -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
        sorry
        --done
      }
      apply And.intro
      { rw [← Prod.snd_mul]
        rw [← mul_assoc]
        exact h3_4_3
      }
      apply And.intro
      { rw [← Prod.fst_mul]
        rw [← mul_assoc]
        rw [← h3_4_4]
        --这个是直接计算结果，因为后者moveAction2的orient全零 --
        have h3_4_4_1: g.1.orient = (g * moveAction3).1.orient
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
        have h3_4_5_1:g.1.permute = (g * moveAction3).1.permute
          := by
          --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
          -- done
          sorry
        exact h3_4_5_1
      }
      { rw [← Prod.snd_mul]
        rw [← mul_assoc]
        rw [← h3_4_6]
        have h3_4_6_1: g.2.permute = (g * moveAction3).2.permute
          := by
          --这个是直接计算结果，因为后者moveAction2的permute为单位元 --
          -- done
          sorry
        exact h3_4_6_1
      }
    }
    done

  end lemma2TrashCode


  -- 先看看这个引理是：1.直接在lemma3中使用，还是2.换成已知定理在去lemma3中使用，这时候就要删掉这里了。
  -- 选择先去掉。
    -- 涉及定理：closure_three_cycles_eq_alternating
    -- 涉及定义：3循环： IsThreeCycle
  -- 通用小引理4.6：假设n>=3，对于任意集合M，假设M包含Sn中全体3循环，则=>， M >= An
  -- lemma lemma46
  -- (M:Subgroup (Perm α)):
  -- ∀ σ:Perm α,
  --   IsThreeCycle σ
  --   ∧
  --   σ ∈ M
  -- →
  -- ∀ al ∈ alternatingGroup α,
  -- al ∈ M
  -- := by
  --   have h1:= closure { σ : Perm α | σ ∈ M}
  --   sorry

  def remains_allOrient_and_edgePermute
  (x : RubiksSuperType)  : Prop
  := x.1.orient=0 ∧ x.2.orient=0 ∧ x.2.permute=1
  def remains_allOrient_and_cornerPermute
  (x : RubiksSuperType)  : Prop
  := x.1.orient=0 ∧ x.2.orient=0 ∧ x.1.permute=1

  -- 角块部分：
  def exist_reachableG_cornerPermute_to1
  (x : RubiksSuperType)  : Prop
  :=
    ∃ g : RubiksSuperType,
      Reachable g
      ∧
      (x * g).1.permute = 1
      ∧
      (x * g).1.orient = (x).1.orient
      ∧
      (x * g).2.orient = (x).2.orient
      ∧
      (x * g).2.permute = (x).2.permute

  def permFin8_to_RubiksSuperType
  : (Perm (Fin 8)) → RubiksSuperType
  := by
    exact fun x => {
      fst := {
        permute := x
        orient := 0
      }
      snd := {
        permute := 1
        orient := 0
      }
    }

  lemma alternatingCornerPermute_eq_3Cycles_to_g_eq_3Cycles_mul_one
  (g: RubiksSuperType)
  (threeList: List (Perm (Fin 8)) )
  (h1: ∀a ∈ threeList, IsThreeCycle a)
  (h2: g.1.permute = threeList.prod)
  :∃ (rubiksList:List RubiksSuperType) (rst1:RubiksSuperType),
  g =rst1 * rubiksList.prod
  ∧
  rst1.1.permute = 1
  ∧
  (g.1.orient=rst1.1.orient ∧ g.2.permute=rst1.2.permute ∧ g.2.orient=rst1.2.orient)
  ∧
  rubiksList = (threeList.map permFin8_to_RubiksSuperType) -- 映射得来
  := by sorry

  -- 棱块部分：
  def exist_reachableG_edgePermute_to1
  (x : RubiksSuperType)  : Prop
  :=
    ∃ g : RubiksSuperType,
      Reachable g
      ∧
      (x * g).2.permute = 1
      ∧
      (x * g).1.orient = (x).1.orient
      ∧
      (x * g).2.orient = (x).2.orient
      ∧
      (x * g).1.permute = (x).1.permute

  def permFin12_to_RubiksSuperType
  : (Perm (Fin 12)) → RubiksSuperType
  := by
    exact fun x => {
      fst := {
        permute := 1
        orient := 0
      }
      snd := {
        permute := x
        orient := 0
      }
    }

  lemma alternatingEdgePermute_eq_3Cycles_to_g_eq_3Cycles_mul_one
  (g: RubiksSuperType)
  (threeList: List (Perm (Fin 12)) )
  (h1: ∀a ∈ threeList, IsThreeCycle a)
  (h2: g.2.permute = threeList.prod)
  :∃ (rubiksList:List RubiksSuperType) (rst1:RubiksSuperType),
  g = rst1 * rubiksList.prod
  ∧
  rst1.2.permute = 1
  ∧
  -- 原始的3个项相等
  (g.1.orient=rst1.1.orient ∧ g.1.permute=rst1.1.permute ∧ g.2.orient=rst1.2.orient)
  ∧
  rubiksList = (threeList.map permFin12_to_RubiksSuperType) -- 映射得来
  := by sorry


  lemma lemma31_001 : Solved = ({ permute := List.formPerm ([1,2,3]:(List (Fin 8))), orient := 0 }, { permute := 1, orient := 0 }) * (G4Perm)
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
    simp only [G4Perm]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul] -- ***这一行很重要，使得decide成为了可能。
    decide
  lemma lemma31_002 : Solved =  ({ permute := List.formPerm ([1,0,6]:(List (Fin 8))) , orient := 0 }, { permute := 1, orient := 0 }) *
    (B * B * VariantFaceTurn_B_List [R', F', F', F', R', B, B, R', R', R', F', R', B, B, R', R'] * B * B)⁻¹
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one, mul_inv_rev]
    simp only [VariantFaceTurn_B_List,VariantFaceTurn_B]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul]
    decide
  lemma lemma31_003 : Solved =  ({ permute := List.formPerm ([1,3,5]:(List (Fin 8))), orient := 0 }, { permute := 1, orient := 0 }) *
    (G4Perm*(conjugate_formula (D'*L*L) G4Perm)⁻¹)⁻¹
    -- (G4Perm * (D' * L * L * G4Perm * L * L * D)⁻¹)⁻¹ -- 记得最后加一个逆号
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
    simp only [conjugate_formula,G4Perm]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul] -- ***这一行很重要，使得decide成为了可能。
    decide

  -- 思考：纯3循环就是偶置换说的全体3循环吗？是的，因为魔方还原到目前状态也具有方向数全0的属性，也是一个“纯”的偶置换。
  /-- 如果状态x的角块的位置是一个三循环（全体方向数已还原,棱块位置已还原），则，存在G中复合操作g，使得（x*g）的位置是复原状态。 -/
  lemma lemma31 -- 这个命题直接上就是给出其中算法将角块3循环（全体方向数已还原,棱块位置已还原）还原到1。
  -- 用到公式有3类：1.g4 ; 2.g4的4种变式(VariantFaceTurn_?_List) ； 3.包含g4（或g4变式）的交换子（conjugate_formula）。
  (x : RubiksSuperType)
  (h1: IsThreeCycle x.1.permute)
  (h2: x.1.orient =0)
  (h3: x.2.permute = 1)
  (h4: x.1.orient =0)
  : Reachable x
  := by
    -- 如何开展分类56种讨论？先看看IsThreeCycle为条件的一些定理是怎么证明的？
    -- G4Perm效果：ρ(g4) =(2,4,3) ： 顺时针
    -- 可能要人为的等价分类：1.“变式的”，即“同形状”的是等价的。
    -- 需要一个制造排列 Perm (Fin 8)的函数。应该是从List (Fin 8) → Perm (Fin 8)。
    have x_eq_Solvedx : x = Solved * x := by exact self_eq_mul_left.mpr rfl
    -- 先进行一个小分类的推理：原2在3，原3在4，原4在2。
    let p1 := List.formPerm ([1,2,3]:(List (Fin 8))) -- ![0, 2, 3, 1, 4, 5, 6, 7]
    -- 先进行一个小分类的推理：原3新在2，原2新在8，原8新在3。
    let p2 := List.formPerm ([1,0,6]:(List (Fin 8))) -- (2,1,7) == 这里的[1,0,6] -- ![0, 7, 1, 3, 4, 5, 6, 2]
    let p3 := List.formPerm ([1,3,5]:(List (Fin 8))) -- (2,4,6) == 这里的[1,3,5]
    by_cases ha0:x.1.permute = p1
      -- 执行一次G4Perm即可完成。此时制造一个RubiksSuperType
    {
      let rubiks_p1:RubiksSuperType := {
        fst := {
          permute := p1
          orient := 0
        }
        snd := {
          permute := 1
          orient := 0
        }
      }
      -- 由于 Solved * rubiks_p1 = x
      have x_eq_rubiks_p1: x = rubiks_p1
        := by
        simp only [mul_one]
        simp only [← h2,← h3,← h4]
        --很明显了
        sorry
      have G4Perm_eq_rubiks_p1: rubiks_p1*G4Perm = 1
        := by
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
        rw [← Solved_eq_1,lemma31_001]
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
      rw [x_eq_Solvedx]
      apply Reachable.mul
      · exact Reachable.Solved
      · rw [x_eq_rubiks_p1]
        have R_rubiks_p1_mul_G4Perm: Reachable (rubiks_p1 * G4Perm) := by
          rw [G4Perm_eq_rubiks_p1];exact Reachable.Solved
        have testaaa1 := Reachable.split_fst (rubiks_p1) (G4Perm) R_rubiks_p1_mul_G4Perm
        apply testaaa1
        sorry
        -- -- 很明显了
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.mul
        -- apply Reachable.inv;apply Reachable.FT;exact FaceTurn.R
        -- -- 很明显了，如何简化？
        -- sorry
    }
    by_cases ha0:x.1.permute = p2
      -- 执行：交换子(B*B*(VariantFaceTurn_B_List [R',F',F',F',R',B,B,R',R',R',F',R',B,B,R',R'])*B*B)⁻¹
      -- 即可完成。此时制造一个RubiksSuperType
    {
      let rubiks_p2:RubiksSuperType := {
        fst := {
          permute := p2
          orient := 0
        }
        snd := {
          permute := 1
          orient := 0
        }
      }
      -- 由于 Solved * rubiks_p2 = x
      have x_eq_rubiks_p2: x = rubiks_p2
        := by
        simp only [mul_one]
        simp only [← h2,← h3,← h4]
        --很明显了
        sorry
      let solution := (B*B*(VariantFaceTurn_B_List [R',F',F',F',R',B,B,R',R',R',F',R',B,B,R',R'])*B*B)⁻¹
      have Solution_mul_rubiksp2_isOne: rubiks_p2 * solution = 1
        := by
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
        rw [← Solved_eq_1,lemma31_002]
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
      rw [x_eq_Solvedx]
      apply Reachable.mul
      · exact Reachable.Solved
      · rw [x_eq_rubiks_p2]
        have R_rubiksp2_mul_Solution: Reachable (rubiks_p2 * solution) := by
          rw [Solution_mul_rubiksp2_isOne];exact Reachable.Solved
        have testaaa1 := Reachable.split_fst (rubiks_p2) (solution) R_rubiksp2_mul_Solution
        apply testaaa1
        sorry
      --   -- -- 很明显了
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.inv;apply Reachable.FT;exact FaceTurn.R
      --   -- -- 很明显了，如何简化？
      --   -- sorry
    }
    by_cases ha0:x.1.permute = p3
      -- 执行：交换子复合g4 : G4Perm*(D'*L*L*G4Perm*L*L*D)⁻¹
      -- 即可完成。此时制造一个RubiksSuperType
    {
      let rubiks_p3:RubiksSuperType := {
        fst := {
          permute := p3
          orient := 0
        }
        snd := {
          permute := 1
          orient := 0
        }
      }
      -- x 和 rubiks_p3 是一回事：
      have x_eq_rubiks_p3: x = rubiks_p3
        := by
        simp only [mul_one]
        simp only [← h2,← h3,← h4]
        -- simp [ha0,p3,h2,h3,h4]
        --很明显了
        sorry
      let solution := (G4Perm*(conjugate_formula (D'*L*L) G4Perm )⁻¹)⁻¹
      have Solution_mul_rubiksp3_isOne: rubiks_p3 * solution = 1
        := by
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
        rw [← Solved_eq_1,lemma31_003]
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
      rw [x_eq_Solvedx]
      apply Reachable.mul
      · exact Reachable.Solved
      · rw [x_eq_rubiks_p3]
        have R_rubiksp3_mul_Solution: Reachable (rubiks_p3 * solution) := by
          rw [Solution_mul_rubiksp3_isOne];exact Reachable.Solved
        have testaaa1 := Reachable.split_fst (rubiks_p3) (solution) R_rubiksp3_mul_Solution
        apply testaaa1
        sorry
      --   -- -- 很明显了
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.inv;apply Reachable.FT;exact FaceTurn.R
      --   -- -- 很明显了，如何简化？
      --   -- sorry
    }
    sorry

  -- def perm_Test001 := List.formPerm ([1,3,5]:(List (Fin 8)))
  -- #eval perm_Test001
  -- def solutionTest001 := (G4Perm * (D' * L * L * G4Perm * L * L * D)⁻¹)
  -- #eval solutionTest001
  -- def rubik_test001:RubiksSuperType := {
  --       fst := {
  --         permute := perm_Test001
  --         -- swap 1 0 * swap 0 6
  --         orient := 0
  --       }
  --       snd := {
  --         permute := 1
  --         orient := 0
  --       }
  --     }
  -- #eval 1= rubik_test001 * solutionTest001⁻¹



  lemma lemma32_001 : Solved = ({ permute := 1, orient := 0 }, { permute := List.formPerm ([0,3,1]:(List (Fin 12))) , orient := 0 })  * (G3Perm)
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
    simp only [G3Perm]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul] -- ***这一行很重要，使得decide成为了可能。
    decide
  lemma lemma32_002 : Solved =  ({ permute := 1, orient := 0 }, { permute := List.formPerm ([0,1,5]:(List (Fin 12))), orient := 0 }) *
    (conjugate_formula (M_UD * L') G3Perm)⁻¹
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one, mul_inv_rev]
    simp only [G3Perm,conjugate_formula]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul]
    decide
  lemma lemma32_003 : Solved =   ({ permute := 1, orient := 0 }, { permute := List.formPerm ([0,6,11]:(List (Fin 12))), orient := 0 }) *
    (conjugate_formula L2 (conjugate_formula (M_UD*R) G3Perm))⁻¹
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
    simp only [G3Perm,conjugate_formula]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul] -- ***这一行很重要，使得decide成为了可能。
    decide


  /-- 如果状态x的棱块的位置是一个三循环（全体方向数已还原,棱块位置已还原），则，存在G中复合操作g，使得（x*g）的位置是复原状态。 -/
  lemma lemma32
  (x : RubiksSuperType)
  (h1: IsThreeCycle x.2.permute)
  (h2: x.2.orient =0)
  (h3: x.1.permute = 1)
  (h4: x.1.orient =0)
  : Reachable x
  := by
    -- 如何分类220种情况？
    -- G3Perm效果： σ(g3) =(1,2,4): 逆时针
    have x_eq_Solvedx : x = Solved * x := by exact self_eq_mul_left.mpr rfl
    let p1 := List.formPerm ([0,3,1]:(List (Fin 12))) -- (1,4,2) == 这里的[0,3,1]
    let p2 := List.formPerm ([0,1,5]:(List (Fin 12))) -- {1,2,6} == 这里的[0,1,5]
    let p3 := List.formPerm ([0,6,11]:(List (Fin 12))) -- {1,7,12} == 这里的[0,6,11]

    by_cases ha0:x.2.permute = p1
      -- 执行：G3Perm
      -- 即可完成。此时制造一个RubiksSuperType
    {
      let rubiks_p1:RubiksSuperType := {
        fst := {
          permute := 1
          orient := 0
        }
        snd := {
          permute := p1
          orient := 0
        }
      }
      -- x 和 rubiks_p1 是一回事：
      have x_eq_rubiks_p1: x = rubiks_p1
        := by
        simp only [mul_one]
        simp only [← h2,← h3,← h4]
        -- simp [ha0,p3,h2,h3,h4]
        --很明显了
        sorry
      let solution := (G3Perm)
      have Solution_mul_rubiksp1_isOne: rubiks_p1 * solution = 1
        := by
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
        rw [← Solved_eq_1,lemma32_001]
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
      rw [x_eq_Solvedx]
      apply Reachable.mul
      · exact Reachable.Solved
      · rw [x_eq_rubiks_p1]
        have R_rubiksp1_mul_Solution: Reachable (rubiks_p1 * solution) := by
          rw [Solution_mul_rubiksp1_isOne];exact Reachable.Solved
        have testaaa1 := Reachable.split_fst (rubiks_p1) (solution) R_rubiksp1_mul_Solution
        apply testaaa1
        sorry
      --   -- -- 很明显了
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.inv;apply Reachable.FT;exact FaceTurn.R
      --   -- -- 很明显了，如何简化？
      --   -- sorry
    }
    by_cases ha2:x.2.permute = p2
      -- 执行：(M_UD L' (R U' R U R U R U' R' U' R R) L M_UD')⁻¹
      -- 即可完成。此时制造一个RubiksSuperType
    {
      let rubiks_p2:RubiksSuperType := {
        fst := {
          permute := 1
          orient := 0
        }
        snd := {
          permute := p2
          orient := 0
        }
      }
      -- x 和 rubiks_p2 是一回事：
      have x_eq_rubiks_p2: x = rubiks_p2
        := by
        simp only [mul_one]
        simp only [← h2,← h3,← h4]
        -- simp [ha0,p3,h2,h3,h4]
        --很明显了
        sorry
      let solution := (conjugate_formula (M_UD*L') G3Perm)⁻¹
      have Solution_mul_rubiksp2_isOne: rubiks_p2 * solution = 1
        := by
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
        rw [← Solved_eq_1,lemma32_002]
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
      rw [x_eq_Solvedx]
      apply Reachable.mul
      · exact Reachable.Solved
      · rw [x_eq_rubiks_p2]
        have R_rubiksp2_mul_Solution: Reachable (rubiks_p2 * solution) := by
          rw [Solution_mul_rubiksp2_isOne];exact Reachable.Solved
        have testaaa1 := Reachable.split_fst (rubiks_p2) (solution) R_rubiksp2_mul_Solution
        apply testaaa1
        sorry
      --   -- -- 很明显了
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.inv;apply Reachable.FT;exact FaceTurn.R
      --   -- -- 很明显了，如何简化？
      --   -- sorry
    }
    by_cases ha3:x.2.permute = p3
      -- 执行：(L2 (1,4,7) L2)⁻¹ = (L2 (M_UD R G3Perm R' M_UD') L2)⁻¹
      -- 即可完成。此时制造一个RubiksSuperType
    {
      let rubiks_p3:RubiksSuperType := {
        fst := {
          permute := 1
          orient := 0
        }
        snd := {
          permute := p3
          orient := 0
        }
      }
      -- x 和 rubiks_p3 是一回事：
      have x_eq_rubiks_p3: x = rubiks_p3
        := by
        simp only [mul_one]
        simp only [← h2,← h3,← h4]
        -- simp [ha0,p3,h2,h3,h4]
        --很明显了
        sorry
      let solution := (conjugate_formula L2 (conjugate_formula (M_UD*R) G3Perm))⁻¹
      have Solution_mul_rubiksp3_isOne: rubiks_p3 * solution = 1
        := by
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
        rw [← Solved_eq_1,lemma32_003]
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
      rw [x_eq_Solvedx]
      apply Reachable.mul
      · exact Reachable.Solved
      · rw [x_eq_rubiks_p3]
        have R_rubiksp3_mul_Solution: Reachable (rubiks_p3 * solution) := by
          rw [Solution_mul_rubiksp3_isOne];exact Reachable.Solved
        have testaaa1 := Reachable.split_fst (rubiks_p3) (solution) R_rubiksp3_mul_Solution
        apply testaaa1
        sorry
      --   -- -- 很明显了
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.mul
      --   -- apply Reachable.inv;apply Reachable.FT;exact FaceTurn.R
      --   -- -- 很明显了，如何简化？
      --   -- sorry
    }
    sorry

  -- def perm_Test001 := List.formPerm ([0,6,11]:(List (Fin 12)))
  -- #eval perm_Test001
  -- -- ![6, 1, 2, 3, 4, 5, 11, 7, 8, 9, 10, 0]
  -- def solutionTest001 := conjugate_formula L2 (conjugate_formula (M_UD * R) G3Perm)
  -- #eval solutionTest001
  -- --   ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
  -- --  { permute := ![6, 1, 2, 3, 4, 5, 11, 7, 8, 9, 10, 0], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
  -- def rubik_test001:RubiksSuperType := {
  --       fst := {
  --         permute := 1
  --         orient := 0
  --       }
  --       snd := {
  --         permute := perm_Test001
  --         orient := 0
  --       }
  --     }
  -- #eval 1= rubik_test001 * solutionTest001⁻¹




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
  := by
    constructor
    · intro signEq
      by_cases ha0:(sign x.1.permute = -1)
      { left
        simp only [ha0,← signEq]
        simp only [and_self]
      }
      {
        have ha1:(sign x.1.permute = 1)
          := by sorry -- 这个很明显，但要问社区
        right
        simp only [ha1,← signEq]
        simp only [and_self]
      }
    · intro oneOrNegone
      cases' oneOrNegone with BothNegone BothOne
      · simp only [BothNegone]
      · simp only [BothOne]
    done

  #check closure_three_cycles_eq_alternating
  #check prod_list_swap_mem_alternatingGroup_iff_even_length

  -- 对于任意g状态角块位置置换属于偶置换的状态，
    -- 则存在操作x1使得(g*x1)的角块位置置换变成1，而且保持(g*x1)的棱块位置不变，而且所有块的方向数不变。
    -- 这里x1的例子我们使用3循环的复合。
  lemma lemma14
  (g:RubiksSuperType)
  -- 1. g.1.p 是偶的置换
  (h1:g.1.permute ∈ alternatingGroup (Fin 8))
  :exist_reachableG_cornerPermute_to1 g
  := by
    -- 2.lemma31,lemma32:即所有满足这样的g:RubiksSuperType：
      -- {1.IsThreeCycle g.1.p ；2.g.1.o = 0 ；3.g.2.p=1 ; 4.g.2.o=0 }
      -- 都能通过群G复合生成。
    -- 3. 由于g.1.p 是偶的置换，使用这里面应该用到了closure_three_cycles_eq_alternating
      -- g.1.p 可以表示成3循环的乘积,这里记为threeList
    have h2 : ∃ (threeList:List (Perm (Fin 8))) ,
      (∀ a ∈ threeList, IsThreeCycle a)
      ∧
      (g.1.permute = threeList.prod)
      := by
      -- ???可能要用归纳法证明。思路：将偶置换表示成一长串3循环的乘积。
      sorry
    obtain ⟨permList,h2_2,h2_3⟩ := h2
    -- 4. 此处需要一个引理lalternatingCornerPermute_eq_3Cycles_to_g_eq_3Cycles_mul_one来带入这个结论
      -- g可以表示成若干RubiksSuperType和一个rst1:RubiksSuperType的乘积，这里记为rubiksList.
      -- rubiksList满足：{对所有元素a，IsThreeCycle a.1.p；a.1.orient=0; a.2.permute=1; a.2.orient=0}
      -- rst1满足：{a.1.p = 1 ; a.1.orient=g.1.orient; a.2.permute=g.2.permute ; a.2.orient=g.2.orient}
    have h3 := alternatingCornerPermute_eq_3Cycles_to_g_eq_3Cycles_mul_one
      g permList h2_2 h2_3
    obtain ⟨rubiksList,rst1,g_split,h3_4,unChanged3,h3_6⟩ := h3
    -- 5.总结：命题所需的复合操作就是(rubiksList.prod)⁻¹
    simp only [exist_reachableG_cornerPermute_to1]
    use (rubiksList.prod)⁻¹
    have rubiksListElement_3items_is0or1 :∀b ∈ rubiksList, b.1.orient=0 ∧ b.2.permute=1 ∧ b.2.orient=0
      := by
      simp only [Prod.forall,h3_6]
      -- 很明显了。
      sorry
    have rubiksListElement_permuteIsThreeCycle :∀b ∈ rubiksList, IsThreeCycle b.1.permute
      := by
      -- h2_2
      -- 很明显了。
      sorry
    apply And.intro
    · have rubiksListElement_isReachable: ∀b ∈ rubiksList, Reachable b
        := by
        intro b binL
        have app1 := rubiksListElement_3items_is0or1 b binL
        have app2 := rubiksListElement_permuteIsThreeCycle b binL
        apply lemma31
        · exact rubiksListElement_permuteIsThreeCycle b binL
        simp only [app1];simp only [app1];simp only [app1]
      apply Reachable.inv
      -- simp [Reachable.mul,rubiksListElement_isReachable]
      -- 很明显了
      sorry
    rw [g_split]
    simp only [mul_inv_cancel_right]
    apply And.intro
    · exact h3_4
    rw [← g_split]
    apply And.intro
    · exact unChanged3.1.symm
    apply And.intro
    · exact unChanged3.2.2.symm
    · exact unChanged3.2.1.symm
    done




  -- 对于任意g状态棱块位置置换属于偶置换的状态，
    -- 则存在操作x1使得(g*x1)的棱块位置置换变成1，而且保持(g*x1)的角块位置不变，而且所有块的方向数不变。
    -- 这里x1的例子我们使用3循环的复合。
  lemma lemma15
  (g:RubiksSuperType)
  (h1:g.2.permute ∈ alternatingGroup (Fin 12))
  :exist_reachableG_edgePermute_to1 g
  := by
    -- 2.lemma31,lemma32:即所有满足这样的g:RubiksSuperType：
      -- {1.IsThreeCycle g.1.p ；2.g.1.o = 0 ；3.g.2.p=1 ; 4.g.2.o=0 }
      -- 都能通过群G复合生成。
    -- 3. 由于g.1.p 是偶的置换，使用这里面应该用到了closure_three_cycles_eq_alternating
      -- g.1.p 可以表示成3循环的乘积,这里记为threeList
    have h2 : ∃ (threeList:List (Perm (Fin 12))) ,
      (∀ g ∈ threeList, IsThreeCycle g)
      ∧
      (g.2.permute = threeList.prod)
      := by
      -- ???可能要用归纳法证明。思路：将偶置换表示成一长串3循环的乘积。
      sorry
    obtain ⟨permList,h2_2,h2_3⟩ := h2
    -- 4. 此处需要一个引理alternatingEdgePermute_eq_3Cycles_to_g_eq_3Cycles_mul_one来带入这个结论
      -- g可以表示成若干RubiksSuperType和一个rst1:RubiksSuperType的乘积，这里记为rubiksList.
      -- rubiksList满足：{对所有元素a，IsThreeCycle a.1.p；a.1.orient=0; a.2.permute=1; a.2.orient=0}
      -- rst1满足：{a.1.p = 1 ; a.1.orient=g.1.orient; a.2.permute=g.2.permute ; a.2.orient=g.2.orient}
    have h3 := alternatingEdgePermute_eq_3Cycles_to_g_eq_3Cycles_mul_one
      g permList h2_2 h2_3
    obtain ⟨rubiksList,rst1,g_split,h3_4,unChanged3,h3_6⟩ := h3
    -- 5.总结：命题所需的复合操作就是(rubiksList.prod)⁻¹
    simp only [exist_reachableG_edgePermute_to1]
    use (rubiksList.prod)⁻¹
    have rubiksListElement_3items_is0or1 :∀b ∈ rubiksList, b.1.orient=0 ∧ b.1.permute=1 ∧ b.2.orient=0
      := by
      simp only [Prod.forall,h3_6]
      -- 很明显了。
      sorry
    have rubiksListElement_permuteIsThreeCycle :∀b ∈ rubiksList, IsThreeCycle b.2.permute
      := by
      -- h2_2
      -- 很明显了。
      sorry
    apply And.intro
    · have rubiksListElement_isReachable: ∀b ∈ rubiksList, Reachable b
        := by
        intro b binL
        have app1 := rubiksListElement_3items_is0or1 b binL
        have app2 := rubiksListElement_permuteIsThreeCycle b binL
        apply lemma32
        · exact rubiksListElement_permuteIsThreeCycle b binL
        simp only [app1];simp only [app1];simp only [app1]
      apply Reachable.inv
      -- simp [Reachable.mul,rubiksListElement_isReachable]
      -- 很明显了
      sorry
    rw [g_split]
    simp only [mul_inv_cancel_right]
    apply And.intro
    · exact h3_4
    rw [← g_split]
    apply And.intro
    · exact unChanged3.1.symm
    apply And.intro
    · exact unChanged3.2.2.symm
    · exact unChanged3.2.1.symm
    done

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
  := by
    have cornerPermuteTo1 := lemma14 g h1
    obtain ⟨c1,c2,c3,c4,c5,c6⟩ := cornerPermuteTo1
    have EdgePermute_remains_in_aGroup: (g * c1).2.permute ∈ alternatingGroup (Fin 12)
      := by sorry
    have edgePermuteTo1 := lemma15 (g * c1) EdgePermute_remains_in_aGroup
    obtain ⟨e1,e2,e3,e4,e5,e6⟩ := edgePermuteTo1
    use (c1 * e1)
    apply And.intro
    · apply Reachable.mul
      {exact c2}
      {exact e2}
    apply And.intro
    · -- 用 c3,e3,还有计算结果
      sorry
      -- done
    · exact
      {left := by
        rw [← mul_assoc]
        simp only [c5,e5],
       right := by simp only [← mul_assoc,c6,e6]}
    done

  -- 化归思想，所有lemma12_condition1_restriction中的情况1可以通过魔方群操作变成情况2。
  /-- （奇X奇) → (偶X偶）-/
  lemma lemma13_oddXoddToEvenXEven
  (x: RubiksSuperType)
  (h3: (sign x.1.permute = -1 ∧ -1 = sign x.2.permute) )
  :
  ∃ (g: RubiksSuperType), -- 要找到一个定理是permute作用一个2轮换后，奇偶性会变换1次的。,举例操作是g5
    Reachable g
    ∧
    (sign (g * x).1.permute = 1 ∧ 1 = sign (g * x).2.permute)
  := by
    use (G5Perm)
    apply And.intro
    · simp only [G5Perm,G5Perm_element1]
      -- 这个很明显了
      sorry
      -- apply Reachable.mul
      -- apply Reachable.mul
      -- apply Reachable.mul
      -- apply Reachable.mul
      -- apply Reachable.mul
      -- apply Reachable.FT <;> simp only [FaceTurn.R,FaceTurn.U]
      -- 这里写完要很长，怎么节省代码呢？
      -- done
    · -- 缺一个lemma13_oddXoddToEvenXEven中的引理，角和棱位置各变换1次，符号会分别变1次。
      -- 就是这个：Equiv.Perm.sign (Equiv.swap x y) = -1
      sorry
    done

  lemma lemma13_EvenPermute_valid_isReachable
  (x: RubiksSuperType)
  (h3_2: sign x.1.permute = 1 ∧ 1 = sign x.2.permute)
  (hvx: x ∈ ValidCube)
  :Reachable x
  := by
    have xIsValid := hvx -- 后面被拆散了，先保留一个。
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
    have h2_9 := h1_4
    rw [h2_6] at h2_9
    let currStat := x * h1_2 * h2_3
    let currStat_satisfy: ((x * h1_2 * h2_3).2.orient = 0) ∧ ((x * h1_2 * h2_3).1.orient = 0)
      := { left := h2_5, right := h2_9 }
    -- ValidCube的条件1，限制了当前状态x的范围，所以可以进行2种分类讨论：1.（奇X奇) 2.(偶X偶）
    have h3 := hvx.1
    rw [lemma12_condition1_restriction] at h3
    -- //
    have h3_2_1 : (x * h1_2 * h2_3).1.permute ∈ alternatingGroup (Fin 8) := sorry
    have h3_2_2 : (x * h1_2 * h2_3).2.permute ∈ alternatingGroup (Fin 12) := sorry
    -- 使用lemma16使得新状态保持旧属性：方向数不变，获取新属性：角块+棱块的位置都变成1。
    have h3_2_3 := lemma16 (x * h1_2 * h2_3) h3_2_1 h3_2_2
    -- 很明显新状态就是还原状态Solved了，也就是已知下面这个y。
    obtain ⟨h3_2_4,h3_2_5,h3_2_6,h3_2_7,h3_2_8⟩ := h3_2_3
    obtain ⟨h3_2_9,h3_2_10⟩ := h3_2_6
    rw [h2_5] at h3_2_8
    rw [h2_9] at h3_2_7
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
    have h101 : Reachable y := by sorry
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
    exact hvx
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
        -- hc5 很明显的重排求和不变
        sorry
        done
      }
    }
  | split x y h1 h2 h3 h4 =>
    have h_split1: x⁻¹ ∈ ValidCube := by
      apply RubiksGroup.inv_mem'
      exact h4
    have h_split2:= RubiksGroup.mul_mem' h_split1 h3 -- 注意：条件不够就会分段报错
    have h_split_eq: (x⁻¹ * (x * y)) = y := by
      rw [← mul_assoc]
      simp only [mul_left_inv, one_mul]
    have h_split3: (y) ∈ ValidCube := by
      rw [← h_split_eq]
      exact h_split2
    exact h_split3
  done



-- 魔方第二基本定理的右推左部分：
theorem valid_reachable
: ∀x : RubiksSuperType, x ∈ ValidCube → Reachable x
:= by
  intro x hvx
  have xIsValid := hvx -- 后面被拆散了，先保留一个。
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
  have h2_9 := h1_4
  rw [h2_6] at h2_9
  let currStat := x * h1_2 * h2_3
  let currStat_satisfy: ((x * h1_2 * h2_3).2.orient = 0) ∧ ((x * h1_2 * h2_3).1.orient = 0)
    := { left := h2_5, right := h2_9 }
  -- ValidCube的条件1，限制了当前状态x的范围，所以可以进行2种分类讨论：1.（奇X奇) 2.(偶X偶）
  have h3 := hvx.1
  rw [lemma12_condition1_restriction] at h3
  have cornerpermute_Remains : (x * h1_2 * h2_3).1.permute = x.1.permute := by
    simp only [h2_7,h1_6]
  have edgepermute_Remains : (x * h1_2 * h2_3).2.permute = x.2.permute := by
    simp only [h2_8,h1_7]
  have corner_eqPermuteSign_edge : sign (x * h1_2 * h2_3).1.permute = sign (x * h1_2 * h2_3).2.permute := by
    simp only [cornerpermute_Remains,edgepermute_Remains,hvx.1]
  cases h3 with
  | inl h3_1 =>
    -- 操作是g5
    -- 某个过程，存在一个复合操作，作用一次到状态集合（奇X奇)上的某个元素后，
    -- 新状态会属于新的状态集合(偶X偶），归化成inr
    -- lemma13_oddXoddToEvenXEven
    -- lemma13_EvenPermute_valid_isReachable
    -- Reachable g →   Reachable g*x →  Reachable x
    have h3_1_1 := lemma13_oddXoddToEvenXEven x h3_1
    obtain ⟨od1,od2,od3,od4⟩ := h3_1_1
    have h3_1_2_1: od1 * x ∈ ValidCube := by
      apply RubiksGroup.mul_mem'
      · exact reachable_valid od1 od2
      · exact hvx
    have h3_1_2 := lemma13_EvenPermute_valid_isReachable (od1 * x) {left:=od3,right:=od4} h3_1_2_1
    -- 这里很明显了，但是是不是需要增加Reachable的定义呢？但是可能会影响左推右的过程，但问题不大。
    apply Reachable.split
    · exact h3_1_2
    · exact od2
  | inr h3_2 =>
    apply lemma13_EvenPermute_valid_isReachable
    · exact h3_2
    · exact hvx
    done
  -- 这里为啥还要证明已知的x ∈ ValidCube？原来是假设被拆散用了...
  exact hvx
  done



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

@[simp]
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

@[simp]
lemma solved_is_solved
: IsSolved (Solved)
:= by
  simp only [IsSolved, CornersSolved, EdgesSolved, Solved]
  apply And.intro
  { simp only [and_self] }
  { simp only [and_self]}
  done

@[simp]
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
-- -- 如何写成这样的子群的子群呢 ? instance TWGroup1_instance : Subgroup RubiksGroup := {
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
