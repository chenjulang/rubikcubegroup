import Lean
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Module.Equiv
import Mathlib.Data.Fin.Tuple.Reflection

open Equiv Perm
open BigOperators
set_option maxRecDepth 2000


-- instance (n : Nat) : Repr (Perm (Fin n)) :=
--     ⟨reprPrec ∘ Equiv.toFun⟩
-- -- instance (n : Nat) : DecidableEq (Perm (Fin n)) :=
-- --   λ a b => mk.injEq a.toFun a.invFun _ _ b.toFun b.invFun _ _ ▸ inferInstance
-- instance (n : Nat) : DecidableEq (Perm (Fin n)) := inferInstance

-- structure PieceState (pieces orientations: ℕ+) where
--   permute : Perm (Fin pieces)
--   orient : Fin pieces → Fin orientations -- 这里应该是增加量，不是绝对量
--   deriving Repr, DecidableEq

-- def ps_mul {p o : ℕ+} : PieceState p o → PieceState p o → PieceState p o :=
--     fun a1 a2 => {
--       permute := a2.permute * a1.permute -- *先运算右，再运算左。
--       orient := (a2.orient ∘ a1.permute) + a1.orient -- ∘是右边的函数作用到左边的对象
--     }
-- instance {p o : ℕ+} : Mul (PieceState p o) where
--   mul a1 a2 := {
--     permute := a2.permute * a1.permute
--     orient := (a2.orient ∘ a1.permute) + a1.orient
--   }

-- theorem permute_mul {p o : ℕ+} (a1 a2 : PieceState p o)
-- : (a1 * a2).permute = a2.permute * a1.permute
-- := by rfl
-- theorem orient_mul {p o : ℕ+} (a1 a2 : PieceState p o)
-- : (a1 * a2).orient = (a2.orient ∘ a1.permute) + a1.orient
-- := by rfl

-- lemma ps_mul_assoc {p o : ℕ+} :
--   ∀ (a b c : PieceState p o),
--   ps_mul (ps_mul a b) c = ps_mul a (ps_mul b c)
--   := by
--     intro a b c
--     simp only [ps_mul]
--     -- simp only [invFun_as_coe]
--     simp only [PieceState.mk.injEq] -- 两同类型对象相等，等价于，各分量相等。
--     apply And.intro
--     · simp only [Perm.mul_def]
--       simp only [Equiv.trans_assoc] -- A.trans B 指的是映射先看A，再看B
--     · simp only [coe_mul]
--       rw [← add_assoc]
--       simp only [add_left_inj]
--       rfl
--     done

-- lemma ps_one_mul {p o : ℕ+} :
--   ∀ (a : PieceState p o),
--   ps_mul {permute := 1, orient := 0} a  =  a
--   := by
--     intro a
--     simp only [ps_mul]
--     simp only [mul_one]
--     simp only [coe_one, Function.comp_id, add_zero]
--     done

-- lemma ps_mul_one {p o : ℕ+} :
-- ∀ (a : PieceState p o),
-- ps_mul a {permute := 1, orient := 0} = a := by
--   intro a
--   simp only [ps_mul]
--   simp only [one_mul, one_symm, coe_one, Function.comp_id, add_zero]
--   simp only [Pi.zero_comp, zero_add]
--   done

-- def ps_inv {p o : ℕ+}
--   : PieceState p o → PieceState p o
--   :=
--     fun ps =>
--     {
--       permute := ps.permute⁻¹
--       orient := fun x => (- ps.orient) (ps.permute⁻¹ x)
--     }
-- instance {p o : ℕ+} : Neg (PieceState p o) where
--     neg := fun
--       | .mk permute orient => {
--         permute := permute⁻¹
--         orient := fun x => (- orient) (permute⁻¹ x)
--       }

-- lemma ps_mul_left_inv {p o : ℕ+} :
--   ∀ (a : PieceState p o),
--   ps_mul (ps_inv a) a = {permute := 1, orient := 0}
--   := by
--     intro a
--     simp only [ps_inv]
--     simp only [ps_mul]
--     simp only [invFun_as_coe, PieceState.mk.injEq, true_and]
--     simp only [mul_right_inv, true_and]
--     have h1 : a.permute⁻¹.symm = a.permute := by rfl
--     have h2 : ((-a.orient) ∘ a.permute) ∘ a.permute.symm = (-a.orient)
--       := by exact (comp_symm_eq a.permute (-a.orient) ((-a.orient) ∘ ⇑a.permute)).mpr rfl
--     simp only [Pi.neg_apply]
--     exact neg_eq_iff_add_eq_zero.mp rfl

-- instance PieceGroup (p o: ℕ+) :
--   Group (PieceState p o) := {
--     mul := ps_mul -- 第一种运算，记为*
--     mul_assoc := ps_mul_assoc -- *的结合律
--     one := {permute := 1, orient := 0} -- *的单位1
--     one_mul := ps_one_mul -- 1 * ? = ?
--     mul_one := ps_mul_one -- ? * 1 = ?
--     inv := ps_inv -- (?)⁻¹ = ps_inv p o
--     mul_left_inv := ps_mul_left_inv -- (?)⁻¹ * (?) = 单位1
--   }

-- abbrev CornerType := PieceState 8 3
-- abbrev EdgeType := PieceState 12 2


-- abbrev RubiksSuperType := CornerType × EdgeType

-- def cyclePieces {α : Type*} [DecidableEq α] -- 这里如何文字上理解也是个问题，输入旧位置，得到新位置？
-- : List α → Perm α
-- := fun list =>  List.formPerm list
-- def Orient
-- (p o : ℕ+)
-- (pairs : List ((Fin p) × (Fin o)))
-- : Fin p → Fin o :=
--   fun i =>
--     match pairs.lookup i with
--     | some x => x
--     | none => 0

-- def Solved
-- : RubiksSuperType
-- where
--   fst := {
--     permute := 1
--     orient := 0
--   }
--   snd := {
--     permute := 1
--     orient := 0
--   }

-- def U : RubiksSuperType :=
--     ⟨
--       {permute := cyclePieces [0,3,2,1], orient := 0},
--       {permute := cyclePieces [0,3,2,1], orient := 0}
--     ⟩
-- def D : RubiksSuperType :=
--   ⟨
--     {permute := cyclePieces [4, 5, 6, 7], orient := 0},
--     {permute := cyclePieces [8, 9, 10, 11], orient := 0}
--   ⟩
-- def R : RubiksSuperType :=
--   ⟨
--     {permute := cyclePieces [1,2,6,5], orient := Orient 8 3 [(1, 2), (2, 1), (5, 1), (6, 2)]},
--     {permute := cyclePieces [1, 6, 9, 5], orient := Orient 12 2 [(1,1 ), (5,1 ), (6,1 ), (9,1 )]}
--   ⟩
-- def L : RubiksSuperType :=
--   ⟨
--     {permute := cyclePieces [0, 4, 7, 3], orient := Orient 8 3 [(0, 1), (3, 2), (4, 2), (7, 1)]},
--     {permute := cyclePieces [3,4 ,11 ,7 ], orient := Orient 12 2 [(3, 1), (4,1 ), (7, 1), (11, 1)]}
--   ⟩
-- def F : RubiksSuperType :=
--   ⟨
--     {permute := cyclePieces [0,1 ,5 ,4 ], orient := Orient 8 3 [(0, 2), (1, 1), (4, 1), (5, 2)]},
--     {permute := cyclePieces [0, 5, 8, 4] , orient :=  Orient 12 2 [(0, 0), (4, 0), (5, 0), (8, 0)]}
--   ⟩
-- def B : RubiksSuperType :=
--   ⟨
--     {permute := cyclePieces [2, 3, 7,6 ], orient := Orient 8 3 [(2, 2), (3, 1), (6, 1), (7, 2)]},
--     {permute := cyclePieces [2, 7, 10,6 ], orient := Orient 12 2 [(2, 0), (6, 0), (7, 0), (10, 0)]}
--   ⟩
-- def U2 := U^2
-- def D2 := D^2
-- def R2 := R^2
-- def L2 := L^2
-- def F2 := F^2
-- def B2 := B^2
-- def U' := U⁻¹
-- def D' := D⁻¹
-- def R' := R⁻¹
-- def L' := L⁻¹
-- def F' := F⁻¹
-- def B' := B⁻¹


-- def G1Perm_element : RubiksSuperType
--   := R' * D * D * R * B' * U * U * B
-- def G1Perm : RubiksSuperType
--   := G1Perm_element^2

-- #eval (F * G1Perm * F').1.permute = 1 -- true

-- lemma Test001
-- :(F * G1Perm * F').1.permute = 1
-- := by decide


-- @[to_additive]
-- lemma _root_.Equiv.prod_comp (e : ι ≃ κ) (g : κ → α)
-- : ∏ i, g (e i) = ∏ i, g i
-- :=
--   prod_equiv e _ _ fun _ ↦ rfl

-- lemma Test002
-- (apermute : Perm (Fin 3))
-- (borient : (Fin 3) → Fin 2)
-- (h2: Finset.sum {0, 1, 2} borient = 0)
-- : (Finset.sum {0, 1, 2} fun x ↦ borient (apermute x)) = 0
-- := by
--   have h1:= Equiv.sum_comp apermute borient -- 常见错误：因为没有输入足够的参数 typeclass instance problem is stuck, it is often due to metavariables
--   -- AddCommMonoid ?m.1493
--   -- have sumEq :  ∑ i : Fin 3 ,i =  ∑ i in {0, 1, 2},i := by
--   --   simp only [Finset.mem_insert,false_or, implies_true, Finset.sum_insert_of_eq_zero_if_not_mem]
--   --   decide -- rfl
--   have sumEq2 : ∑ i : Fin 3, borient (apermute i) = ∑ x in {0, 1, 2}, borient (apermute x) := rfl
--   rw [← sumEq2]
--   clear sumEq2
--   rw [h1]
--   clear h1
--   have sumEq1 : ∑ i : Fin 3, borient i = Finset.sum {0, 1, 2} borient := rfl
--   rw [sumEq1]
--   exact h2
--   done
-- -- Finset.sum_equiv


-- lemma Test003
-- (apermute : Perm (Fin 12))
-- (borient : (Fin 12) → Fin 2)
-- (h2: Finset.sum {0, 1, 2,3,4,5,6,7,8,9,10,11} borient = 0)
-- : (Finset.sum {0, 1, 2,3,4,5,6,7,8,9,10,11} fun x ↦ borient (apermute x)) = 0
-- := by
--   have h1:= Equiv.sum_comp apermute borient -- 常见错误：因为没有输入足够的参数 typeclass instance problem is stuck, it is often due to metavariables
--   have sumEq2 : ∑ i : Fin 12, borient (apermute i) = ∑ x in {0, 1, 2,3,4,5,6,7,8,9,10,11}, borient (apermute x) := rfl
--   rw [← sumEq2]
--   clear sumEq2
--   rw [h1]
--   clear h1
--   have sumEq1 : ∑ i : Fin 12, borient i = Finset.sum {0, 1, 2,3,4,5,6,7,8,9,10,11} borient := rfl
--   rw [sumEq1]
--   exact h2
--   done



  -- intro x
  -- induction n
  -- simp at x
  -- rename_i i j
  -- have h: 2 * Nat.succ i + 1 = 2 * i + 1 + 2 := by linarith
  -- rw [h] at x
  -- rw [Nat.mod_eq_sub_mod] at x
  -- simp at x
  -- exact j x
  -- linarith

  -- #check Finset.sum_bij


  -- 改进证明：
  variable {α : Type*}

  example [AddCommMonoid α] (a : Fin 3 → α) : ∑ i, a i = a 0 + a 1 + a 2 :=
  (FinVec.sum_eq _).symm





  variable {β : Type*}
  @[to_additive]
  theorem prod_univ_9 [CommMonoid β] (f : Fin 9 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8
  := by
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_eight]
    rfl
  @[to_additive]
  theorem prod_univ_10 [CommMonoid β] (f : Fin 10 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9
  := by
    rw [Fin.prod_univ_castSucc, prod_univ_9]
    rfl
  @[to_additive]
  theorem prod_univ_11 [CommMonoid β] (f : Fin 11 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 * f 10
  := by
    rw [Fin.prod_univ_castSucc, prod_univ_10]
    rfl
  @[to_additive]
  theorem prod_univ_12 [CommMonoid β] (f : Fin 12 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 * f 10 * f 11
  := by
    rw [Fin.prod_univ_castSucc, prod_univ_11]
    rfl

  -- 如何将这些比较复杂的tactic由simp？或apply?自动提醒比如：(FinVec.sum_eq _).symm ,这就要设计macro了。
  lemma testSum2'
  (fn: Fin 12 → Fin 10)
  : ∑ i in {0,1,2,3,4,5,6,7,8,9,10,11}, fn i = fn 0 + fn 1 + fn 2 + fn 3 + fn 4+ fn 5+ fn 6 + fn 7+ fn 8+ fn 9+ fn 10+ fn 11
  := (FinVec.sum_eq _).symm

  lemma testSum2
  (fn: Fin 12 → Fin 10)
  : ∑ i in {0,1,2,3,4,5,6,7,8,9,10,11}, fn i = fn 0 + fn 1 + fn 2 + fn 3 + fn 4+ fn 5+ fn 6 + fn 7+ fn 8+ fn 9+ fn 10+ fn 11
  := by
    apply sum_univ_12 fn

  lemma testSum'
  (fn: Fin 3 → Fin 10)
  : ∑ i in {0,1,2}, fn i = fn 0 + fn 1 + fn 2
  := by
    exact (FinVec.sum_eq _).symm

  lemma testSum
  (fn: Fin 3 → Fin 10)
  : ∑ i in {0,1,2}, fn i = fn 0 + fn 1 + fn 2
  := by
    apply Fin.sum_univ_three _
    done

  lemma Test004_2
  (apermute : Perm (Fin 3))
  (borient : (Fin 3) → (Fin 3))
  (h2: Finset.sum {0, 1, 2} borient = 0)
  : (Finset.sum {0, 1, 2} fun x ↦ borient (apermute x)) = 0
  := by
    have h1:= Equiv.sum_comp apermute borient -- 常见错误：因为没有输入足够的参数 typeclass instance problem is stuck, it is often due to metavariables
    have sumEq2 : ∑ i : Fin 3, borient (apermute i) = ∑ x in {0, 1, 2}, borient (apermute x) := rfl
    rw [← sumEq2]
    clear sumEq2
    rw [h1]
    clear h1
    have sumEq1 : ∑ i : Fin 3, borient i = Finset.sum {0, 1, 2} borient := rfl
    rw [sumEq1]
    exact h2
    done

  lemma Test004_1
  (gorient: Fin 3 → Fin 3)
  (gpermute: Perm (Fin 3))
  : ∑ i in {0,1,2}, (gorient ∘ gpermute) i
  = (gorient ∘ gpermute) 0
  + (gorient ∘ gpermute) 1
  + (gorient ∘ gpermute) 2
    := by
    set fn := (gorient ∘ gpermute)
    -- apply Fin.sum_univ_three _
    exact (FinVec.sum_eq _).symm
    -- simp only [Function.comp_apply]
    -- simp only [Finset.mem_insert, or_self, not_false_eq_true,Finset.sum_insert,
    -- Finset.mem_singleton, OfNat.one_ne_ofNat]
    -- sorry


lemma Test004
(gorient: Fin 3 → Fin 3)
(gpermute: Perm (Fin 3))
(h1: Finset.sum {0,1,2} gorient = 0)
(h2:
gorient (gpermute 0) = 0
∧
gorient (gpermute 1) = 0
)
:gorient (gpermute 2) = 0
:= by
  by_cases ha0:(gorient (gpermute 2))=1
  {
    obtain ⟨h2_1,h2_2⟩ := h2
    have h3: ∑ x in {0, 1, 2}, gorient (gpermute x) = Finset.sum {0,1,2} (gorient ∘ gpermute)
    := by rfl
    have h4_2 : Finset.sum {0,1,2} (gorient ∘ gpermute) = ∑ i in {0,1,2}, (gorient ∘ gpermute) i := by rfl
    have h4_1 : ∑ i in {0,1,2}, (gorient ∘ gpermute) i = (gorient ∘ gpermute) 0 +(gorient ∘ gpermute) 1 + (gorient ∘ gpermute) 2
      := by exact Test004_1 gorient gpermute
    have h4: Finset.sum {0,1,2} (gorient ∘ gpermute) = 1
      := by
      simp only [Function.comp_apply]
      rw [h3]
      rw [h4_2]
      rw [h4_1]
      simp only [Function.comp_apply]
      rw [h2_1,h2_2]
      simp only [add_zero, zero_add,ha0]
    have h5: Finset.sum {0, 1, 2} (gorient ∘ gpermute) = 0 := by
      have h5_1 := Test004_2 gpermute gorient-- Test003类似的工作
      apply h5_1 at h1
      exact h1
    clear h3 h2_1 h2_2 ha0 h1
    have h6: Finset.sum {0, 1, 2} (gorient ∘ ⇑gpermute) ≠ 1 := by
      rw [h5]
      exact Fin.zero_ne_one
    exact (h6 h4).elim
  }


  -- def pairingFunction (i j : ℕ) : ℕ :=
  -- ((i + j) * (i + j + 1)) / 2 + j

  -- def inversePairingFunction (k : ℕ) : ℕ × ℕ
  -- := by
  --   let w := Nat.floor ((Nat.sqrt (8 * k + 1) - 1) / 2)
  --   let t := (w * w + w) / 2
  --   let y := k - t
  --   exact (y, w - y)

  -- #eval pairingFunction 2 3
  -- #eval inversePairingFunction 11
