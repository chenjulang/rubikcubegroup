import Lean
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Module.Equiv

-- set_option maxHeartbeats 800000
set_option maxRecDepth 4000


open Equiv Perm
open BigOperators

section RubiksSuperGroup

  -- 举例：
  -- def testInst1 : (Perm (Fin 8)) where
  --   toFun := fun
  --     | .mk val isLt => val +1
  --   invFun := fun
  --     | .mk val isLt => val -1
  --   left_inv := by decide
  --   right_inv := by decide
  -- #eval testInst1.toFun -- ![1, 2, 3, 4, 5, 6, 7, 0]
  -- #check (Repr.reprPrec ∘ testInst1.toFun)
  -- #eval testInst1.toFun 7  -- 0
  -- #eval Repr.reprPrec (0:(Fin 8)) 999  -- 0
  -- #eval (Repr.reprPrec ∘ testInst1.toFun) 7 3 -- 0

  -- 这个实例声明表明对于任意的 n : Nat，类型 Perm (Fin n) 具有 Repr 实例。
  -- 在 Lean 中，Repr 是一个类型类，用于定义类型的外部表示形式。它提供了将值转换为字符串的方法，以便在打印输出和调试信息中使用。
  -- 例如，当你在 Lean 中使用 #eval 命令打印一个值时，它将使用 Repr 实例将该值转换为字符串进行显示。
  -- 该实例声明的右侧是一个匿名构造子，它使用了函数合成操作符 (∘) 来组合两个函数：reprPrec 和 Equiv.toFun。
  -- reprPrec 是一个内置函数，用于将值转换为字符串的表示形式，而 Equiv.toFun 是一个类型为 Equiv α β → α → β 的函数，
    -- 它将一个等价关系 Equiv 转换为一个函数。
  -- 因此，整个实例声明的含义是，对于类型 Perm (Fin n)，我们可以使用函数合成的方式将其转换为字符串表示形式。
    -- 这意味着在打印输出或调试信息中，Perm (Fin n) 类型的值将以字符串的形式显示。
  -- 如果去掉：下面代码的structure PieceState 会报错： failed to synthesize instance Repr (Perm (Fin ↑pieces✝))
  instance (n : Nat) : Repr (Perm (Fin n)) :=
    ⟨reprPrec ∘ Equiv.toFun⟩



  -- 在 Lean 中，instance 关键字用于声明类型类的实例。在这个例子中，instance (n : Nat) : DecidableEq (Perm (Fin n))
    -- 声明了一个 DecidableEq (Perm (Fin n)) 类型类的实例，其中 (n : Nat) 表示这个实例是一个依赖于 n 的类型。
  -- DecidableEq 是一个类型类，表示类型具有可判定相等性的能力，即可以判断两个值是否相等。
    -- 在这个例子中，(Perm (Fin n)) 是一个表示有限集合上的置换的类型，因此这个实例表示对于任意自然数 n，Perm (Fin n) 类型上都存在可判定相等性。
    -- 而 := inferInstance 则是使用类型类的隐式实例解析机制来推断和生成这个实例。这意味着编译器会根据上下文自动搜索并生成满足
    -- DecidableEq (Perm (Fin n)) 类型类约束的实例。
  -- 因此，这行代码的含义是声明了一个依赖于 n 的 DecidableEq 类型类实例，用于在有限集合上的置换类型上判断相等性，
    -- 并使用了类型类隐式实例解析机制来自动生成这个实例。
  -- 如果去掉：好像没影响。
  instance (n : Nat) : DecidableEq (Perm (Fin n)) := inferInstance

  /- This PieceState structure is used to represent the entire state of both corner pieces and edge pieces.-/
  /-- 可以看成全体角块，或全体棱块。为方便讲解，目前语境先当成是全体角块。-/
  structure PieceState (pieces orientations: ℕ+) where
    permute : Perm (Fin pieces)
    orient : Fin pieces → Fin orientations -- 这里是增加量，不是绝对量
    -- 去掉这一行结果，
      -- 1.丢失了一些打印的功能："{repr c}" 报错：failed to synthesize instance Repr RubiksSuperType
      -- 2.也无法处理相等的判断：if c = Solved then "Solved"： failed to synthesize instance Decidable (c = Solved)
    deriving Repr, DecidableEq

  -- 举例：
  -- def testP1: Perm (Fin 8) := List.formPerm ([1,2,3])
  -- def testP2: Perm (Fin 8) := List.formPerm ([2,3,4])
  -- #eval testP1 -- ![0, 2, 3, 1, 4, 5, 6, 7]
    -- 实际理解应该这样： ![0=>0,1=>2, 2=>3, 3=>1, 4=>4, 5=>5, 6=>6, 7=>7] ;
    -- 0=>0 定义：“索引位置”0的数A在变换后，新的“索引位置”是0; 换句话说，位置没变。
    -- 1=>2 定义：“索引位置”1的数A在变换后，新的“索引位置”是2
    -- 举例testP1代表这样的一个重排列：
    --        {a,b,c,d,e,f,g,h}
    --        →
    --        {a,d,b,c,e,f,g,h}
  -- #eval testP2 -- ![0, 1, 3, 4, 2, 5, 6, 7]
    -- 实际理解应该这样写： ![0=>0,1=>1, 2=>3, 3=>4, 4=>2, 5=>5, 6=>6, 7=>7] ;
  -- 那如何理解乘法呢？testP2 * testP1
    -- 这里看的顺序要从右开始看。先进行testP1变换，在进行testP2变换。
    -- testP1 = ![0=>0,1=>2, 2=>3, 3=>1, 4=>4, 5=>5, 6=>6, 7=>7]
    -- testP2 = ![0=>0,1=>1, 2=>3, 3=>4, 4=>2, 5=>5, 6=>6, 7=>7]
    -- 举例：
    -- “索引位置”1的数，经过testP1得到新的“索引位置”2，再经过testP2,得到新的“索引位置”3。总结就是1=>3
    -- “索引位置”2的数，经过testP1得到新的“索引位置”3，再经过testP2,得到新的“索引位置”4。总结就是2=>4
    -- “索引位置”3的数，经过testP1得到新的“索引位置”1，再经过testP2,得到新的“索引位置”1。总结就是3=>1
    -- “索引位置”4的数，经过testP1得到新的“索引位置”4，再经过testP2,得到新的“索引位置”2。总结就是4=>2
    -- 写成向量就是 = ![0,1=>3,2=>4,3=>1,4=>2,5,6,7]
    -- 简化后就是 ![0,3,4,1,2,5,6,7]
  -- #check Perm.mul_def -- permute的乘法就是这样定义的。
  -- #eval testP2 * testP1 -- ![0, 3, 4, 1, 2, 5, 6, 7]


  -- 举例：(a2.orient ∘ a1.permute) + a1.orient
    -- 比如，取值如下：
    -- a.1.permute = ![1,2,0,3,4,5,6,7]
    -- a.2.orient =  ![o0,o1,o2,o3,o4,o5,o6,o7]
  -- 问题来了：  ρ(g)^(-1)·v(h) + v(g) 要怎么用a1.orient，a1.permute，a2.orient来表示出来呢？
  -- 1. 首先v(g)等价于a1.orient。
  -- 2. 然后v(h)等价于a2.orient。
  -- 3. ρ(g)的重排列效果 等价于 a.1.permute的重排列效果。
      -- 先看看a.1.permute和ρ(g)的重排列效果：
      -- 先写成[0=>1,1=>2,2=>0,3=>3,4=>4,5=>5,6=>6,7=>7]
      -- 重排列效果也就是：
      --        {a,b,c,d,e,f,g,h}
      --        →
      --        {c,a,b,d,e,f,g,h}
      -- 然后分析逆操作ρ(g)^(-1)重排列效果：
      -- 很容易知道就是反着写：[0<=1,1<=2,2<=0,3<=3,4<=4,5<=5,6<=6,7<=7]
      -- 改写一下 [0=>2,1=>0,2=>1,3=>3,4=>4,5=>5,6=>6,7=>7]
  -- 4. 因此ρ(g)^(-1)·v(h)的效果是ρ(g)^(-1)重排列作用在v(h)上，
    -- v(h) = ![o0,o1,o2,o3,o4,o5,o6,o7]
    -- 经过变换[0=>2,1=>0,2=>1,3=>3,4=>4,5=>5,6=>6,7=>7]
    -- 得到 ![o1,o2,o0,o3,o4,o5,o6,o7]
  -- 5. 现在回到原来的问题 ρ(g)^(-1)·v(h) + v(g) 要怎么用a1.orient，a1.permute，a2.orient来表示出来呢？
    -- 先撇开一个加项v(g)不管
    -- 问题剩下了：ρ(g)^(-1)·v(h) 要怎么用a1.permute，a2.orient来表示出来呢？
    -- 也就是![o1,o2,o0,o3,o4,o5,o6,o7] 怎么用a1.permute，a2.orient来表示出来呢？
      -- 先列出a.1.permute = [0=>1,1=>2,2=>0,3=>3,4=>4,5=>5,6=>6,7=>7]
      -- a2.orient = ![o0,o1,o2,o3,o4,o5,o6,o7]
    --
    -- 不妨去掉不变的部分看的更清晰：
    -- 也就是![o1,o2,o0,-,-,-,-,-] 怎么用a1.permute，a2.orient来表示出来呢？
      -- 先列出a.1.permute = [0=>1,1=>2,2=>0,-,-,-,-,-]
      -- a2.orient = ![o0,o1,o2,-,-,-,-,-]
    -- [o1,o2,o0,-,-,-,-,-] = F([0=>1,1=>2,2=>0,-,-,-,-,-],[o0,o1,o2,-,-,-,-,-])
    -- 这样的F要怎么构造呢？
    -- 左边：输入0，得到o1
    --      输入0，得到o2
    --      输入0，得到o0
    -- 右边：输入0。可以这样构造：先通过第一个参数映射，0就变成了1；再将1代入第二个参数（是一个向量）就得到了o1。
    --      这样，输入1，得到2,再得到o2
    --      输入2，得到0，再得到o0
    -- 刚好左右相等，这样构造就可以了。
    -- 先通过第一个参数映射，0就变成了1；再将1代入第二个参数：这个过程写成lean就是(a2.orient ∘ a1.permute)
    -- 因为lean里面这个复合映射(a2.orient ∘ a1.permute)表示先通过a1.permute映射，再通过a2.orient映射。


  def ps_mul {p o : ℕ+} : PieceState p o → PieceState p o → PieceState p o :=
    fun a1 a2 => {
      permute := a2.permute * a1.permute -- *先映射右，再映射左。 -- 为什么呢？看例子testP1,testP2
      orient := (a2.orient ∘ a1.permute) + a1.orient -- 复合函数计算顺序:右→左
    }


  -- 将上面替换成下面的等价写法，好处：1.可以到处写*，来代替ps_mul，lean系统会自动匹配到这个*的类型用法。
  -- 实际上就是定义了PieceState的其中一种2元乘法运算。当然你最想定义多少种乘法运算都可以。但我们只想要这个，也只有这个能有进展。
  instance {p o : ℕ+} : Mul (PieceState p o) where
    mul a1 a2 := {
      permute := a2.permute * a1.permute
      orient := (a2.orient ∘ a1.permute) + a1.orient
    }


  -- 这里可以写*，来代替ps_mul
  /-- 先“PieceState乘”后p = 先p后“PieceState乘” -/
  @[simp]
  theorem permute_mul {p o : ℕ+} (a1 a2 : PieceState p o)
  : (a1 * a2).permute = a2.permute * a1.permute
  := by rfl
  @[simp]
  theorem orient_mul {p o : ℕ+} (a1 a2 : PieceState p o)
  : (a1 * a2).orient = (a2.orient ∘ a1.permute) + a1.orient
  := by rfl

-- #check PieceState.mk.injEq

  /-- PieceState乘法的结合律 -/
  @[simp]
  lemma ps_mul_assoc {p o : ℕ+} :
  ∀ (a b c : PieceState p o),
  ps_mul (ps_mul a b) c = ps_mul a (ps_mul b c)
  := by
    intro a b c
    simp only [ps_mul]
    simp only [PieceState.mk.injEq] -- ***两同类型对象相等，等价于，各分量相等。
    apply And.intro
    · simp only [Perm.mul_def]
      ext i
      rw [trans_apply]
      rw [trans_apply]
      rw [trans_apply]
      rw [trans_apply]
    · simp only [coe_mul] -- 乘法号 和 复合符号 效果是一样的。
      rw [← add_assoc]
      simp only [add_left_inj]
      ext i
      simp only [Pi.add_apply]
      simp only [Function.comp_apply] -- 去掉复合符号
      simp only [Pi.add_apply]
      simp only [Function.comp_apply]
    done

  /-- PieceState乘法的左单位元 -/
  @[simp]
  lemma ps_one_mul {p o : ℕ+} :
  ∀ (a : PieceState p o),
  ps_mul {permute := 1, orient := 0} a = a
  := by
    intro a
    simp only [ps_mul]
    simp only [mul_one]
    simp only [coe_one, Function.comp_id, add_zero]
    done

  /-- PieceState乘法的右单位元 -/
  @[simp]
  lemma ps_mul_one {p o : ℕ+} :
  ∀ (a : PieceState p o),
  ps_mul a {permute := 1, orient := 0} = a := by
    intro a
    simp only [ps_mul]
    simp only [one_mul, one_symm, coe_one, Function.comp_id, add_zero]
    simp only [Pi.zero_comp, zero_add]
    done

  /-- PieceState乘法的普通元素的右逆 -/
  def ps_inv {p o : ℕ+}
  : PieceState p o → PieceState p o
  :=
    fun A =>
    {
      permute := A.permute⁻¹
      orient := fun x => (- A.orient) (A.permute⁻¹ x)
      -- 问题是：如何定义这个PieceState对象，使得A*B = 1, 也就是(ps_mul A ?）.orient = 0 呢？
      -- 解开(ps_mul A ?）.orient 看一下：
      -- (ps_mul A ?）.orient =  (a2.orient ∘ A.permute) + A.orient
      -- 如果要上面这个等于0，只需要满足：(a2.orient ∘ A.permute) + A.orient = 0
      -- 只需要满足 ：(a2.orient ∘ A.permute)  = -A.orient
      -- 只需要满足 ：(a2.orient ∘ A.permute) x = (-A.orient) x
      -- 只需要满足 ：a2.orient (A.permute x) = (-A.orient) x
      -- a2.orient y = (-A.orient) x ; y= (A.permute x)
      -- A.permute⁻¹ y = A.permute⁻¹ (A.permute x) = x
      -- 只需要满足 ：a2.orient (y) = (-A.orient) (A.permute⁻¹ y)
    }

  -- 当然，上面的推理过程也是可以证明的，来看看lean是怎么证明的，截然不同的思路：
  /- 证明右逆的定义合理性：-/
  @[simp]
  lemma ps_mul_right_inv {p o : ℕ+} :
  ∀ (a : PieceState p o),
  ps_mul a (ps_inv a)  = {permute := 1, orient := 0}
  := by
    intro a
    simp only [ps_mul]
    simp only [ps_inv]
    simp only [mul_left_inv]
    simp only [Pi.neg_apply]
    simp only [PieceState.mk.injEq]
    simp only [true_and]
    ext i
    simp only [Pi.add_apply]
    simp only [Function.comp_apply]
    simp only [inv_apply_self]
    simp only [add_left_neg]
    simp only [Fin.val_zero']
    simp only [Pi.zero_apply]
    simp only [Fin.val_zero']
    done

  -- 类似Mul， 右逆元素简写成符号“-”。
  instance {p o : ℕ+} : Neg (PieceState p o) where
    neg := fun
      | .mk permute orient => {
        permute := permute⁻¹
        orient := fun x => (- orient) (permute⁻¹ x)
      }


  -- 定义右的逆后，证明右的逆，左乘也为1：
  @[simp]
  lemma ps_mul_left_inv {p o : ℕ+} :
  ∀ (a : PieceState p o),
  ps_mul (ps_inv a) a = {permute := 1, orient := 0}
  := by
    intro a
    simp only [ps_inv]
    simp only [ps_mul]
    simp only [PieceState.mk.injEq]
    simp only [Pi.neg_apply]
    simp only [mul_right_inv]
    simp only [true_and]
    apply neg_eq_iff_add_eq_zero.1
    ext i
    simp only [Pi.neg_apply]
    simp only [Function.comp_apply]


  /- This sets up a group structure for all Rubik's cube positions
  (including invalid ones that couldn't be reached from a solved state without
  removing pieces from the cube,
  twisting corners, etc.). -/
  /-- 一个由角块（棱块）状态组成的群。当然，现在这样说还是比较狭隘的。因为有可能是魔方正常操作不能到达的状态。 -/
  instance PieceGroup (p o: ℕ+) :
  Group (PieceState p o) := {
    mul := ps_mul -- 提供一种PieceState的二元乘法运算，这里提供了ps_mul。
    mul_assoc := ps_mul_assoc -- 证明：上面乘法的结合律
    one := {permute := 1, orient := 0} -- 提供一种乘法运算的单位1
    one_mul := ps_one_mul -- 证明：上面的单位1左乘任意元素不变
    mul_one := ps_mul_one -- 证明：上面的单位1右乘任意元素不变
    inv := ps_inv -- 提供一个函数，输入一个PieceState对象，得到一个PieceState的逆对象。
    mul_left_inv := ps_mul_left_inv -- 证明:上面生成逆对象的函数生成的逆对象，左乘原对象结果为1
  }


  @[simp]
  lemma PieceState.mul_def {p o : ℕ+} (a b : PieceState p o)
  : a * b  = ps_mul a b := by rfl
  @[simp]
  lemma PieceState.inv_def {p o : ℕ+} (a b : PieceState p o)
  : a⁻¹ = ps_inv a := by rfl


  abbrev CornerType := PieceState 8 3
  abbrev EdgeType := PieceState 12 2


  -- #check PieceGroup 24 2 -- 四阶魔方的棱块应该也符合。
  -- PieceGroup 输入任意2个值都可以形成一个群。并且满足结合律，左逆等。

  instance RubiksCornerGroup :
  Group CornerType
  := PieceGroup 8 3
  instance RubiksEdgeGroup :
  Group EdgeType
  := PieceGroup 12 2

  /-- 简单笛卡尔积凑在一起了。这个就是魔方超群。 -/
  abbrev RubiksSuperType := CornerType × EdgeType

  @[simp]
  lemma RubiksSuperType_mul_assoc :
  ∀ (a b c : RubiksSuperType),
  a * b * c = a * (b * c)
  := by
    simp only [Prod.forall, Prod.mk_mul_mk, PieceState.mul_def, ps_mul_assoc, forall_const]
    done

  instance RubiksSuperGroup -- 就是手写证明中的群H
  : Group RubiksSuperType
  := by exact Prod.instGroup -- 应该就是笛卡尔积元素组成的群，第一种运算为：“每一个分量本身的运算，运算结果的某个分量就是这个分量的运算结果”。

end RubiksSuperGroup

-- 下面开始为魔方的6个基本操作的定义做铺垫：

-- List.lookup用法,换句话说就是找匹配第一个分量，如果匹配到返回存在，还有该项的第二个分量：
#eval List.lookup 3 [(1, 2), (3, 4), (3, 5)] = some 4
#eval List.lookup 2 [(1, 2), (3, 4), (3, 5)] = none


/- Creates an orientation function given a list of input-output pairs
(with 0 for anything left unspecified). -/
/-- 为了方便定义每个操作的"方向数增加量"orient,然后定义的这两个东西： -/
def Orient
(p o : ℕ+)
(pairs : List ((Fin p) × (Fin o)))
: Fin p → Fin o :=
  fun i =>
    match pairs.lookup i with
    | some x => x
    | none => 0
-- 举例说明：
-- 比如为了创建这个向量：![1, 0, 2, 2, 0, 1, 0, 0]，这样输入参数。8项分量，每一项为Fin 3,即小于3。
-- #eval Orient 8 3 [(0, 1), (1, 0), (2, 2), (3, 2), (4, 0), (5, 1), (6, 0), (7, 0)] -- ![1, 0, 2, 2, 0, 1, 0, 0]


def Solved
: RubiksSuperType
where
  fst := {
    permute := 1
    orient := 0
  }
  snd := {
    permute := 1
    orient := 0
  }

@[simp]
lemma Solved_eq_1: Solved = 1 :=by rfl

@[simp]
lemma Solved_iff
(x: RubiksSuperType)
:
(Solved = x)
↔
(x.1.permute=1 ∧ x.2.permute=1 ∧ x.1.orient=0 ∧ x.2.orient=0)
:= by
  constructor
  · simp only [Solved]
    intro x
    cases x
    apply And.intro
    { rfl}
    { apply And.intro
      {rfl}
      apply And.intro
      {rfl}
      {rfl}
    }
  · intro hx
    obtain ⟨hx1,hx2,hx3,hx4⟩:= hx
    simp only [Solved]
    congr
    {exact id hx1.symm}
    {exact id hx3.symm}
    {exact id hx2.symm}
    {exact id hx4.symm}
    done



section FACE_TURNS

  -- 为了方便定义每个操作的“位置变化”：排列permute,然后定义的这个东西：

  -- -- 只用formPerm可以办到，但是输入时要转一下脑筋：
  def lista : List (Fin 8) := [0,3,2,1] -- 这样写得到的Perm意思是：
  -- [0,3,2,1]表示：0=>3；3=>2；2=>1；1=>0
  -- 整理后就是： [0=>3,1=>0,2=>1,3=>2]
  #eval List.formPerm lista

  /- These two functions (from kendfrey's repository) create a cycle permutation,
  which is useful for defining the rotation of any given face, as seen directly below. -/
  def cyclePieces {α : Type*} [DecidableEq α]
  : List α → Perm α
  := fun list =>  List.formPerm list




  -- 第1大括号"{}"内描述的是：角块
    -- permute描述的是位置变化，orient描述的是方向数变化。
  -- 第2大括号"{}"内描述的是：棱块
    -- permute描述的是位置变化，orient描述的是方向数变化。

  -- 这里注释一下下面每个位置对应的块是哪个，比如UFR这样的：
  --   ({ permute := ![UFL, UFR, UBR, UBL, DFL, DFR, DBR, DBL],
  --    orient := ![UFL, UFR, UBR, UBL, DFL, DFR, DBR, DBL] },
  --  { permute := ![UF, UR, UB, UL, FL, FR, RB, LB, FD, RD, BD, LD],
  --    orient := ![UF, UR, UB, UL, FL, FR, RB, LB, FD, RD, BD, LD] })

  def U : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [0,3,2,1], orient := 0},
      -- 即：0=>3,3=>2,2=>1,1=>0
      -- 整理：[3,0,1,2,4,5,6,7]
      {permute := cyclePieces [0,3,2,1], orient := 0}
    ⟩
  def D : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [4, 5, 6, 7], orient := 0},
      {permute := cyclePieces [8, 9, 10, 11], orient := 0}
    ⟩
  def R : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [1,2,6,5], orient := Orient 8 3 [(1, 2), (2, 1), (5, 1), (6, 2)]},
      {permute := cyclePieces [1, 6, 9, 5], orient := Orient 12 2 [(1,1 ), (5,1 ), (6,1 ), (9,1 )]}
    ⟩
  def L : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [0, 4, 7, 3], orient := Orient 8 3 [(0, 1), (3, 2), (4, 2), (7, 1)]},
      {permute := cyclePieces [3,4 ,11 ,7 ], orient := Orient 12 2 [(3, 1), (4,1 ), (7, 1), (11, 1)]}
    ⟩
  def F : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [0,1 ,5 ,4 ], orient := Orient 8 3 [(0, 2), (1, 1), (4, 1), (5, 2)]},
      {permute := cyclePieces [0, 5, 8, 4] , orient :=  Orient 12 2 [(0, 0), (4, 0), (5, 0), (8, 0)]}
    ⟩
  def B : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [2, 3, 7,6 ], orient := Orient 8 3 [(2, 2), (3, 1), (6, 1), (7, 2)]},
      {permute := cyclePieces [2, 7, 10,6 ], orient := Orient 12 2 [(2, 0), (6, 0), (7, 0), (10, 0)]}
    ⟩
  -- 中层（U和D的中层）的顺时针90旋转。通常用于桥式还原法。
  -- def M_UD : RubiksSuperType :=
  --   ⟨
  --     {permute := 1, orient := 0 },
  --     {permute := cyclePieces [4,7,6,5], orient := Orient 12 2 [(4, 1), (5, 1), (6, 1), (7, 1)]}
  --   ⟩

  #eval U^4 = Solved
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


  -- 举例：
  -- #eval 1*R
  --   ({ permute := ![0, 2, 6, 3, 4, 1, 5, 7], orient := ![0, 2, 1, 0, 0, 1, 2, 0] },
  --  { permute := ![0, 6, 2, 3, 4, 1, 9, 7, 8, 5, 10, 11], orient := ![0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0] })
  -- permute := [0, 1=>2, 2=>6, 3, 4, 5=>1, 6=>5, 7]意思是一个变化过程，那变化结果是什么呢？
  -- 1=>2 表示“索引位置1”去了“索引位置2”。
  -- orient := [0, 1=>2, 2=>1, 0, 0, 5=>1, 6=>2, 0] 则是这个变化过程的前提下才有意义的。
    -- 这里1=>2意思是：“索引位置1”去了“索引位置2”后，“索引位置2”的本地观察的方向数+2了。
  -- 方向数是指：逆时针“标记点”旋转了多少次。
  --
  -- 所以目前要酸楚某个角块的"索引位置j"的方向数目前是多少，
  -- 首先分析：还原状态操作了一个Action， 结果就是当前状态：1*Action
  -- 问题：当前状态的"索引位置j"从原来哪个索引位置来的呢？
    -- 答：可以由Action.1.permute知道每个索引位置分别到了哪一个新位置。比如：1=>2
    -- 如果用Action.1.permute的逆映射，比如：1=>2，反过来就是2=>1
    -- 比如：如果j=2, 则通过(Action.1.permute j)就得到了从“索引位置1”来的。
  -- 问题：当前状态的"索引位置j"方向数是多少？
    -- 答：由Action.1.orient的定义，Action.1.orient记录了每一个索引位置到新的索引位置后，
    -- 方向数的增加量。比如：“索引位置1”增加的量就是+2。
    -- 而我们都知道原始位置全部方向数都是0，当前状态的"索引位置j"方向数就是0+2=2

  def Corner_Absolute_Orient
  : CornerType → Fin 8 → Fin 3
  := fun x p => x.orient (x.permute.invFun p)

  def Edge_Absolute_Orient
  : EdgeType → Fin 12 → Fin 2
  := fun x p => x.orient (x.permute.invFun p)

  -- #eval Corner_Absolute_Orient U.1
  -- #eval Edge_Absolute_Orient U.2
  -- #eval Corner_Absolute_Orient F.1

  /-- 定义了哪些是属于G中6个操作的，{UDFBLR} -/
  inductive FaceTurn
  : RubiksSuperType → Prop where
    | U : FaceTurn U -- 就是说，U是其中搞一个操作。
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

  -- inductive FaceTurn_TWGroup1
  -- : RubiksSuperType → Prop where
  --   | U : FaceTurn_TWGroup1 U
  --   | D : FaceTurn_TWGroup1 D
  --   | R2 : FaceTurn_TWGroup1 R2
  --   | L2 : FaceTurn_TWGroup1 L2
  --   | F : FaceTurn_TWGroup1 F
  --   | B : FaceTurn_TWGroup1 B

  -- inductive FaceTurn_TWGroup2
  -- : RubiksSuperType → Prop where
  --   | U : FaceTurn_TWGroup2 U
  --   | D : FaceTurn_TWGroup2 D
  --   | R2 : FaceTurn_TWGroup2 R2
  --   | L2 : FaceTurn_TWGroup2 L2
  --   | F2 : FaceTurn_TWGroup2 F2
  --   | B2 : FaceTurn_TWGroup2 B2

  -- inductive FaceTurn_TWGroup3
  -- : RubiksSuperType → Prop where
  --   | U2 : FaceTurn_TWGroup3 U2
  --   | D2 : FaceTurn_TWGroup3 D2
  --   | R2 : FaceTurn_TWGroup3 R2
  --   | L2 : FaceTurn_TWGroup3 L2
  --   | F2 : FaceTurn_TWGroup3 F2
  --   | B2 : FaceTurn_TWGroup3 B2

  -- #check FaceTurn_TWGroup1.L2 -- Prop

  /-- 使用#eval的时候要怎么打印出来 -/
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
      else if c = U2 then "U, U"
      else if c = D2 then "D, D"
      else if c = R2 then "R, R"
      else if c = L2 then "L, L"
      else if c = F2 then "F, F"
      else if c = B2 then "B, B"
      else if c = U' then "U'"
      else if c = D' then "D'"
      else if c = R' then "R'"
      else if c = L' then "L'"
      else if c = F' then "F'"
      else if c = B' then "B'"
      else s!"{repr c}" -- 如果都不匹配的话，直接打印出permute，orient的结构体。repr的作用。

  -- def aRubikSuperType : RubiksSuperType :=
  --   ⟨
  --     {permute := cyclePieces [0, 1, 2, 3], orient := 0},
  --     {permute := cyclePieces [0, 1, 2, 3], orient := 0}
  --   ⟩
  -- --举例使用：它会把这个RubiksSuperType类型的东西对比来得到字符串。
  -- #eval aRubikSuperType -- 直接打印
  -- #eval toString aRubikSuperType -- 字符串打印


end FACE_TURNS

-- 这个*是在哪里定义的呢？
-- 因为RubiksSuperType是笛卡尔积CornerType × EdgeType，其乘法就是两个分量分别乘积
-- 这里*实际上是两个分量的ps_mul,要从左往右→运算。


def TPerm : RubiksSuperType
  := R * U * R' * U' * R' * F * R2 * U' * R' * U' * R * U * R' * F'
def AlteredYPerm : RubiksSuperType
  := R * U' * R' * U' * R * U * R' * F' * R * U * R' * U' * R' * F * R
def MyTestActions : RubiksSuperType
  := R *U'* R* U* R* U* R* U'* R'* U'* R* R

-- 以下两个定义，形容两个不可能的魔方状态：只旋转一次角块，还有只旋转一次棱块。
-- 后文将会证明这两种状态不存在。

def CornerTwist : RubiksSuperType
  := (
      {permute := 1, orient := (fun | 0 => 1 | _ => 0) },
      -- 这种是归纳定义的向量写法，只有0位置为1，“_”意思是其余的，其余为0。
      {permute := 1, orient := 0}
     )
def EdgeFlip : RubiksSuperType
  := (
      {permute := 1, orient := 0},
      {permute := 1, orient := (fun | 0 => 1 | _ => 0)}
     )



section RubiksGroup

  -- 魔方第二基本定理直接就定义了～～～两个定义需要互推。
  /-- 关于魔方状态集合的非直觉定义。-/
  def ValidCube :
  Set RubiksSuperType
  :=
  -- 这样的一个集合：其中的任意元素c，c满足后面这些条件。
  {
    c |
      Perm.sign c.fst.permute = Perm.sign c.snd.permute
      -- c.fst指的是角块 , c.snd指的是棱块。1，2也行。
      ∧
      Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) c.fst.orient = 0
      ∧
      Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) c.snd.orient = 0
  }

    -- 用于mul_mem'，inv_mem'的证明
    /-- 证明8个分量如果求和为0（模3），随意排列组合后，求和还是为0（模3）。 -/
    @[simp]
    lemma mul_mem'_permuteRemainsSum_2
    (apermute : Perm (Fin 8))
    (borient : (Fin 8) → Fin 3)
    (h2: Finset.sum {0, 1, 2,3,4,5,6,7} borient = 0)
    : (Finset.sum {0, 1, 2,3,4,5,6,7} fun x ↦ borient (apermute x)) = 0
    := by
      have h1:= Equiv.sum_comp apermute borient -- 常见错误：因为没有输入足够的参数 typeclass instance problem is stuck, it is often due to metavariables
      have sumEq2 : ∑ i : Fin 8, borient (apermute i)
        = ∑ x in {0, 1, 2,3,4,5,6,7}, borient (apermute x) := rfl
      rw [← sumEq2]
      clear sumEq2
      rw [h1]
      clear h1
      exact h2
      done

    -- 用于mul_mem'的证明
    /-- 证明12个分量如果求和为0（模2），随意排列组合后，求和还是为0（模2）。 -/
    @[simp]
    lemma mul_mem'_permuteRemainsSum
    (apermute : Perm (Fin 12))
    (borient : (Fin 12) → Fin 2)
    (h2: Finset.sum {0, 1, 2,3,4,5,6,7,8,9,10,11} borient = 0)
    : (Finset.sum {0, 1, 2,3,4,5,6,7,8,9,10,11} fun x ↦ borient (apermute x)) = 0
    := by
      have h1:= Equiv.sum_comp apermute borient -- 常见错误：因为没有输入足够的参数 typeclass instance problem is stuck, it is often due to metavariables
      have sumEq2 : ∑ i : Fin 12, borient (apermute i)
        = ∑ x in {0, 1, 2,3,4,5,6,7,8,9,10,11}, borient (apermute x) := rfl
      rw [← sumEq2]
      clear sumEq2
      rw [h1]
      clear h1
      exact h2
      done


  -- -- sign映射是同态的，简单举例：
  -- def permtest1: Perm (Fin 8) := (swap 0 1)
  -- def permtest2: Perm (Fin 8) := (swap 2 3)
  -- #eval sign permtest1 -- -1
  -- #eval sign permtest2 -- -1
  -- #eval (sign permtest1) * (sign permtest2) -- 1
  -- #eval sign (permtest1 * permtest2) -- 1



  /-- 因为是从这个定义ValidCube，构建一个RubiksSuperGroup的子群，然后再分析如何与Reachable（可操作到达）联系起来。
    所以首先证明群所需的性质之一：封闭性  -/
  @[simp]
  theorem mul_mem' {a b : RubiksSuperType}
  : a ∈ ValidCube → b ∈ ValidCube → a * b ∈ ValidCube
  := by
    intro hav hbv
    simp only [ValidCube]
    apply And.intro
    { -- 1.符号不变：
      have h1 : sign a.1.permute = sign a.2.permute
        := by apply hav.left
      have h2 : sign b.1.permute = sign b.2.permute
        := by apply hbv.left
      simp only [Prod.fst_mul]
      simp only [PieceState.mul_def]
      simp only [Prod.snd_mul]
      simp only [PieceState.mul_def]
      simp only [ps_mul]
      simp only [map_mul] -- sign映射是同态的，简单举例.
      exact Mathlib.Tactic.LinearCombination.mul_pf h2 h1
    }
    apply And.intro
    {-- 乘积的棱块方向数增加量orient各分量求和为0（mod 2）
      have h1 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} a.1.orient = 0
        := by apply hav.right.left
      have h2 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} b.1.orient = 0
        := by apply hbv.right.left
      simp only [Prod.fst_mul]
      simp only [PieceState.mul_def]
      simp only [ps_mul]
      simp only [Pi.add_apply]
      simp only [Function.comp_apply]
      simp only [Finset.sum_add_distrib]
      rw [h1]
      clear h1
      simp only [add_zero]
      apply mul_mem'_permuteRemainsSum_2
      exact h2
    }
    {-- 乘积的角块方向数增加量orient各分量求和为0（mod 3）
      have h1 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7, 8,9,10,11} a.2.orient = 0
        := by apply hav.right.right
      have h2 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7, 8,9,10,11} b.2.orient = 0
        := by apply hbv.right.right
      simp only [Prod.snd_mul]
      simp only [PieceState.mul_def]
      simp only [ps_mul]
      simp only [Pi.add_apply]
      simp only [Function.comp_apply]
      simp only [Finset.sum_add_distrib]
      rw [h1]
      clear h1
      simp only [add_zero]
      apply mul_mem'_permuteRemainsSum
      exact h2
    }

  -- #eval (1: RubiksSuperType)
--   { permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
--  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })

  /-- 因为是从这个定义ValidCube，构建一个RubiksSuperGroup的子群，然后再分析如何与Reachable（可操作到达）联系起来。
    所以首先证明群所需的性质之一：父群中的单位元也在该子群中；换句话说，子群里有单位元。  -/
  @[simp]
  lemma one_mem'
  : 1 ∈ ValidCube
  := by
    simp only [ValidCube]
    apply And.intro
    { apply Eq.refl }
    { apply And.intro
      { apply Eq.refl }
      { apply Eq.refl }
    }

  -- -- -- sign映射是同态的，简单举例：
  -- def permtest1: Perm (Fin 8) := (swap 0 1)
  -- #eval sign permtest1 -- -1
  -- #eval (sign permtest1⁻¹) -- -1
  -- #eval (sign permtest1)⁻¹ -- -1


  /-- 因为是从这个定义ValidCube，构建一个RubiksSuperGroup的子群，然后再分析如何与Reachable（可操作到达）联系起来。
    所以首先证明群所需的性质之一：父群中的逆函数生成的元素也在该子群中；换句话说，子群中每个元素都有逆元素。  -/
  @[simp]
  theorem inv_mem' {x : RubiksSuperType}
  :x ∈ ValidCube
  →
  x⁻¹ ∈ ValidCube
  := by
    intro hxv
    simp only [ValidCube]
    simp only [Set.mem_setOf_eq]
    simp only [Prod.fst_inv]
    simp only [Prod.snd_inv]
    simp only [PieceState.inv_def]
    simp only [ps_inv]
    apply And.intro
    {
      simp only [map_inv] -- 举例
      simp only [Int.units_inv_eq_self] -- 因为sign映射成整数{1,-1}, {1,-1}都满足逆是本身。
      apply hxv.left
    }
    apply And.intro
    { have h1 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} x.1.orient = 0
        := by apply hxv.right.left
      apply mul_mem'_permuteRemainsSum_2
      simp only [Pi.neg_apply]
      simp only [Finset.sum_neg_distrib]
      simp only [neg_eq_zero]
      exact h1
    }
    {
      have h1 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7, 8,9,10,11} x.2.orient = 0
        := by apply hxv.right.right
      apply mul_mem'_permuteRemainsSum
      simp only [Pi.neg_apply]
      simp only [Finset.sum_neg_distrib]
      simp only [neg_eq_zero]
      exact h1
    }


  /-- 因为是从这个定义ValidCube，构建一个RubiksSuperGroup的子群，然后再分析如何与Reachable（可操作到达）联系起来。
    所以首先证明群所需的性质都准备好了，正式定义这个群  -/
  instance RubiksGroup : Subgroup RubiksSuperType := {
    carrier := ValidCube -- 提供一个RubiksSuperType群的子集合ValidCube。
    mul_mem' := mul_mem' -- 封闭性质
    one_mem' := one_mem' -- 单位1元素
    inv_mem' := inv_mem' -- 沿用父群的逆函数定义，需要证明这样定义产生的逆元素也在提供的子集合ValidCube中。
    -- 结合律的性质，父群已经证明。
    -- 左乘单位元=本身的性质，已经证明
    -- 右乘单位元=本身，已经证明
    -- 左乘逆函数产生的逆元=单位元，已经证明
    -- 右乘逆函数产生的逆元=单位元，已经证明
  }


  /-- 这个就是直觉的魔方状态集合定义。后面将用一个定理证明这两个定义的集合是等价的。
  我后面可能会简称“可达”。 -/
  /- Defining the intuitively valid set of Rubik's cube positions. -/
  inductive Reachable
  : RubiksSuperType → Prop
  where
    | Solved : Reachable Solved -- 已还原状态"是Reachable的"
    -- 下面是3种方法，从定义上构造“xx是Reachable的”：
    | FT : ∀x : RubiksSuperType, FaceTurn x → Reachable x
    | mul : ∀x y : RubiksSuperType, Reachable x → Reachable y → Reachable (x * y)
    | inv :  ∀x : RubiksSuperType, Reachable x → Reachable x⁻¹

  /-- 从以上的4种基础定义，可以推出第5种基础定义：xy可达，y可达，那么x也可达。 -/
  def Reachable.split_fst: ∀x y : RubiksSuperType, Reachable (x * y) → Reachable y → Reachable x
  := by
    intro x y Rxy Ry
    have h1 := Reachable.inv (x * y) Rxy
    simp at h1 -- Reachable (y⁻¹ * x⁻¹) -- 想知道simp做了什么，可以用print，或者另开一个have。
      -- 这里简单举例说明：
      -- (x*y)⁻¹  = (y⁻¹ * x⁻¹) -- 这里应该是因为：左右同乘一个(x*y)来的
      -- 1 = 1 -- 是因为满足结合律，还有左逆，所以有这个推理。
    have h3 := Reachable.mul (y) (y⁻¹ * x⁻¹) Ry h1
    simp at h3
    have h4 := Reachable.inv (x⁻¹) h3
    simp at h4
    exact h4


  /-- 第6种基础定义: 同样xy可达，x可达，那么y也可达。-/
  def Reachable.split_snd: ∀x y : RubiksSuperType, Reachable (x * y) → Reachable x → Reachable y
  := by
    intro x y Rxy Rx
    have h1 := Reachable.inv (x * y) Rxy
    simp at h1 -- Reachable (y⁻¹ * x⁻¹)
    have h3 := Reachable.mul (y⁻¹ * x⁻¹) (x) h1 Rx
    simp at h3
    have h4 := Reachable.inv (y⁻¹) h3
    simp at h4
    exact h4


  -- inductive Reachable_TWGroup1
  -- : RubiksSuperType → Prop
  -- where
  --   | Solved : Reachable_TWGroup1 Solved
  --   | FT : ∀x : RubiksSuperType, FaceTurn_TWGroup1 x → Reachable_TWGroup1 x
  --   | mul : ∀x y : RubiksSuperType, Reachable_TWGroup1 x → Reachable_TWGroup1 y → Reachable_TWGroup1 (x * y)

  -- inductive Reachable_TWGroup2
  -- : RubiksSuperType → Prop
  -- where
  --   | Solved : Reachable_TWGroup2 Solved
  --   | FT : ∀x : RubiksSuperType, FaceTurn_TWGroup2 x → Reachable_TWGroup2 x
  --   | mul : ∀x y : RubiksSuperType, Reachable_TWGroup2 x → Reachable_TWGroup2 y → Reachable_TWGroup2 (x * y)

  -- inductive Reachable_TWGroup3
  -- : RubiksSuperType → Prop
  -- where
  --   | Solved : Reachable_TWGroup3 Solved
  --   | FT : ∀x : RubiksSuperType, FaceTurn_TWGroup3 x → Reachable_TWGroup3 x
  --   | mul : ∀x y : RubiksSuperType, Reachable_TWGroup3 x → Reachable_TWGroup3 y → Reachable_TWGroup3 (x * y)

end RubiksGroup


/- The widget below was adapted from kendfrey's repository. -/
-- section WIDGET

  -- inductive Color
  -- : Type
  -- | white | green | red | blue | orange | yellow

  -- instance : ToString Color where
  --   toString :=
  --     fun c => match c with
  --       | Color.white => "#ffffff"
  --       | Color.green => "#00ff00"
  --       | Color.red => "#ff0000"
  --       | Color.blue => "#0000ff"
  --       | Color.orange => "#ff7f00"
  --       | Color.yellow => "#ffff00"


  -- /-- 为每一个List类型定义了一个成员变量，只需要.vec就可以调用出来。 将 List 变成Vector-/
  -- def List.vec {α : Type}
  -- : Π a : List α, Vector α (a.length)
  --   | [] => Vector.nil
  --   | (x :: xs) => Vector.cons x (xs.vec)

  -- -- #check List.vec {1,2,3,4,5}



  -- def corner_map
  -- : Vector (Vector Color 3) 8
  -- :=
  -- [
  --   [Color.white, Color.orange, Color.blue].vec,
  --   [Color.white, Color.blue, Color.red].vec,
  --   [Color.white, Color.red, Color.green].vec,
  --   [Color.white, Color.green, Color.orange].vec,
  --   [Color.yellow, Color.orange, Color.green].vec,
  --   [Color.yellow, Color.green, Color.red].vec,
  --   [Color.yellow, Color.red, Color.blue].vec,
  --   [Color.yellow, Color.blue, Color.orange].vec
  -- ].vec


  -- def edge_map : Vector (Vector Color 2) 12 :=
  -- [
  --   [Color.white, Color.blue].vec,
  --   [Color.white, Color.red].vec,
  --   [Color.white, Color.green].vec,
  --   [Color.white, Color.orange].vec,
  --   [Color.yellow, Color.green].vec,
  --   [Color.yellow, Color.red].vec,
  --   [Color.yellow, Color.blue].vec,
  --   [Color.yellow, Color.orange].vec,
  --   [Color.blue, Color.orange].vec,
  --   [Color.blue, Color.red].vec,
  --   [Color.green, Color.red].vec,
  --   [Color.green, Color.orange].vec
  -- ].vec

  -- def corner_sticker
  -- : Fin 8 → Fin 3 → RubiksSuperType → Color
  -- :=
  --   fun i o cube =>
  --   (corner_map.get (cube.1.permute⁻¹ i)).get (Fin.sub o (cube.1.orient i))

  -- def edge_sticker
  -- : Fin 12 → Fin 2 → RubiksSuperType → Color
  -- :=
  --   fun i o cube => (edge_map.get (cube.2.permute⁻¹ i)).get (Fin.sub o (cube.2.orient i))


  -- open Lean Widget

  -- def L8x3
  -- : List (ℕ × ℕ)
  -- :=
  -- (List.map (fun x => (x, 0)) (List.range 8))
  -- ++
  -- (List.map (fun x => (x, 1)) (List.range 8))
  -- ++
  -- (List.map (fun x => (x, 2)) (List.range 8))
  -- def L12x2
  -- : List (ℕ × ℕ)
  -- :=
  -- (List.map (fun x => (x, 0)) (List.range 12))
  -- ++
  -- (List.map (fun x => (x, 1)) (List.range 12))


  -- def cubeStickerJson
  -- : RubiksSuperType → Json
  -- :=
  --   fun cube => Json.mkObj --???
  --   (
  --     (List.map
  --       (fun p => (s!"c_{p.fst}_{p.snd}", Json.str (toString (corner_sticker p.fst p.snd $ cube))))
  --       L8x3
  --     )
  --     ++
  --     (List.map
  --       (fun p => (s!"e_{p.fst}_{p.snd}", Json.str (toString (edge_sticker p.fst p.snd $ cube))))
  --       L12x2
  --     )
  --   )

/- Useful predicates for the SolutionAlgorithm, as well as for some minor proofs. -/
-- section SolutionState

  def CornersSolved :
  RubiksSuperType → Prop
  :=
    fun c =>
      -- 定义需要满足：
      c.fst.permute = 1
      ∧
      c.fst.orient = 0

  def EdgesSolved
  : RubiksSuperType → Prop
  :=
    fun c =>
      -- 定义需要满足：
      c.snd.permute = 1
      ∧
      c.snd.orient = 0

  def IsSolved
  : RubiksSuperType → Prop
  :=
    fun c =>
      -- 定义需要满足：
      CornersSolved c
      ∧
      EdgesSolved c

--   instance {c} : Decidable (CornersSolved c) := by apply And.decidable
--   instance {c} : Decidable (EdgesSolved c) := by apply And.decidable
--   instance {c} : Decidable (IsSolved c) := by apply And.decidable


-- end SolutionState
