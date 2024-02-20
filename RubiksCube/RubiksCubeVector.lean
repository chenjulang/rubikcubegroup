-- import Lean
-- import Mathlib.GroupTheory.Perm.Basic
-- import Mathlib.GroupTheory.Perm.Fin

-- open Equiv Perm

-- -- Vector α n ：α是类型，n是个数。

-- section RubiksSuperGroup

--   -- 这两个instance和下面的deriving Repr有关
--   instance (n : Nat) : Repr (Perm (Fin n)) :=
--     ⟨reprPrec ∘ Equiv.toFun⟩

--   instance (n m : Nat) : Repr (Vector (Fin n) m) :=
--     ⟨reprPrec ∘ Vector.toList⟩

--   /-- 用排列的逆操作重新排列一个向量-/
--   def permuteVector {α : Type} {n : ℕ}
--   : Perm (Fin n) → Vector α n → Vector α n
--   :=
--     fun p v => {
--     -- 举例:
--       -- p:一个重排列(1=>2,2=>3,3=>1,4=>4,5=>5,6=>6,7=>7,8=>8)
--       -- v:一个向量(a1,a2,a3,a4,a5,a6,a7,a8)
--       -- 给出列表
--       val := by
--         exact (Vector.ofFn (fun i => v.get (p.invFun i))).toList
--         -- 举例：
--           -- Vector.ofFn (fun i => v.get (p.invFun i)) 就是 ：(a1,a2,a3,a4,a5,a6,a7,a8).get (3,1,2,4,5,6,7,8)
--                 -- 也就是 (a3,a1,a2,a4,a5,a6,a7,a8)
--           -- (Vector.ofFn (fun i => v.get (p.invFun i))).toList 就是 [a3,a1,a2,a4,a5,a6,a7,a8]
--       -- 检查长度
--       property := by simp only [invFun_as_coe, Vector.toList_ofFn, List.length_ofFn]
--         -- simp
--     }

--   /-- 魔方全体块的某一个状态,感觉是分开角块和棱块两种 PieceState。
--   可以这样理解，一个PieceState结构，就是某一个群H中的角块或棱块状态。
--   首先permute描述了块的位置，orient描述了各位置上的方向数（逆时针转一次算+1）。-/
--   structure PieceState (pieces orientations: ℕ+) where
--     --代表全体方块的位置：
--     permute : Perm (Fin pieces) -- 比如这里pieces取8
--     --代表全体方块的方向：
--     orient : Vector (Fin orientations) pieces -- 比如这里orientations取3
--     deriving Repr
--     --比如上面这样取的话，就是全体角块的位置状态+方向数状态的总和。

--   --魔方状态的复合函数：
--   -- 这个定义很重要，其实是可以按需定义的，
--   /-- 程序中的复合ab，是这样理解的：先作用b，再作用a。
--   而我们手写证明中复合ab,是这样理解的：先作用a，再作用b。-/
--   def ps_mul {p o : ℕ+}
--   : PieceState p o → PieceState p o → PieceState p o
--   :=
--     fun a2 a1 => {
--     --举例：a是F,b是R
--       -- a: {
--       --  permute: Perm (Fin 8) := (1=>2,2=>6,3,4,5=>1,6=>5,7,8) -- 有8项
--       --  orient : Vector (Fin 3) 8 := (1,2,0,0,2,1,0,0) -- 有8项
--       --}
--       -- b: {
--       --  permute: Perm (Fin 8) := (1,2=>3,3=>7,4,5,6=>2,7=>6,8) -- 有8项
--       --  orient : Vector (Fin 3) 8 := (0,1,2,0,0,2,1,0) -- 有8项
--       --}
--       permute := a1.permute * a2.permute -- 这里 “*” 应该是指排列之间的复合运算
--       orient := Vector.map₂ Fin.add (permuteVector a1.permute a2.orient) a1.orient
--         --1.分析类型：
--           --Vector.map₂ ： (f : α → β → φ) : Vector α n → Vector β n → Vector φ n
--           --
--           --Fin.add:                              Fin n → Fin n → Fin n  --应该是一个求和模n的计算函数
--           --(permuteVector b.permute a.orient) :  Vector (Fin ↑o) ↑p
--           -- b.orient:                            Vector (Fin ↑orientations) ↑pieces
--           --
--         --2.举例：
--           -- 所以
--           -- (permuteVector b.permute a.orient) = (permuteVector (1,2=>3,3=>7,4,5,6=>2,7=>6,8) (1,2,0,0,2,1,0,0) )
--               -- = (1,1,2,0,2,0,0,0) -- 8项
--           --  b.orient = (0,1,2,0,0,2,1,0)
--           -- 所以 orient := Vector.map₂ Fin.add (permuteVector b.permute a.orient) b.orient = 应该就是2个向量加起来每个分量mod 3的结果
--               -- = (1,1,2,0,2,0,0,0) + (0,1,2,0,0,2,1,0) 【mod 3】
--               -- = (1,2,1,0,2,2,1,0)
--         --3.对比一下手写的证明：v(gh) := v(g) + ρ(g)^(-1)·v(h)
--               -- v(RF) = v(R) + ρ(R)^(-1)·v(F) = (0,1,2,0,0,2,1,0) +  (1,2=>3,3=>7,4,5,6=>2,7=>6,8)^(-1)·(1,2,0,0,2,1,0,0)
--           -- 实际上，上面程序做的是 v(ab) = ρ(b))^(-1)·v(a) + v(b) , 其实可以ps_mul理解成，
--           -- 先对魔方操作第二个参数b的操作，然后再操作第一个参数a的操作，得到的最终效果。
--           -- 因此程序中的复合ab，是这样理解的：先作用b，再作用a。
--           -- 而我们手写证明中复合ab,是这样理解的：先作用a，再作用b。
--           --实际上只是定义不一样，得到的相对结论是一样的。
--     }

--   lemma ps_mul_assoc {p o : ℕ+}
--   : ∀ (a b c : PieceState p o),
--   ps_mul (ps_mul c b) a = ps_mul c (ps_mul b a)
--   --举例：a是F,b是R，c是B
--   -- a: {
--   --  permute: Perm (Fin 8) := (1=>2,2=>6,3,4,5=>1,6=>5,7,8) -- 有8项
--   --  orient : Vector (Fin 3) 8 := (2,1,0,0,1,2,0,0) -- 有8项
--   --}
--   -- b: {
--   --  permute: Perm (Fin 8) := (1,2=>3,3=>7,4,5,6=>2,7=>6,8) -- 有8项
--   --  orient : Vector (Fin 3) 8 := (0,2,1,0,0,1,2,0) -- 有8项
--   --}
--   -- c: {
--   --  permute: Perm (Fin 8) := (1,2,3=>4,4=>8,5,6,7=>3,8=>7) -- 有8项
--   --  orient : Vector (Fin 3) 8 := (0,0,2,1,0,0,1,2) -- 有8项
--   --}
--   -- 读法是从右开始看：ba是先作用a，再作用b
--   --引理实际说的是：(ba)c = a(cb) -- 也就是1·F·R·B = 1·F·R·B
--   := by
--     intro a b c
--     simp [ps_mul]
--     apply And.intro
--     {
--       --???todo
--       simp only [Perm.mul_def]
--       simp only [Equiv.trans_assoc]
--     }
--     {
--       --手写的证明应该是：a(bc) = (ab)c
--       --bc:{
--       --  permute: (1,2=>3,3=>7,4,5,6=>2,7=>6,8) * (1,2,3=>4,4=>8,5,6,7=>3,8=>7)
--       --          = (1,2=>4,3,4=>8,5,6=>2,7=>6,8=>7)
--       --  orient : (1,2=>3,3=>7,4,5,6=>2,7=>6,8)^(-1)·(0,0,2,1,0,0,1,2)
--       --           + (0,2,1,0,0,1,2,0)
--       --          = (0,2,1,1,0,0,0,2) +
--       --            (0,2,1,0,0,1,2,0)
--       --          = (0,1,2,1,0,1,2,2) （mod 3）
--       -- }
--       --ab:{
--       --  permute: (1=>2,2=>6,3,4,5=>1,6=>5,7,8) * (1,2=>3,3=>7,4,5,6=>2,7=>6,8)
--       --          = (1=>3,2,3=>7,4,5=>1,6=>5,7=>6,8)
--       --  orient : (1=>2,2=>6,3,4,5=>1,6=>5,7,8)^(-1)·(0,2,1,0,0,1,2,0)
--       --          + (2,1,0,0,1,2,0,0)
--       --          = (2,1,1,0,0,0,2,0) +
--       --            (2,1,0,0,1,2,0,0)
--       --          = (1,2,1,0,1,2,2,0) (mod 3)
--       -- }
--       --a(bc):{
--       --  permute: (1=>2,2=>6,3,4,5=>1,6=>5,7,8) * (1,2=>4,3,4=>8,5,6=>2,7=>6,8=>7)
--       --          = (1=>4,2,3,4=>8,5=>1,6=>5,7=>6,8=>7)
--       --  orient : (1=>2,2=>6,3,4,5=>1,6=>5,7,8)^(-1)·(0,1,2,1,0,1,2,2) +
--       --            (2,1,0,0,1,2,0,0)
--       --          = (1,1,2,1,0,0,2,2) +
--       --            (2,1,0,0,1,2,0,0)
--       --          = (0,2,2,1,1,2,2,2) (mod 3)
--       -- }
--       --(ab)c:{
--       --  permute: (1=>3,2,3=>7,4,5=>1,6=>5,7=>6,8) * (1,2,3=>4,4=>8,5,6,7=>3,8=>7)
--       --          = (1=>4,2,3,4=>8,5=>1,6=>5,7=>6,8=>7)
--       --  orient : (1=>3,2,3=>7,4,5=>1,6=>5,7=>6,8)^(-1)·(0,0,2,1,0,0,1,2) +
--       --            (1,2,1,0,1,2,2,0)
--       --          = (2,0,1,1,0,0,0,2) +
--       --            (1,2,1,0,1,2,2,0)
--       --          = (0,2,2,1,1,2,2,2)
--       -- }
--       -- we can see a(bc) is equal to (ab)c



--       -- a: {
--       --  permute: Perm (Fin 8) := (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)
--       --  orient : Vector (Fin 3) 8 := (b1,b2,b3,b4,b5,b6,b7,b8)
--       --}
--       -- b: {
--       --  permute: Perm (Fin 8) := (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)
--       --  orient : Vector (Fin 3) 8 := (d1,d2,d3,d4,d5,d6,d7,d8)
--       --}
--       -- c: {
--       --  permute: Perm (Fin 8) := (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)
--       --  orient : Vector (Fin 3) 8 := (f1,f2,f3,f4,f5,f6,f7,f8)
--       --}
--       --bc:{
--       --  permute: (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8) * (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)
--       --        = (a1=>e1,a2=>e2,a3=>e3,a4=>e4,a5=>e5,a6=>e6,a7=>e7,a8=>e8)
--       --  orient : (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)^(-1)·(f1,f2,f3,f4,f5,f6,f7,f8)
--       --            + (d1,d2,d3,d4,d5,d6,d7,d8) (mod 3)
--       -- }
--       --ab:{
--       --  permute: (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1) * (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)
--       --        = (1=>c1,2=>c1,3=>c1,4=>c1,5=>c1,6=>c1,7=>c1,8=>c1)
--       --  orient : (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
--       --            + (b1,b2,b3,b4,b5,b6,b7,b8) (mod 3)
--       -- }
--       --todo--
--       --a(bc):{
--       --  permute: (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)
--       --    * (a1=>e1,a2=>e2,a3=>e3,a4=>e4,a5=>e5,a6=>e6,a7=>e7,a8=>e8)
--       --    = (1=>e1,2=>e1,3=>e1,4=>e1,5=>e1,6=>e1,7=>e1,8=>e1)
--       --  orient : (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·
--       --    ((a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)^(-1)·(f1,f2,f3,f4,f5,f6,f7,f8) + (d1,d2,d3,d4,d5,d6,d7,d8))
--       --     + (b1,b2,b3,b4,b5,b6,b7,b8) (mod 3)
--       --  = (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·((a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)^(-1)·(f1,f2,f3,f4,f5,f6,f7,f8))
--       --  + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
--       --  + (b1,b2,b3,b4,b5,b6,b7,b8)
--       --  = (a1=>1,a1=>2,a1=>3,a1=>4,a1=>5,a1=>6,a1=>7,a1=>8)·((c1=>a1,c2=>a2,c3=>a3,c4=>a4,c5=>a5,c6=>a6,c7=>a7,c8=>a8)·(f1,f2,f3,f4,f5,f6,f7,f8))
--       --  + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
--       --  + (b1,b2,b3,b4,b5,b6,b7,b8)
--       --  = (c1=>1,c1=>2,c1=>3,c1=>4,c1=>5,c1=>6,c1=>7,c1=>8)·(f1,f2,f3,f4,f5,f6,f7,f8))
--       --  + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
--       --  + (b1,b2,b3,b4,b5,b6,b7,b8)
--       -- }
--       --(ab)c:{
--       --  permute: (1=>c1,2=>c1,3=>c1,4=>c1,5=>c1,6=>c1,7=>c1,8=>c1)
--       --         * (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)
--       --          = (1=>e1,2=>e1,3=>e1,4=>e1,5=>e1,6=>e1,7=>e1,8=>e1)
--       --  orient : (1=>c1,2=>c1,3=>c1,4=>c1,5=>c1,6=>c1,7=>c1,8=>c1)^(-1)·
--       --           (f1,f2,f3,f4,f5,f6,f7,f8)
--       --          + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
--       --            + (b1,b2,b3,b4,b5,b6,b7,b8) (mod 3)
--       --  = (1=>c1,2=>c1,3=>c1,4=>c1,5=>c1,6=>c1,7=>c1,8=>c1)^(-1)·(f1,f2,f3,f4,f5,f6,f7,f8)
--       --  + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
--       --  + (b1,b2,b3,b4,b5,b6,b7,b8)
--       --  = (c1=>1,c1=>2,c1=>3,c1=>4,c1=>5,c1=>6,c1=>7,c1=>8)·(f1,f2,f3,f4,f5,f6,f7,f8)
--       --  + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
--       --  + (b1,b2,b3,b4,b5,b6,b7,b8)
--       -- }

--       simp only [permuteVector]
--       -- simp only [invFun_as_coe, Vector.toList_ofFn, Vector.get_map₂]
--       -- obtain ⟨a_p, a_o⟩ := a
--       -- obtain ⟨a_o_List, a_o_lengthPro⟩ := a_o
--       -- obtain ⟨a1⟩ := a_o_List ???

--       --



--       --todo--
--       sorry

--     }

--   -- #check Vector.map₂

--   lemma ps_one_mul {p o : ℕ+} : ∀ (a : PieceState p o), ps_mul {permute := 1, orient := Vector.replicate p 0} a = a := by
--     intro a
--     simp [ps_mul, permuteVector]
--     cases a with
--     | mk a.permute a.orient =>
--       simp
--       sorry

--   lemma ps_mul_one {p o : ℕ+} : ∀ (a : PieceState p o), ps_mul a {permute := 1, orient := Vector.replicate p 0} = a := by
--     intro a
--     simp [ps_mul, permuteVector]
--     cases a with
--     | mk a.permute a.orient =>
--       simp
--       sorry

--   def ps_inv {p o : ℕ+} : PieceState p o → PieceState p o :=
--     fun ps =>
--     { permute := ps.permute⁻¹
--       orient := permuteVector ps.permute⁻¹ (Vector.map (fun x => -x) ps.orient) }

--   lemma ps_mul_left_inv {p o : ℕ+} : ∀ (a : PieceState p o), ps_mul (ps_inv a) a = {permute := 1, orient := Vector.replicate p 0} := by
--     intro a
--     simp [ps_inv, ps_mul, permuteVector]
--     sorry

--   instance PieceGroup (pieces orientations: ℕ+) :
--   Group (PieceState pieces orientations) := {
--     mul := ps_mul
--     mul_assoc := sorry
--     --  ps_mul_assoc
--     one := {permute := 1, orient := Vector.replicate pieces 0}
--     one_mul := ps_one_mul
--     mul_one := ps_mul_one
--     inv := ps_inv
--     mul_left_inv := ps_mul_left_inv
--   }

--   lemma PieceState.mul_def {p o : ℕ+} (a b : PieceState p o) : a * b = ps_mul a b := by rfl

--   lemma PieceState.inv_def {p o : ℕ+} (a b : PieceState p o) : a⁻¹ = ps_inv a := by rfl

--   abbrev CornerType := PieceState 8 3
--   abbrev EdgeType := PieceState 12 2

--   instance Rubiks2x2Group : Group CornerType := PieceGroup 8 3

--   abbrev RubiksSuperType := CornerType × EdgeType
--   instance RubiksSuperGroup : Group RubiksSuperType := Prod.instGroup

-- end RubiksSuperGroup

-- --//---

-- def zeroOrient (p o : ℕ+) : Vector (Fin o) p  := Vector.replicate p 0

-- def orientVector (p o : ℕ+) : List ((Fin p) × (Fin o)) → Vector (Fin o) p
--   | [] => zeroOrient p o
--   | (i, x) :: os => (orientVector p o os).set i x

-- --//---

-- section FACE_TURNS

--   def cycleImpl {α : Type*} [DecidableEq α] : α → List α → Perm α
--     | _, [] => 1
--     | a, (x :: xs) => swap a x * cycleImpl x xs

--   def cyclePieces {α : Type*} [DecidableEq α] : List α → Perm α
--     | [] => 1
--     | (x :: xs) => cycleImpl x xs

--   def U : RubiksSuperType :=
--     ⟨{permute := cyclePieces [0, 1, 2, 3], orient := zeroOrient 8 3},
--     {permute := cyclePieces [0, 1, 2, 3], orient := zeroOrient 12 2}⟩
--   def D : RubiksSuperType :=
--     ⟨{permute := cyclePieces [4, 5, 6, 7], orient := zeroOrient 8 3},
--     {permute := cyclePieces [4, 5, 6, 7], orient := zeroOrient 12 2}⟩
--   def R : RubiksSuperType :=
--     ⟨{permute := cyclePieces [1, 6, 5, 2], orient := orientVector 8 3 [(1, 1), (6, 2), (5, 1), (2, 2)]},
--     {permute := cyclePieces [1, 9, 5, 10], orient := zeroOrient 12 2}⟩
--   def L : RubiksSuperType :=
--     ⟨{permute := cyclePieces [0, 3, 4, 7], orient := orientVector 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)]},
--     {permute := cyclePieces [3, 11, 7, 8], orient := zeroOrient 12 2}⟩
--   def F : RubiksSuperType :=
--     ⟨{permute := cyclePieces [2, 5, 4, 3], orient := orientVector 8 3 [(2, 1), (5, 2), (4, 1), (3, 2)]},
--     {permute := cyclePieces [2, 10, 4, 11], orient := orientVector 12 2 [(2, 1), (10, 1), (4, 1), (11, 1)]}⟩
--   def B : RubiksSuperType :=
--     ⟨{permute := cyclePieces [0, 7, 6, 1], orient := orientVector 8 3 [(0, 1), (7, 2), (6, 1), (1, 2)]},
--     {permute := cyclePieces [0, 8, 6, 9], orient := orientVector 12 2 [(0, 1), (8, 1), (6, 1), (9, 1)]}⟩
--   def U2 := U^2
--   def D2 := D^2
--   def R2 := R^2
--   def L2 := L^2
--   def F2 := F^2
--   def B2 := B^2
--   def U' := U⁻¹
--   def D' := D⁻¹
--   def R' := R⁻¹
--   def L' := L⁻¹
--   def F' := F⁻¹
--   def B' := B⁻¹

--   inductive FaceTurn : RubiksSuperType → Prop where
--     | U : FaceTurn U
--     | D : FaceTurn D
--     | R : FaceTurn R
--     | L : FaceTurn L
--     | F : FaceTurn F
--     | B : FaceTurn B
--     | U2 : FaceTurn U2
--     | D2 : FaceTurn D2
--     | R2 : FaceTurn R2
--     | L2 : FaceTurn L2
--     | F2 : FaceTurn F2
--     | B2 : FaceTurn B2
--     | U' : FaceTurn U'
--     | D' : FaceTurn D'
--     | R' : FaceTurn R'
--     | L' : FaceTurn L'
--     | F' : FaceTurn F'
--     | B' : FaceTurn B'

-- end FACE_TURNS

-- def Solved : RubiksSuperType := 1
-- def TPerm : RubiksSuperType := R * U * R' * U' * R' * F * R2 * U' * R' * U' * R * U * R' * F'
-- def AlteredYPerm : RubiksSuperType := R * U' * R' * U' * R * U * R' * F' * R * U * R' * U' * R' * F * R

-- def CornerTwist : RubiksSuperType := ({permute := 1, orient := (zeroOrient 8 3).set 0 1}, {permute := 1, orient := zeroOrient 12 2})
-- def EdgeFlip : RubiksSuperType := ({permute := 1, orient := zeroOrient 8 3}, {permute := 1, orient := (zeroOrient 12 2).set 0 1})

-- section RubiksGroup

--   def ValidCube : Set RubiksSuperType := {c | Perm.sign c.fst.permute = Perm.sign c.snd.permute ∧ c.fst.orient.toList.sum = 0 ∧ c.snd.orient.toList.sum = 0}

--   lemma mul_mem' {a b : RubiksSuperType} : a ∈ ValidCube → b ∈ ValidCube → a * b ∈ ValidCube := by
--     intro hav hbv
--     simp [ValidCube, PieceState.mul_def, ps_mul]
--     repeat' apply And.intro
--     aesop
--     { have h1 : sign fst.permute = sign snd.permute := by apply hav.left
--       have h2 : sign fst_1.permute = sign snd_1.permute := by apply hbv.left
--       simp [h1, h2] }
--     { sorry }
--     { sorry }

--   lemma one_mem' : 1 ∈ ValidCube := by
--       simp [ValidCube]
--       apply And.intro
--       · apply Eq.refl
--       · apply And.intro
--         · apply Eq.refl
--         · apply Eq.refl

--   lemma inv_mem' {x : RubiksSuperType} : x ∈ ValidCube → x⁻¹ ∈ ValidCube := by
--     intro hxv
--     simp [ValidCube, PieceState.inv_def, ps_inv]
--     sorry

--   instance RubiksGroup : Subgroup RubiksSuperType := {
--     carrier := ValidCube
--     mul_mem' := mul_mem'
--     one_mem' := one_mem'
--     inv_mem' := inv_mem'
--   }

--   inductive Reachable : RubiksSuperType → Prop where
--     | Solved : Reachable Solved
--     | FT : ∀x : RubiksSuperType, FaceTurn x → Reachable x
--     | mul : ∀x y : RubiksSuperType, Reachable x → Reachable y → Reachable (x * y)

-- end RubiksGroup

-- section WIDGET

--   inductive Color : Type | white | green | red | blue | orange | yellow

--   instance : ToString Color where
--     toString :=
--     fun c => match c with
--       | Color.white => "#ffffff"
--       | Color.green => "#00ff00"
--       | Color.red => "#ff0000"
--       | Color.blue => "#0000ff"
--       | Color.orange => "#ff7f00"
--       | Color.yellow => "#ffff00"

--   def List.vec {α : Type} : Π a : List α, Vector α (a.length)
--     | [] => Vector.nil
--     | (x :: xs) => Vector.cons x (xs.vec)

--   def corner_map : Vector (Vector Color 3) 8 :=
--   [
--     [Color.white, Color.orange, Color.blue].vec,
--     [Color.white, Color.blue, Color.red].vec,
--     [Color.white, Color.red, Color.green].vec,
--     [Color.white, Color.green, Color.orange].vec,
--     [Color.yellow, Color.orange, Color.green].vec,
--     [Color.yellow, Color.green, Color.red].vec,
--     [Color.yellow, Color.red, Color.blue].vec,
--     [Color.yellow, Color.blue, Color.orange].vec
--   ].vec

--   def edge_map : Vector (Vector Color 2) 12 :=
--   [
--     [Color.white, Color.blue].vec,
--     [Color.white, Color.red].vec,
--     [Color.white, Color.green].vec,
--     [Color.white, Color.orange].vec,
--     [Color.yellow, Color.green].vec,
--     [Color.yellow, Color.red].vec,
--     [Color.yellow, Color.blue].vec,
--     [Color.yellow, Color.orange].vec,
--     [Color.blue, Color.orange].vec,
--     [Color.blue, Color.red].vec,
--     [Color.green, Color.red].vec,
--     [Color.green, Color.orange].vec
--   ].vec

--   def corner_sticker : Fin 8 → Fin 3 → RubiksSuperType → Color :=
--     fun i o cube => (corner_map.get (cube.1.permute⁻¹ i)).get (Fin.sub o (cube.1.orient.get i))

--   def edge_sticker : Fin 12 → Fin 2 → RubiksSuperType → Color :=
--     fun i o cube => (edge_map.get (cube.2.permute⁻¹ i)).get (Fin.sub o (cube.2.orient.get i))

--   open Lean Widget

--   def L8x3 : List (ℕ × ℕ) := (List.map (fun x => (x, 0)) (List.range 8)) ++ (List.map (fun x => (x, 1)) (List.range 8)) ++ (List.map (fun x => (x, 2)) (List.range 8))
--   def L12x2 : List (ℕ × ℕ) := (List.map (fun x => (x, 0)) (List.range 12)) ++ (List.map (fun x => (x, 1)) (List.range 12))

--   def cubeStickerJson : RubiksSuperType → Json :=
--     fun cube => Json.mkObj
--     ((List.map (fun p => (s!"c_{p.fst}_{p.snd}", Json.str (toString (corner_sticker p.fst p.snd $ cube)))) L8x3)
--     ++
--     (List.map (fun p => (s!"e_{p.fst}_{p.snd}", Json.str (toString (edge_sticker p.fst p.snd $ cube)))) L12x2))

--   @[widget] def cubeWidget : UserWidgetDefinition where
--     name := "Cube State"
--     javascript :="
--       import * as React from 'react';

--     export default function (props) {
--       return React.createElement(
--         'div',
--         {
--           style: {
--             display: 'grid',
--             gridTemplateColumns: 'repeat(12, 20px)',
--             gridTemplateRows: 'repeat(9, 20px)',
--             rowGap: '2px',
--             columnGap: '2px',
--             margin: '10px',
--           },
--         },
--         React.createElement('div', {style: {gridColumn: '4', gridRow: '1', backgroundColor: props.c_0_0}}),
--         React.createElement('div', {style: {gridColumn: '5', gridRow: '1', backgroundColor: props.e_0_0}}),
--         React.createElement('div', {style: {gridColumn: '6', gridRow: '1', backgroundColor: props.c_1_0}}),
--         React.createElement('div', {style: {gridColumn: '4', gridRow: '2', backgroundColor: props.e_3_0}}),
--         React.createElement('div', {style: {gridColumn: '5', gridRow: '2', backgroundColor: '#ffffff'}}),
--         React.createElement('div', {style: {gridColumn: '6', gridRow: '2', backgroundColor: props.e_1_0}}),
--         React.createElement('div', {style: {gridColumn: '4', gridRow: '3', backgroundColor: props.c_3_0}}),
--         React.createElement('div', {style: {gridColumn: '5', gridRow: '3', backgroundColor: props.e_2_0}}),
--         React.createElement('div', {style: {gridColumn: '6', gridRow: '3', backgroundColor: props.c_2_0}}),
--         React.createElement('div', {style: {gridColumn: '1', gridRow: '4', backgroundColor: props.c_0_1}}),
--         React.createElement('div', {style: {gridColumn: '2', gridRow: '4', backgroundColor: props.e_3_1}}),
--         React.createElement('div', {style: {gridColumn: '3', gridRow: '4', backgroundColor: props.c_3_2}}),
--         React.createElement('div', {style: {gridColumn: '1', gridRow: '5', backgroundColor: props.e_8_1}}),
--         React.createElement('div', {style: {gridColumn: '2', gridRow: '5', backgroundColor: '#ff7f00'}}),
--         React.createElement('div', {style: {gridColumn: '3', gridRow: '5', backgroundColor: props.e_11_1}}),
--         React.createElement('div', {style: {gridColumn: '1', gridRow: '6', backgroundColor: props.c_7_2}}),
--         React.createElement('div', {style: {gridColumn: '2', gridRow: '6', backgroundColor: props.e_7_1}}),
--         React.createElement('div', {style: {gridColumn: '3', gridRow: '6', backgroundColor: props.c_4_1}}),
--         React.createElement('div', {style: {gridColumn: '4', gridRow: '4', backgroundColor: props.c_3_1}}),
--         React.createElement('div', {style: {gridColumn: '5', gridRow: '4', backgroundColor: props.e_2_1}}),
--         React.createElement('div', {style: {gridColumn: '6', gridRow: '4', backgroundColor: props.c_2_2}}),
--         React.createElement('div', {style: {gridColumn: '4', gridRow: '5', backgroundColor: props.e_11_0}}),
--         React.createElement('div', {style: {gridColumn: '5', gridRow: '5', backgroundColor: '#00ff00'}}),
--         React.createElement('div', {style: {gridColumn: '6', gridRow: '5', backgroundColor: props.e_10_0}}),
--         React.createElement('div', {style: {gridColumn: '4', gridRow: '6', backgroundColor: props.c_4_2}}),
--         React.createElement('div', {style: {gridColumn: '5', gridRow: '6', backgroundColor: props.e_4_1}}),
--         React.createElement('div', {style: {gridColumn: '6', gridRow: '6', backgroundColor: props.c_5_1}}),
--         React.createElement('div', {style: {gridColumn: '7', gridRow: '4', backgroundColor: props.c_2_1}}),
--         React.createElement('div', {style: {gridColumn: '8', gridRow: '4', backgroundColor: props.e_1_1}}),
--         React.createElement('div', {style: {gridColumn: '9', gridRow: '4', backgroundColor: props.c_1_2}}),
--         React.createElement('div', {style: {gridColumn: '7', gridRow: '5', backgroundColor: props.e_10_1}}),
--         React.createElement('div', {style: {gridColumn: '8', gridRow: '5', backgroundColor: '#ff0000'}}),
--         React.createElement('div', {style: {gridColumn: '9', gridRow: '5', backgroundColor: props.e_9_1}}),
--         React.createElement('div', {style: {gridColumn: '7', gridRow: '6', backgroundColor: props.c_5_2}}),
--         React.createElement('div', {style: {gridColumn: '8', gridRow: '6', backgroundColor: props.e_5_1}}),
--         React.createElement('div', {style: {gridColumn: '9', gridRow: '6', backgroundColor: props.c_6_1}}),
--         React.createElement('div', {style: {gridColumn: '10', gridRow: '4', backgroundColor: props.c_1_1}}),
--         React.createElement('div', {style: {gridColumn: '11', gridRow: '4', backgroundColor: props.e_0_1}}),
--         React.createElement('div', {style: {gridColumn: '12', gridRow: '4', backgroundColor: props.c_0_2}}),
--         React.createElement('div', {style: {gridColumn: '10', gridRow: '5', backgroundColor: props.e_9_0}}),
--         React.createElement('div', {style: {gridColumn: '11', gridRow: '5', backgroundColor: '#0000ff'}}),
--         React.createElement('div', {style: {gridColumn: '12', gridRow: '5', backgroundColor: props.e_8_0}}),
--         React.createElement('div', {style: {gridColumn: '10', gridRow: '6', backgroundColor: props.c_6_2}}),
--         React.createElement('div', {style: {gridColumn: '11', gridRow: '6', backgroundColor: props.e_6_1}}),
--         React.createElement('div', {style: {gridColumn: '12', gridRow: '6', backgroundColor: props.c_7_1}}),
--         React.createElement('div', {style: {gridColumn: '4', gridRow: '7', backgroundColor: props.c_4_0}}),
--         React.createElement('div', {style: {gridColumn: '5', gridRow: '7', backgroundColor: props.e_4_0}}),
--         React.createElement('div', {style: {gridColumn: '6', gridRow: '7', backgroundColor: props.c_5_0}}),
--         React.createElement('div', {style: {gridColumn: '4', gridRow: '8', backgroundColor: props.e_7_0}}),
--         React.createElement('div', {style: {gridColumn: '5', gridRow: '8', backgroundColor: '#ffff00'}}),
--         React.createElement('div', {style: {gridColumn: '6', gridRow: '8', backgroundColor: props.e_5_0}}),
--         React.createElement('div', {style: {gridColumn: '4', gridRow: '9', backgroundColor: props.c_7_0}}),
--         React.createElement('div', {style: {gridColumn: '5', gridRow: '9', backgroundColor: props.e_6_0}}),
--         React.createElement('div', {style: {gridColumn: '6', gridRow: '9', backgroundColor: props.c_6_0}}),
--       );
--     }"

-- end WIDGET

-- #widget cubeWidget (cubeStickerJson Solved)
-- #widget cubeWidget (cubeStickerJson TPerm)
-- #widget cubeWidget (cubeStickerJson AlteredYPerm)
-- #widget cubeWidget (cubeStickerJson CornerTwist)
-- #widget cubeWidget (cubeStickerJson EdgeFlip)

-- section SolutionState

--   def CornersSolved : RubiksSuperType → Prop :=
--     fun c => c.fst.permute = 1 ∧ c.fst.orient = zeroOrient 8 3

--   def EdgesSolved : RubiksSuperType → Prop :=
--     fun c => c.snd.permute = 1 ∧ c.snd.orient = zeroOrient 12 2

--   def IsSolved : RubiksSuperType → Prop := fun c => CornersSolved c ∧ EdgesSolved c

--   instance {c} : Decidable (CornersSolved c) := by apply And.decidable
--   instance {c} : Decidable (EdgesSolved c) := by apply And.decidable
--   instance {c} : Decidable (IsSolved c) := by apply And.decidable

-- end SolutionState
