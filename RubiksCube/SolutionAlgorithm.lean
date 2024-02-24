import RubiksCube.RubiksCubeFunc
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

set_option autoImplicit true
-- set_option trace.Meta.synthInstance true

open Equiv Perm Lean Widget

open scoped ProofWidgets.Jsx

-- 盲拧坑

/-- invert and update are useful for dealing with setup moves and partial solutions.
得到逆操作-/
def invert : List RubiksSuperType → List RubiksSuperType
  | [] => []
  | c :: cs =>
      -- dbg_trace "add1: {cs}";
      invert cs ++ [c⁻¹]
-- #eval (invert [F,R,B])
-- c=F cs=[R,B] => invert [R,B] ++ [F']
-- invert [R,B] = c=R,cs=[B] => invert [B] ++ [R']
-- invert [B] = c=B,cs=[] => invert [] ++ [B']
-- 总结： (invert [B] ++ [R']) ++ [F'] = (invert [] ++ [B'] ++ [R']) ++ [F']
-- = ([B'] ++ [R']) ++ [F'] = [B',R',F']



/-- 在最前面插入一个操作 -/
def update : RubiksSuperType → List RubiksSuperType → RubiksSuperType
  | c, [] => c
  | c, u :: us => update (c * u) us
-- #eval update F [R,B]
-- c=F,u=R,us=[B] => update (F*R) [B]
-- update (F*R) [B] = c=(F*R) u=B us=[] => update (F*R*B) []
-- update (F*R*B) [] = c=(F*R*B)  []=[] => (F*R*B)
-- 总结：update (F*R) [B] = update (F*R*B) [] = (F*R*B)

/-- 在还原状态前面插入一个操作列表-/
def generate
: List RubiksSuperType → RubiksSuperType
:= fun l => update Solved l
-- #eval generate [F]


/-- 用来还原棱块的： 一个保持方向数的棱位置2循环+角位置2循环。角块2↔3,棱块2↔4。-/
def TPList
: List RubiksSuperType
:= [R, U, R', U', R', F, R2, U', R', U', R, U, R', F']
-- R U R' U' R' F R R U' R' U' R U R' F'

/-- 用来还原角块的： 一个不保持方向数的棱位置2循环+角位置2循环。角块4↔6,棱块3↔4-/
def AYPList
: List RubiksSuperType
:= [R, U', R', U', R, U, R', F', R, U, R', U', R', F, R]
-- R U' R' U' R U R' F' R U R' U' R' F R

/-- 盲拧视频中所谓的“奇偶检验”公式。
一个保持方向数的棱位置2循环+角位置2循环-/
-- R U' R' U' R U R D R' U' R D' R' U U R' U'
def BlindCornerList
: List RubiksSuperType
:= [R,U',R',U',R,U,R,D,R',U',R,D',R',U,U,R',U']

-- 缓冲区就是setup的时候，和想用的公式没有交集中，想通过想用公式到达的那个块。
/- This function is used to find a (non-buffer) piece that is incorrectly oriented
 whenever the buffer piece is in the buffer slot but the relevant set of pieces is not solved.
 This process of swapping the buffer piece out of the buffer slot is sometimes referred to
 as "breaking into a new cycle,"
  and is discussed here: https://youtu.be/ZZ41gWvltT8?si=LxTY7dWfq_0yGaP6&t=220.
-/
/-- 函数效果：
从0到(n-1)逐个检查索引 i 是否与 x 不同且 f i 不等于 0。得到这样的一个索引。
  1.如果找到满足条件的 i，则将其赋值给 out 并结束循环。
  2.如果循环结束后没有找到满足条件的 i，则返回 x 作为默认值。
-/
def Misoriented {n m : ℕ+}
(x : Fin n)
(f : Fin n → Fin m)
: Fin n :=
  Id.run do
  let mut out := x
  for h : i in [0:n] do
    let i : Fin n := ⟨i, h.2⟩
    if i != x ∧ f i != 0 then
      out := i
      break
    else continue
  out

-- def testParam
-- -- {n m : ℕ+}
-- -- :Fin n → Fin m
-- : Fin 8 → Fin 3
--   | 0 => 1
--   | 1 => 2
--   | 2 => 3
--   | 3 => 2
--   | 4 => 1
--   | 5 => 2
--   | 6 => 3
--   | 7 => 2
-- #eval (Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)]) -- : Fin 8 → Fin 3
-- ![2, 0, 0, 1, 2, 0, 0, 1]
-- #eval Misoriented 1 (Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)]) -- 是一个索引：满足索引不等于参数x，索引对应项不等于0。-- 0
-- #eval Misoriented 2 (Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)]) -- 0
-- #eval Misoriented 0 (Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)]) -- 3


abbrev FT := {t : RubiksSuperType // FaceTurn t}

-- 盲拧视频原理是不是用2循环来将一个队列全部排好呢？对的，这里所说的缓冲块，是让某个块先在这里停留一下，下一波操作就会把它还原到原位置。
  -- 而且这两个基本公式的选取，也是尽量找变换的块都是扎堆在一个面的很近的位置。
-- 举例还原6个纸牌： 3 6 4
--                5 2 1
-- 要还原这6个的位置，盲拧的策略首先是只通过2轮换来还原
-- 先排好还原的顺序：3,4,5,2,6,1 。
-- 3 6 4
-- 5 2 1 →
-- 4 6 3
-- 5 2 1 →
-- 5 6 3
-- 4 2 1 →
-- 2 6 3
-- 4 5 1 →
-- 6 2 3
-- 4 5 1 →
-- 1 2 3
-- 4 5 6
-- 为什么只操作了5次？因为前5个都还原了，最后一个还不还原吗，还能去哪～～
------------------
-- 盲拧教程中：这些其实就是特殊的情况：
  -- 1.“小循环”指的是如何用之前的公式解决单纯的3棱块位置循环 or 单纯的2棱块方向数+1 or ...
  -- 2.“奇偶校验”是一个公式，效果是方向数不变，角块位置2循环+棱块位置2循环。
        -- 使用这个的原因是：比如在棱块位置还原过程中，随之变化的其实还有两个角块
        -- 如果公式使用了奇数次，那么两个角块位置是交换的。
        -- 如果到最后只剩下单纯的2棱块位置乱了，还有上述2个角块位置乱了，那么只需要使用这个公式来补漏。



/-- 可以观察到不存在L,U,B,是因为不想和棱块3,4有交集。
所以效果至少会有：棱块位置循环3↔4-/
def cornerSetup
: Fin 8 → Fin 3 → List RubiksSuperType
  | 0, _ => []
  | 1, 0 => [R, D']
  | 1, 1 => [R2]
  | 1, 2 => [R', F]
  | 2, 0 => [F]
  | 2, 1 => [F2, D]
  | 2, 2 => [R']
  | 3, 0 => [F, R']
  | 3, 1 => [F2]
  | 3, 2 => [F', D]
  | 4, 0 => [F']
  | 4, 1 => [D]
  | 4, 2 => [F2, R']
  | 5, 0 => [F', R']
  | 5, 1 => [] -- ?
  | 5, 2 => [D, R]
  | 6, 0 => [D2, F']
  | 6, 1 => [D']
  | 6, 2 => [R]
  | 7, 0 => [D, F']
  | 7, 1 => [D2]
  | 7, 2 => [D', R]

/-- 交换子思想-/
def cornerSwap
(corner : Fin 8)
(orientation : Fin 3)
: List RubiksSuperType
:=
  let setup := cornerSetup corner orientation
  setup ++ AYPList ++ (invert setup)

-- 棱块一直是3↔4吗？真是
-- cornerSwap ? ?:
-- AYP: R U' R' U' R U R' F' R U R' U' R' F R
-- 1,0:方向不变,角3↔4,棱3↔4
-- 1,1:方向变,角3↔4,棱3↔4
-- 1,2:方向变,角↔,棱↔
-- 2,0:方向变,角↔,棱↔
-- 2,1:方向变,角↔,棱↔
-- 2,2:方向变,角↔,棱↔
-- 3,0:方向变,角↔,棱↔
-- 3,1:方向变,角↔,棱↔
-- 3,2:方向变,角↔,棱↔
-- 4,0:方向变,角↔,棱↔
-- 4,1:方向变,角↔,棱↔
-- 4,2:方向变,角↔,棱↔
-- 5,0:方向变,角↔,棱↔
-- 5,1:方向变,角↔,棱↔
-- 5,2:方向变,角↔,棱↔
-- 6,0:方向变,角↔,棱↔
-- 6,1:方向变,角↔,棱↔
-- 6,2:方向变,角↔,棱↔
-- 7,0:方向变,角↔,棱↔
-- 7,1:方向变,角↔,棱↔
-- 7,2:方向变,角↔,棱↔



-- #eval toString $ cornerSwap 2 0
-- F R U' R' U' R U R' F' R U R' U' R' F R F'


--todo--
-- solveCorners如何把所有角块都solve掉呢？是否需要循环语句呢？其实就是找出一个长度为8的列表，然后8个交换子按顺序执行就可以了。
-- 问题就是在每一次swap，如何写代码可以根据列表来逐个还原?

/-- 应该是在单纯还原角块-/
unsafe def solveCorners
: RubiksSuperType → List RubiksSuperType
-- 举例：传入参数(update Solved (cornerSwap 7 1))
  -- 也就是经过了这样的打乱：-- D D R U' R' U' R U R' F' R U R' U' R' F R D D
  -- 当前状态：是一个角块2循环+棱块2循环
  -- 期待的解决方案也是：D D TPList D D
  -- 所以期待的swap = cornerSwap 7 1
:=
  fun c =>
    dbg_trace "打印每一次c: {c}";
    if CornersSolved c then []
    else
      let buffer := c.1.permute⁻¹ 0
      -- c.1.permute = [0,3,6,4,7,5,1,2] ,就是循环：(1,3,4,2,6)
      -- c.1.permute⁻¹ 就是 (6,2,4,3,1)
      -- buffer = c.1.permute⁻¹ 0 = 0
      let swap := match buffer with
        | 0 => cornerSwap (Misoriented 0 c.1.orient) 0 -- 这一步得到的就是一个交换子公式本身。
        -- 0 => cornerSwap (Misoriented 0 c.1.orient) 0
        -- swap = [R, D', R, U', R', U', R, U, R', F', R, U, R', U', R', F, R, D, R']
        | _ => cornerSwap buffer (c.1.orient 0)
      dbg_trace "打印每一次swap: {swap}";
      (swap ++ solveCorners (update c swap)) -- 直接写一个对象就是返回值了
      ----
      -- let swap := cornerSwap 7 1
      -- dbg_trace "打印每一次swap: {swap}";
      -- (swap ++ solveCorners (update c swap))



-- #eval cornerSwap 7 1
-- #eval toString $ cornerSwap 7 1
  -- D D R U' R' U' R U R' F' R U R' U' R' F R D D -- 是一个角块2循环+棱块2循环
-- #eval update Solved (cornerSwap 7 1)
-- #eval toString $ cornerSwap (Misoriented 0 (update Solved (cornerSwap 7 1)).1.orient) 0
-- #eval toString $ solveCorners (update Solved (cornerSwap 7 1))
-- 5次才还原？？？明明一次就可以的
-- D, D, R, U', R', U', R, U, R', F', R, U, R', U', R', F, R, D, D, D, D, R, U', R', U', R, U, R', F', R, U, R', U', R', F, R, D, D, D, D, R, U', R', U', R, U, R', F', R, U, R', U', R', F, R, D, D, D, D, R, U', R', U', R, U, R', F', R, U, R', U', R', F, R, D, D, D, D, R, U', R', U', R, U, R', F', R, U, R', U', R', F, R, D, D

def edgeSetup : Fin 12 → Fin 2 → List RubiksSuperType
  | 0, 0 => [R, U', R']
  | 0, 1 => [B, L]
  | 1, _ => []
  | 2, 0 => [R, U, R']
  | 2, 1 => [F', L']
  | 3, 0 => []
  | 3, 1 => [L2, D, F, L']
  | 4, 0 => [D', L2]
  | 4, 1 => [F, L']
  | 5, 0 => [D2, L2]
  | 5, 1 => [D', F, L']
  | 6, 0 => [D, L2]
  | 6, 1 => [B', L]
  | 7, 0 => [L2]
  | 7, 1 => [D, F, L']
  | 8, 0 => [L]
  | 8, 1 => [B', R, U', R']
  | 9, 0 => [B2, L]
  | 9, 1 => [B, R, U', R']
  | 10, 0 => [F2, L']
  | 10, 1 => [F', R, U, R']
  | 11, 0 => [L']
  | 11, 1 => [F, R, U, R']

def edgeSwap (edge : Fin 12) (orientation : Fin 2) : List RubiksSuperType :=
  let setup := edgeSetup edge orientation
  setup ++ TPList ++ (invert setup)


unsafe def solveEdges
: RubiksSuperType → List RubiksSuperType
:=
  fun c =>
    if EdgesSolved c then []
    else
      let buffer := c.2.permute⁻¹ 1
      let swap := match buffer with
        | 1 => edgeSwap (Misoriented 1 c.2.orient) 0
        | _ => edgeSwap buffer (c.2.orient 1)
      swap ++ solveEdges (update c swap)


unsafe def solveCube : RubiksSuperType → List RubiksSuperType := fun c =>
  let edgeSolution := solveEdges c
  edgeSolution ++ solveCorners (update c edgeSolution)


unsafe def solveScramble : List RubiksSuperType → List RubiksSuperType :=
  fun l => solveCube (generate l)



#eval toString $ cornerSwap 7 1
  -- 一个不保持TW坐标下方向数的棱位置2循环+角位置2循环
  -- 这是在造公式啊～～
  -- D D R U' R' U' R U R' F' R U R' U' R' F R D D

-- #eval toString $ solveEdges (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U')
  -- stackoverflow报错了Server process for file:///Users/chenjulang/Desktop/%E6%95%B0%E5%AD%A6/rubikcubegroup/RubiksCube/SolutionAlgorithm.lean crashed, likely due to a stack overflow or a bug.
-- #eval update R (solveEdges R)

-- #eval toString $ update R (solveCube R)
-- #eval toString $ update (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U') (solveCube (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U'))

/- Since the solution algorithm is unsafe, it cannot be used directly in the widget declarations,
but the list of moves that solve the edges were generated using the algorithm and
the toString method above. -/
#widget cubeWidget (cubeStickerJson (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U'))
#widget cubeWidget (cubeStickerJson (update (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U') [F, R, U, R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U', R', F', B', L, R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L', B, B', R, U', R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U, R', B, B, L, R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L', B', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', B, R, U', R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U, R', B', F, L', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L, F', R, U, R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U', R', F', R, U, R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U', R', F, D2, L2, R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L2, D2, D, F, L', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L, F', D', D2, L2, R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L2, D2]))
