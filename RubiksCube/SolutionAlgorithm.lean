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
  | c :: cs => invert cs ++ [c⁻¹]
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


/-- 一个保持方向数的棱位置2循环+角位置2循环-/
def TPList
: List RubiksSuperType
:= [R, U, R', U', R', F, R2, U', R', U', R, U, R', F']

/-- 一个不保持方向数的棱位置2循环+角位置2循环-/
def AYPList
: List RubiksSuperType
:= [R, U', R', U', R, U, R', F', R, U, R', U', R', F, R]

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
逐个检查 i 是否与 x 不同且 f i 不等于 0。得到这样的一个索引。
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
#eval (Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)]) -- : Fin 8 → Fin 3
-- ![2, 0, 0, 1, 2, 0, 0, 1]
-- #eval Misoriented 1 (Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)]) -- 是一个索引：满足索引不等于参数x，索引对应项不等于0。-- 0
-- #eval Misoriented 2 (Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)]) -- 0
-- #eval Misoriented 0 (Orient 8 3 [(0, 2), (3, 1), (4, 2), (7, 1)]) -- 3


abbrev FT := {t : RubiksSuperType // FaceTurn t}

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

--todo--
/-- 应该是在单纯还原角块-/
unsafe def solveCorners
: RubiksSuperType → List RubiksSuperType
:=
  fun c =>
    if CornersSolved c then []
    else
      let buffer := c.1.permute⁻¹ 0
      let swap := match buffer with
        | 0 => cornerSwap (Misoriented 0 c.1.orient) 0
        | _ => cornerSwap buffer (c.1.orient 0)
      swap ++ solveCorners (update c swap)

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

unsafe def solveEdges : RubiksSuperType → List RubiksSuperType := fun c =>
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
-- #eval toString $ solveEdges (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U')
-- #eval update R (solveEdges R)

-- #eval toString $ update R (solveCube R)
-- #eval toString $ update (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U') (solveCube (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U'))

/- Since the solution algorithm is unsafe, it cannot be used directly in the widget declarations,
but the list of moves that solve the edges were generated using the algorithm and
the toString method above. -/
#widget cubeWidget (cubeStickerJson (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U'))
#widget cubeWidget (cubeStickerJson (update (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U') [F, R, U, R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U', R', F', B', L, R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L', B, B', R, U', R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U, R', B, B, L, R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L', B', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', B, R, U', R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U, R', B', F, L', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L, F', R, U, R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U', R', F', R, U, R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U', R', F, D2, L2, R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L2, D2, D, F, L', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L, F', D', D2, L2, R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L2, D2]))
