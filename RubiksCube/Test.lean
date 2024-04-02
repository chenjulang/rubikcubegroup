import RubiksCube.FuncProofs

def List.invert : List RubiksSuperType → List RubiksSuperType
  | [] => []
  | c :: cs =>
      -- dbg_trace "add1: {cs}";
      invert cs ++ [c⁻¹]

def conjList
(l1:List RubiksSuperType)
(l2:List RubiksSuperType)
: List RubiksSuperType
:=
  l1 ++ l2 ++ (l1.invert)

def V_L_List : (l:List RubiksSuperType) → List RubiksSuperType
:= fun l => (l.map VariantFaceTurn_L)
def V_R_List : (l:List RubiksSuperType) → List RubiksSuperType
:= fun l => (l.map VariantFaceTurn_R)
def V_B_List : (l:List RubiksSuperType) → List RubiksSuperType
:= fun l => (l.map VariantFaceTurn_B)

-- 当前状态A：
def statusA := D'*F2*U2*F2*U'*F2*D'*B2*D'*U'*L'*B*R2*B*D2*F2*U2*R'*D*U'
-- D' F2 U2 F2 U' F2 D' B2 D' U' L' B R2 B D2 F2 U2 R' D U'
-- D' F F U U F F U' F F D' B B D' U' L' B R R B D D F F U U R' D U'
-- #eval statusA
-- #eval Corner_Absolute_Orient (D'*F2*U2*F2*U'*F2*D'*B2*D'*U'*L'*B*R2*B*D2*F2*U2*R'*D*U').1
-- ![1, 1, 1, 0, 1, 1, 1, 0]

-- 奇排列，变偶排列：
def OddToEven := G5Perm
def reshow_OddToEven := G5Perm⁻¹


-- 4个分别还原操作：
def solve_Corner_Permute:= (
  (conj R2 (VarR G4Perm_List)⁻¹)
* (VarL G4Perm_List)
* (conj (D*L'*D'*F2*L) (VarL G4Perm_List))
* (conj L2 (G4Perm)⁻¹)
)⁻¹

-- #eval toString$
--   (
--   (conjList [R,R] (V_R_List G4Perm_List).invert)
--   ++ (V_L_List G4Perm_List)
--   ++ (conjList [D,L',D',F2,L] (V_L_List G4Perm_List))
--   ++ (conjList [L,L] G4Perm_List.invert)
--   ).invert


def solve_Edge_Permute :=
(
  (conj (U'*L2*U*B') (VarL G3Perm_List))
* (conj F (G3Perm)⁻¹)
* (conj F2 (VarR G3Perm_List)⁻¹)
* (conj (D'*L2) G3Perm)
)⁻¹

-- #eval toString$
--   (
--   (conjList [U',L,L,U,B'] (V_L_List G3Perm_List))
--   ++ (conjList [F] G3Perm_List.invert)
--   ++ (conjList [F,F] (V_R_List G3Perm_List).invert)
--   ++ (conjList [D',L,L] G3Perm_List)
--   ).invert


def solve_Corner_Orient:=
(conj D G1Perm)
* (conj (U'*D) G1Perm)
* (conj (U*D') G1Perm)
* (conj D' G1Perm)
* (conj D2 G1Perm) * (conj D2 G1Perm)

#eval (conj D2 G1Perm) * (conj D2 G1Perm)


def reshow_Edge_Orient:= 1


-- 检验：
--1:
-- 一步步检查问题：
-- #eval (conj R2 (VarR G4Perm_List)⁻¹) --ok
-- #eval (VarL G4Perm_List) --ok
-- #eval (conj (D*L'*D'*F2*L) (VarL G4Perm_List)) -- ok
-- #eval (conj L2 (G4Perm)⁻¹) --ok
-- #eval (reshow_Corner_Permute * reshow_OddToEven ).1.permute = statusA.1.permute -- true

--2:
-- #eval (reshow_Edge_Permute * reshow_OddToEven ).2.permute = statusA.2.permute -- true

--3:
-- 一步步检查问题：
-- #eval (conj D G1Perm) --ok
-- #eval (conj (U'*D) G1Perm) --ok
-- #eval (conj (U*D') G1Perm) --ok
-- #eval (conj D' G1Perm) --ok
-- #eval  (conj D2 G1Perm) * (conj D2 G1Perm)
-- #eval reshow_Corner_Orient.1.orient = (Corner_Absolute_Orient statusA.1) -- true

--4:
-- #eval (reshow_Corner_Orient * reshow_OddToEven).2.orient = statusA.2.orient -- true


-- 还原方向数：
#eval (statusA * solve_Corner_Orient).1.orient = 0
-- 还原角块位置：
#eval (statusA*OddToEven * solve_Corner_Permute).1.permute = 1
-- 还原棱块位置：
#eval (statusA*OddToEven * solve_Edge_Permute).2.permute = 1

-- 还原魔方：
-- 1.先方向，后位置(先角后棱)
#eval statusA * (OddToEven * solve_Corner_Orient * solve_Corner_Permute * solve_Edge_Permute)
  = Solved -- true
-- 1.先方向，后位置(先棱后角)
#eval statusA * (OddToEven * solve_Corner_Orient * solve_Edge_Permute * solve_Corner_Permute)
  = Solved -- true

#eval statusA * (solve_Corner_Orient * OddToEven * solve_Edge_Permute * solve_Corner_Permute)
  = Solved -- true


#eval solve_Corner_Orient
