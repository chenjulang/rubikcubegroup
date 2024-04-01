import RubiksCube.FuncProofs

-- 当前状态A：
def statusA := D'*F2*U2*F2*U'*F2*D'*B2*D'*U'*L'*B*R2*B*D2*F2*U2*R'*D*U'
-- D' F2 U2 F2 U' F2 D' B2 D' U' L' B R2 B D2 F2 U2 R' D U'
-- D' F F U U F F U' F F D' B B D' U' L' B R R B D D F F U U R' D U'
-- 奇排列，变偶排列：
def OddToEven := G5Perm
def reshow_OddToEven := G5Perm⁻¹

-- #eval statusA
-- 4个分别还原操作：
def reshow_Corner_Permute:= (conj R2 (VarR G4Perm_List)⁻¹)
* (VarL G4Perm_List)
* (conj (D*L'*D'*F2*L) (VarL G4Perm_List))
* (conj L2 (G4Perm)⁻¹)

-- def reshow_Edge_Permute:= sorry

def reshow_Corner_Orient:= (conj U G1Perm) * (conj (U'*D') G1Perm) * (conj (U2*D) G1Perm)

-- def reshow_Edge_Orient:= sorry


-- 检验：
--1:
-- 一步步检查问题：
#eval (conj R2 (VarR G4Perm_List)⁻¹) --ok
#eval (VarL G4Perm_List) --ok
#eval (conj (D*L'*D'*F2*L) (VarL G4Perm_List)) -- ok
#eval (conj L2 (G4Perm)⁻¹) --ok
#eval (reshow_Corner_Permute * reshow_OddToEven ).1.permute = statusA.1.permute

--2:

--3:
#eval (reshow_Corner_Orient * reshow_OddToEven ).1.orient
#eval statusA.1.orient


--4:
