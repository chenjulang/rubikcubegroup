import Lean
import RubiksCube.RubiksCubeFunc
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin

open Equiv Perm Lean Widget

open scoped ProofWidgets.Jsx

/- invert and update are useful for dealing with setup moves and partial solutions. -/
def invert : List RubiksSuperType → List RubiksSuperType
  | [] => []
  | c :: cs => invert cs ++ [c⁻¹]

def update : RubiksSuperType → List RubiksSuperType → RubiksSuperType
  | c, [] => c
  | c, u :: us => update (c * u) us

def generate : List RubiksSuperType → RubiksSuperType := fun l => update Solved l

def AYPList : List RubiksSuperType := [R, U', R', U', R, U, R', F', R, U, R', U', R', F, R]

def TPList : List RubiksSuperType := [R, U, R', U', R', F, R2, U', R', U', R, U, R', F']

/- This function is used to find a (non-buffer) piece that is incorrectly oriented whenever the buffer piece is in the buffer slot but the relevant set of pieces is not solved. This process of swapping the buffer piece out of the buffer slot is sometimes referred to as "breaking into a new cycle," and is discussed here: https://youtu.be/ZZ41gWvltT8?si=LxTY7dWfq_0yGaP6&t=220. -/
def Misoriented {n m : ℕ+} (x : Fin n) (f : Fin n → Fin m) : Fin n :=
  Id.run do
  let mut out := x
  for h : i in [0:n] do
    let i : Fin n := ⟨i, h.2⟩
    if i != x ∧ f i != 0 then
      out := i
      break
    else continue
  out

-- #eval Misoriented (fun x => 2 : Fin 8 → Fin 3) -- not working...why?

abbrev FT := {t : RubiksSuperType // FaceTurn t}

def cornerSetup : Fin 8 → Fin 3 → List RubiksSuperType
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
  | 5, 1 => []
  | 5, 2 => [D, R]
  | 6, 0 => [D2, F']
  | 6, 1 => [D']
  | 6, 2 => [R]
  | 7, 0 => [D, F']
  | 7, 1 => [D2]
  | 7, 2 => [D', R]

def cornerSwap (corner : Fin 8) (orientation : Fin 3) : List RubiksSuperType :=
  let setup := cornerSetup corner orientation
  setup ++ AYPList ++ (invert setup)

unsafe def solveCorners : RubiksSuperType → List RubiksSuperType := fun c =>
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
#eval toString $ solveEdges (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U')
#eval update R (solveEdges R)

#eval toString $ update R (solveCube R)
#eval toString $ update (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U') (solveCube (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U'))

/- Since the solution algorithm is unsafe, it cannot be used directly in the widget declarations, but the list of moves that solve the edges were generated using the algorithm and the toString method above. -/
#widget cubeWidget (cubeStickerJson (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U'))
#widget cubeWidget (cubeStickerJson (update (R * B2 * D * L2 * B2 * R2 * B2 * D * F2 * U * R2 * D2 * R' * U' * B * F * L' * D2 * R * D' * U') [F, R, U, R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U', R', F', B', L, R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L', B, B', R, U', R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U, R', B, B, L, R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L', B', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', B, R, U', R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U, R', B', F, L', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L, F', R, U, R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U', R', F', R, U, R', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', R, U', R', F, D2, L2, R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L2, D2, D, F, L', R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L, F', D', D2, L2, R, U, R', U', R', F, R2, U', R', U', R, U, R', F', L2, D2]))
