import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin
open Equiv Equiv.Perm

-- def P1: Prop := sorry

-- lemma lemma31
-- (p : Perm (Fin 5))
-- (h1: IsThreeCycle p)
-- : P1
-- := by sorry

mutual
      def foo (n : Nat) : Nat :=
      if n = 0 then 1 else n * bar (n - 1)

      def bar (n : Nat) : Nat :=
      if n = 0 then 1 else n * foo (n - 1)
end
#eval foo 10 -- 3628800
