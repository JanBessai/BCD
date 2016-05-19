Require Import Filter.
Require Import Coq.Structures.Equalities.

Module HSTy.
  Module MachineIntVar <: VariableAlphabet.
    Axiom t : Set.
    Axiom eq_dec: forall α β : t, { α = β } + { ~ (α = β) }.

    Include HasUsualEq.
    Include UsualIsEq.
    Extract Inductive nat => "Prelude.Int" [ "0" "Prelude.succ" ] "(\ fO fS n -> if n == 0 then fO () else fS (n - 1))".
    Extract Constant plus => "(Prelude.+)".
    Extract Inductive prod => "(,)" [ "(,)" ].
    Extract Constant fst => "Prelude.fst".
    Extract Constant snd => "Prelude.snd".

    Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
    Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

    Extract Constant t => "Prelude.Int".
    Extract Constant eq_dec => "(Prelude.==)".
  End MachineIntVar.

  Module T := MachineIntVar <+ Types.
  Include T.
End HSTy.

Extraction Language Haskell.
Extraction "BCD.hs" HSTy.
