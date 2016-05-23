Require Import Filter.
Require Import Coq.Structures.Equalities.

Module OcamlTy.
  Module MachineIntVar <: VariableAlphabet.
    Axiom t : Set.
    Axiom eq_dec: forall α β : t, { α = β } + { ~ (α = β) }.
    Include HasUsualEq.
    Include UsualIsEq.

    Extract Inductive nat => "int" [ "0" "succ" ] "(fun fO fS n => if n = 0 then fO () else fS (n - 1))".
    Extract Constant plus => "(fun x y -> x + y)".
    Extract Inductive prod => "(*)" [ "(,)" ].
    Extract Constant fst => "fst".
    Extract Constant snd => "snd".

    Extract Inductive bool => "bool" [ "true" "false" ].
    Extract Inductive sumbool => "bool" [ "true" "false" ].
    Extract Constant t => "int".
    Extract Constant eq_dec => "(fun x y -> x = y)".
  End MachineIntVar.

  Module T := MachineIntVar <+ Types.
End OcamlTy.


Extraction Language Ocaml.
Extraction "BCD.ml" OcamlTy.
