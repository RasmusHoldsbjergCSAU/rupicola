Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Cells.Cells.
Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.


    Definition swapthree_gallina_spec (c1 c2 c3: cell) :=
        let/d v1 := get c1 in
        let/d v2 := get c2 in
        let/d v3 := get c3 in
        let/d c1 := put v1 c2 in
        let/d c2 := put v2 c3 in
        let/d c1 := put v3 c1 in
        (c1, c2, c3).

  Import ListNotations.
  Definition ThreeCells a_ptr b_ptr c_ptr abc
  : list word -> Semantics.mem -> Prop :=
  fun _ =>
    seps [cell_value a_ptr (fst (fst abc)); cell_value b_ptr (snd (fst abc)); cell_value c_ptr (snd abc)].


    Hint Unfold ThreeCells : compiler.
    Derive swapthree_body SuchThat
        (let swapthree := ("swapthree", (["a"; "b"; "c"], [], swapthree_body)) in
            program_logic_goal_for swapthree
            (forall functions,
            forall (a_ptr : word) (a : cell) (b_ptr : word) (b : cell) (c_ptr : word) (c : cell) (tr : Semantics.trace) (R : Semantics.mem -> Prop) (mem : Semantics.mem),
            sep (ThreeCells a_ptr b_ptr c_ptr (a,b,c) []) R mem ->
            WeakestPrecondition.call
                (swapthree :: functions)
                "swap"
                tr mem [a_ptr;b_ptr;c_ptr]
                (postcondition_func_norets
                    (ThreeCells a_ptr b_ptr c_ptr (swapthree_gallina_spec a b c))
                    R tr)))
    As swapthree_body_correct.
    Proof.
    try compile.
    Abort.

End with_parameters.