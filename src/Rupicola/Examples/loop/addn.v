Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.SepLocals.
Require Import Rupicola.Lib.ControlFlow.DownTo.
Require Import Rupicola.Lib.ControlFlow.CondSwap.
Require Import Rupicola.Examples.Cells.Cells.
Require Import Rupicola.Examples.ECC.Field.
Require Import Rupicola.Examples.ECC.Field.

Check cell.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

Check downto.
Check word.

Context (bound : nat).
Context (bound_pos : (bound > 0)%nat).

Definition addn_gallina_spec (c: Z) :=
  let/d count := word.of_Z (Z.of_nat bound) in 
  let/d c := 
    downto  (word.of_Z 0)
            bound
            (fun state i => word.add (word.of_Z 1) state) in
  c. 
 
  Definition addn_result (c: word) (pc: address) (result: word):
    list word -> Semantics.mem -> Prop :=
    fun _ => (emp (c =  (word.of_Z (word.wrap (Z.of_nat bound)))) * (pc ~> c))%sep.

  Instance spec_of_addn : spec_of "addn" :=
  (forall! (pc : address) (c : word),
  (sep (pc ~> c))
    ===>
    "addn" @ [pc; c]
    ===>
    addn_result c pc (addn_gallina_spec c)).



  Context (zbound : Z)
  (zbound_small : word.wrap zbound = zbound)
  (zbound_eq : zbound =  Z.of_nat bound).

Check sep.

(* Definition downto_inv  := *)
Ltac setup_downto_inv_init :=
  lift_eexists; sepsimpl;
  (* first fill in any map.get goals where we know the variable names *)
  lazymatch goal with
  | |- map.get _ ?x = Some _ =>
    tryif is_evar x then idtac
    else (autorewrite with mapsimpl; reflexivity)
  | _ => idtac
  end;
  lazymatch goal with
  | |- (_ * _)%sep _ => ecancel_assumption
  | _ => idtac
  end.

Definition downto_inv
    (locals : Semantics.locals) 
    (_ : nat)
    (gst : bool)
    (st : word)
    (_ : list word): Semantics.mem -> Prop :=
  (emp True). 

  Check mul.

Derive addn_body SuchThat
       (let addn := ("addn", (["c"; "c_ptr"], [], addn_body)) in
        program_logic_goal_for addn
        (ltac:( let x := program_logic_goal_for_function
                                addn ([]: list string) in
                     exact x)))
        
        
        (* (forall functions,
         forall n c c_ptr tr R mem,
           sep (c_ptr ~> c) R mem ->
           WeakestPrecondition.call
             (addn :: functions)
             "addn"
             tr mem [c_ptr]
             (postcondition_func_norets
                (c_ptr (addn_gallina_spec c))
                R tr))) *)
  As addn_body_correct.
Proof.
  cbv [program_logic_goal_for spec_of_addn].
  setup.
  repeat safe_compile_step.

  let i_var := gen_sym_fetch "v" in (* last used variable name *)
  let locals := lazymatch goal with
                | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
  remember locals as L;
  evar (l : map.rep (map:=Semantics.locals));
    let Hl := fresh in
    assert (map.remove L i_var = l) as Hl by
          (subst L; push_map_remove; subst_lets_in_goal; reflexivity);
      subst l;
      match type of Hl with
      | _ = ?l =>
        sep_from_literal_locals l;
          match goal with H : sep _ _ l |- _ =>
                          rewrite <-Hl in H; clear Hl
          end
      end.


let counter_var := gen_sym_fetch "v" in
  let locals := lazymatch goal with
                    | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
  
  simple eapply compile_downto with
   (ginit := false)
   (wcount := word.of_Z ( word.wrap zbound))
   (i_var := counter_var)
   (ghost_step := fun s b count => false)
   (Inv := downto_inv); auto.
    - cbv [downto_inv]. sepsimpl; eauto.
    - subst. autorewrite with mapsimpl. unfold head. rewrite zbound_small. eauto.
    - rewrite ?zbound_small, word.unsigned_of_Z; solve [eauto using zbound_small].
    - (* loop body *)
    intros. clear_old_seps.
    destruct_products.
    cbv [downto_inv] in * |-. sepsimpl_hyps.
    eexists; intros.

    (* convert locals back to literal map using the separation-logic
       condition; an alternative would be to have all lemmas play nice with
       locals in separation logic *)
    (* match goal with H : sep _ _ (map.remove _ ?i_var)
                    |- context [map.get _ ?i_var = Some ?wi] =>
                    eapply Var_put_remove with (v:=wi) in H;
                      eapply sep_assoc in H
    end. *)
    (* literal_locals_from_sep. *)

    repeat safe_compile_step.
    cbv zeta.
(* first, resolve evars *)
    (* *after* evar resolution *)
    repeat safe_compile_step.

    
    (* unset loop-local variables *)
    repeat remove_unused_var.

    compile_done.
    { (* prove locals postcondition *)
      autorewrite with mapsimpl.
      ssplit; [ | reflexivity ].
      subst_lets_in_goal. reflexivity. }
    { (* prove loop invariant held *)
      cbv [downto_inv]. auto.
      cleanup; sepsimpl_hyps.
      repeat match goal with
             | H : ?x = (_, _) |- context [fst ?x] =>
               rewrite H; progress cbn [fst snd]
             end.
      clear_old_seps.
      lift_eexists. sepsimpl; auto. }
  - intros. destruct_products.
  cbv [downto_inv downto_inv] in *.
  sepsimpl_hyps.

  (* convert locals back to literal map using the separation-logic
     condition; an alternative would be to have all lemmas play nice with
     locals in separation logic *)
  
  repeat safe_compile_step.
  cbv match zeta.

  repeat safe_compile_step.

  (* the output of this last operation needs to be stored in the pointer
     for the output, so we guide the automation to the right pointer *)
  clear_old_seps.

  repeat safe_compile_step.  
  (* destruct the hypothesis identifying the new pointers as some swapping
     of the original ones *)
  all:cleanup; subst.
  all:lift_eexists. subst_lets_in_goal. auto. repeat safe_compile_step. 
  compile_done.
Qed.

End with_parameters.