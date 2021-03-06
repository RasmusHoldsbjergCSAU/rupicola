Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.SepLocals.
Require Import Rupicola.Lib.ControlFlow.DownTo.
Require Import Rupicola.Lib.ControlFlow.CondSwap.
Require Import Rupicola.Examples.ECC.Field.
Require Import Rupicola.Examples.ECC.Point.
Require Import Rupicola.Examples.ECC.LadderStep.
Require Import Rupicola.Examples.ECC.ScalarField.
Local Open Scope Z_scope.

Section __.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {scalar_field_parameters : ScalarFieldParameters}.
  Context {bignum_representaton : BignumRepresentation}
          {scalar_representation : ScalarRepresentation}.
  Existing Instances spec_of_mul spec_of_square spec_of_add
           spec_of_sub spec_of_scmula24 spec_of_inv spec_of_bignum_copy
           spec_of_bignum_literal spec_of_sctestbit spec_of_ladderstep.

  Context {relax_bounds :
             forall X : bignum,
               bounded_by tight_bounds X ->
               bounded_by loose_bounds X}.
  Hint Resolve relax_bounds : compiler.

  Context (bound : nat).
  Context (bound_pos : (bound > 0)%nat).

  Section Gallina.
    (* Everything in gallina-world is mod M; ideally we will use a type like
       fiat-crypto's F for this *)
    Local Notation "0" := (0 mod M).
    Local Notation "1" := (1 mod M).
    Local Infix "+" := (fun x y => (x + y) mod M).
    Local Infix "-" := (fun x y => (x - y) mod M).
    Local Infix "*" := (fun x y => (x * y) mod M).
    Local Infix "^" := (fun x y => (x ^ y) mod M).

    Definition montladder_gallina (testbit:nat ->bool) (u:Z) : Z :=
      let/d P1 := (1, 0) in
      let/d P2 := (u, 1) in
      let/d swap := false in
      let/d count := bound in
      let/d ''(P1, P2, swap) :=
         downto
           (P1, P2, swap) (* initial state *)
           count
           (fun state i =>
              let '(P1, P2, swap) := state in
              let/d s_i := testbit i in
              let/d swap := xorb swap s_i in
              let/d ''(P1, P2) := cswap swap P1 P2 in
              let/d ''(P1, P2) := ladderstep_gallina u P1 P2 in
              let/d swap := s_i in
              (P1, P2, swap)
           ) in
      let/d ''(P1, P2) := cswap swap P1 P2 in
      let '(x, z) := P1 in
      let/d r := Finv z mod M in
      let/d r := (x * r) in
      r.
  End Gallina.

  Section MontLadder.
    (* need the literal Z form of bound to give to expr.literal *)
    Context (zbound : Z)
            (zbound_small : word.wrap zbound = zbound)
            (zbound_eq : zbound = Z.of_nat bound).

    (* TODO: make Placeholder [Lift1Prop.ex1 (fun x => Bignum p x)], and prove
       an iff1 with Bignum? Then we could even do some loop over the pointers to
       construct the seplogic condition *)
    (* TODO: should montladder return a pointer to the result? Currently writes
       result into U. *)
    Definition MontLadderResult
               (K : scalar)
               (pK pU pX1 pZ1 pX2 pZ2 pA pAA pB pBB pE pC pD pDA pCB : Semantics.word)
               (result : Z)
      : list word -> Semantics.mem -> Prop :=
      fun _ =>
      (liftexists U' X1' Z1' X2' Z2' A' AA' B' BB' E' C' D' DA' CB' : bignum,
         (emp (result = eval U' mod M)
          * (Scalar pK K * Bignum pU U'
             * Bignum pX1 X1' * Bignum pZ1 Z1'
             * Bignum pX2 X2' * Bignum pZ2 Z2'
             * Bignum pA A' * Bignum pAA AA'
             * Bignum pB B' * Bignum pBB BB'
             * Bignum pE E' * Bignum pC C' * Bignum pD D'
             * Bignum pDA DA' * Bignum pCB CB'))%sep).

    Instance spec_of_montladder : spec_of "montladder" :=
      forall!
            (K : scalar)
            (U X1 Z1 X2 Z2 : bignum) (* u, P1, P2 *)
            (A AA B BB E C D DA CB : bignum) (* ladderstep intermediates *)
            (pK pU pX1 pZ1 pX2 pZ2
                pA pAA pB pBB pE pC pD pDA pCB : Semantics.word),
        (fun R m =>
           bounded_by tight_bounds U
           /\ (Scalar pK K * Bignum pU U
               * Placeholder pX1 X1 * Placeholder pZ1 Z1
               * Placeholder pX2 X2 * Placeholder pZ2 Z2
               * Placeholder pA A * Placeholder pAA AA
               * Placeholder pB B * Placeholder pBB BB
               * Placeholder pE E * Placeholder pC C
               * Placeholder pD D * Placeholder pDA DA
               * Placeholder pCB CB * R)%sep m)
          ===>
          "montladder" @
          [pK; pU; pX1; pZ1; pX2; pZ2; pA; pAA; pB; pBB; pE; pC; pD; pDA; pCB]
          ===>
          (MontLadderResult
             K pK pU pX1 pZ1 pX2 pZ2 pA pAA pB pBB pE pC pD pDA pCB
             (montladder_gallina
                (fun i => Z.testbit (sceval K) (Z.of_nat i))
                (eval U mod M))).

    Ltac apply_compile_cswap_nocopy :=
      simple eapply compile_cswap_nocopy with
        (Data :=
           fun p (X : Z) =>
             (Lift1Prop.ex1
                (fun x =>
                   (emp (eval x mod M = X mod M) * Bignum p x)%sep)))
        (tmp:="tmp");
      [ lazymatch goal with
        | |- sep _ _ _ =>
          repeat lazymatch goal with
                 | |- Lift1Prop.ex1 _ _ => eexists
                 | |- eval _ mod _ = _ => eassumption
                 | _ => progress sepsimpl
                 end; ecancel_assumption
        | _ => idtac
        end .. | ];
      [ repeat compile_step .. | ];
      [ try congruence .. | ].

    Ltac compile_custom ::=
      gen_sym_inc;
      let name := gen_sym_fetch "v" in
      cleanup;
      first [ simple eapply compile_downto
            | simple eapply compile_sctestbit with (var:=name)
            | simple eapply compile_point_assign
            | simple eapply compile_bignum_literal
            | simple eapply compile_bignum_copy
            | simple eapply compile_cswap_pair
            | apply_compile_cswap_nocopy
            | simple eapply compile_ladderstep ].

    Definition downto_inv
               swap_var X1_var Z1_var X2_var Z2_var K_var
               K K_ptr X1_ptr Z1_ptr X2_ptr Z2_ptr Rl
               A_ptr AA_ptr B_ptr BB_ptr E_ptr C_ptr D_ptr DA_ptr CB_ptr
               (locals : Semantics.locals)
               (_ : nat)
               (gst : bool)
               (st : point * point * bool)
               (_ : list word)
      : Semantics.mem -> Prop :=
      let P1 := fst (fst st) in
      let P2 := snd (fst st) in
      let swap := snd st in
      let X1z := fst P1 in
      let Z1z := snd P1 in
      let X2z := fst P2 in
      let Z2z := snd P2 in
      let swapped := gst in
      liftexists X1_ptr' Z1_ptr' X2_ptr' Z2_ptr'
                 X1 Z1 X2 Z2 A AA B BB E C D DA CB,
        (emp (bounded_by tight_bounds X1
              /\ bounded_by tight_bounds Z1
              /\ bounded_by tight_bounds X2
              /\ bounded_by tight_bounds Z2
              /\ X1z mod M = X1z
              /\ Z1z mod M = Z1z
              /\ X2z mod M = X2z
              /\ Z2z mod M = Z2z
              /\ eval X1 mod M = X1z mod M
              /\ eval Z1 mod M = Z1z mod M
              /\ eval X2 mod M = X2z mod M
              /\ eval Z2 mod M = Z2z mod M
              /\ (if swapped
                  then (X1_ptr' = X2_ptr
                        /\ Z1_ptr' = Z2_ptr
                        /\ X2_ptr' = X1_ptr
                        /\ Z2_ptr' = Z1_ptr)
                  else (X1_ptr' = X1_ptr
                        /\ Z1_ptr' = Z1_ptr
                        /\ X2_ptr' = X2_ptr
                        /\ Z2_ptr' = Z2_ptr))
              /\ (Var swap_var (word.of_Z (Z.b2z swap)) * Var K_var K_ptr
                  * Var X1_var X1_ptr' * Var Z1_var Z1_ptr'
                  * Var X2_var X2_ptr' * Var Z2_var Z2_ptr'
                  * Rl)%sep locals)
         * (Scalar K_ptr K * Bignum X1_ptr' X1 * Bignum Z1_ptr' Z1
            * Bignum X2_ptr' X2 * Bignum Z2_ptr' Z2
            * Placeholder A_ptr A * Placeholder AA_ptr AA
            * Placeholder B_ptr B * Placeholder BB_ptr BB
            * Placeholder E_ptr E * Placeholder C_ptr C
            * Placeholder D_ptr D * Placeholder DA_ptr DA
            * Placeholder CB_ptr CB))%sep.

    Definition downto_ghost_step
               (K : scalar) (st : point * point * bool)
               (gst : bool) (i : nat) :=
      let swap := snd st in
      let swap := xorb swap (Z.testbit (sceval K) (Z.of_nat i)) in
      xorb gst swap.

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

    Ltac solve_downto_inv_subgoals :=
      lazymatch goal with
      | |- map.get _ _ = _ => subst_lets_in_goal; solve_map_get_goal
      | |- bounded_by _ _ => solve [ auto ]
      | |- eval _ mod _ = _ =>
        subst_lets_in_goal; rewrite ?Z.mod_mod by apply M_nonzero;
        first [ reflexivity | assumption ]
      | |- ?x mod M = ?x => subst_lets_in_goal;
                            rewrite ?Z.mod_mod by apply M_nonzero; reflexivity
      | |- ?x = ?x => reflexivity
      | |- ?x => fail "unrecognized side condition" x
      end.

    Lemma eval_fst_cswap s a b A B :
      eval a mod M = A mod M->
      eval b mod M = B mod M ->
      eval (fst (cswap s a b)) mod M = (fst (cswap s A B)) mod M.
    Proof. destruct s; cbn; auto. Qed.

    Lemma eval_snd_cswap s a b A B :
      eval a mod M = A mod M->
      eval b mod M = B mod M ->
      eval (snd (cswap s a b)) mod M = (snd (cswap s A B)) mod M.
    Proof. destruct s; cbn; auto. Qed.

    Lemma eval_fst_cswap_small s a b A B :
      eval a mod M = A ->
      eval b mod M = B ->
      eval (fst (cswap s a b)) mod M = (fst (cswap s A B)).
    Proof. destruct s; cbn; auto. Qed.

    Local Ltac swap_mod :=
      subst_lets_in_goal;
      repeat lazymatch goal with
             | H : ?x mod M = ?x |- context [cswap _ ?x] => rewrite <-H
             | H : ?x mod M = ?x |- context [cswap _ _ ?x] => rewrite <-H
             end;
      first [apply cswap_cases_fst | apply cswap_cases_snd ];
      auto using Z.mod_mod, M_nonzero.

    (* Adding word.unsigned_of_Z_1 and word.unsigned_of_Z_0 as hints to
       compiler doesn't work, presumably because of the typeclass
       preconditions. This is a hacky workaround. *)
    (* TODO: figure out a cleaner way to do this *)
    Lemma unsigned_of_Z_1 : word.unsigned (word.of_Z 1) = 1.
    Proof. exact word.unsigned_of_Z_1. Qed.
    Lemma unsigned_of_Z_0 : word.unsigned (word.of_Z 0) = 0.
    Proof. exact word.unsigned_of_Z_0. Qed.
    Hint Resolve unsigned_of_Z_0 unsigned_of_Z_1 : compiler.

    Ltac safe_compile_step :=
      compile_step;
      (* first pass fills in some evars *)
      [ repeat compile_step .. | idtac ];
      (* second pass must solve *)
      [ first [ solve [repeat compile_step]
              | solve [straightline_map_solver_locals] ] .. | idtac ].

    Ltac solve_field_subgoals_with_cswap :=
      lazymatch goal with
      | |- map.get _ _ = Some _ =>
        solve [subst_lets_in_goal; solve_map_get_goal]
      | |- eval _ mod _ = _ =>
        solve [eauto using eval_fst_cswap, eval_snd_cswap]
      | |- bounded_by _ (fst (cswap _ _ _)) =>
        apply cswap_cases_fst; solve [auto]
      | |- bounded_by _ (snd (cswap _ _ _)) =>
        apply cswap_cases_snd; solve [auto]
      | |- context [WeakestPrecondition.cmd] => idtac
      | _ => solve [eauto]
      end.

    (* create a new evar to take on the second swap clause *)
    Ltac rewrite_cswap_iff1_with_evar_frame :=
      match goal with
        |- (?P * ?R)%sep _ =>
        match P with context [cswap] => idtac end;
        is_evar R;
        let R1 := fresh "R" in
        let R2 := fresh "R" in
        evar (R1 : Semantics.mem -> Prop);
        evar (R2 : Semantics.mem -> Prop);
        unify R (sep R1 R2);
        seprewrite (cswap_iff1 Bignum)
      end.

    Ltac safe_field_compile_step :=
      field_compile_step;
      lazymatch goal with
      | |- sep _ ?R _ =>
        tryif is_evar R
        then (repeat rewrite_cswap_iff1_with_evar_frame)
        else (repeat seprewrite (cswap_iff1 Bignum));
        ecancel_assumption
      | _ => idtac
      end;
      lazymatch goal with
      | |- context [WeakestPrecondition.cmd] => idtac
      | _ => solve_field_subgoals_with_cswap
      end.

    Derive montladder_body SuchThat
           (let args := ["K"; "U"; "X1"; "Z1"; "X2"; "Z2";
                           "A"; "AA"; "B"; "BB"; "E"; "C"; "D"; "DA"; "CB"] in
            let montladder := ("montladder", (args, [], montladder_body)) in
            program_logic_goal_for
              montladder
              (ltac:(
                 let callees :=
                     constr:([bignum_literal; bignum_copy; "ladderstep";
                                sctestbit; inv; mul]) in
                 let x := program_logic_goal_for_function
                                montladder callees in
                     exact x)))
           As montladder_body_correct.
    Proof.
      cbv [program_logic_goal_for spec_of_montladder].
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

      let tmp_var := constr:("tmp") in
      let x1_var := constr:("X1") in
      let z1_var := constr:("Z1") in
      let x2_var := constr:("X2") in
      let z2_var := constr:("Z2") in
      let counter_var := gen_sym_fetch "v" in
      let locals := lazymatch goal with
                    | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
        simple eapply compile_downto with
            (wcount := word.of_Z (word.wrap zbound))
            (ginit := false)
            (i_var := counter_var)
            (ghost_step := downto_ghost_step K)
            (Inv :=
               downto_inv
                 _ x1_var z1_var x2_var z2_var _
                 _ pK pX1 pZ1 pX2 pZ2
                 _ pA pAA pB pBB pE pC pD pDA pCB);
        [ .. | subst L | subst L ].
      { cbv [downto_inv].
        setup_downto_inv_init.
        all:solve_downto_inv_subgoals. }
      { subst. autorewrite with mapsimpl.
        reflexivity. }
      { rewrite ?zbound_small, word.unsigned_of_Z;
          solve [eauto using zbound_small]. }
      { subst_lets_in_goal.
        rewrite ?word.unsigned_of_Z, ?zbound_small; lia. }
      { (* loop body *)
        intros. clear_old_seps.
        match goal with gst' := downto_ghost_step _ _ _ _ |- _ =>
                                subst gst' end.
        destruct_products.
        cbv [downto_inv] in * |-. sepsimpl_hyps.
        eexists; intros.

        (* convert locals back to literal map using the separation-logic
           condition; an alternative would be to have all lemmas play nice with
           locals in separation logic *)
        match goal with H : sep _ _ (map.remove _ ?i_var)
                        |- context [map.get _ ?i_var = Some ?wi] =>
                        eapply Var_put_remove with (v:=wi) in H;
                          eapply sep_assoc in H
        end.
        literal_locals_from_sep.

        repeat safe_compile_step.
        cbv zeta.

        match goal with
        | |- context [dlet (ladderstep_gallina _ (?x1, ?z1) (?x2, ?z2))] =>
          replace x1 with (x1 mod M) by swap_mod;
          replace z1 with (z1 mod M) by swap_mod;
          replace x2 with (x2 mod M) by swap_mod;
          replace z2 with (z2 mod M) by swap_mod
        end.

        compile_step.
        (* first, resolve evars *)
        all:lazymatch goal with
            | |- eval _ mod _ = _ =>
              solve [eauto using eval_fst_cswap, eval_snd_cswap]
            | _ => idtac
            end.
        (* *after* evar resolution *)
        all:lazymatch goal with
            | |- sep _ _ _ =>
              repeat seprewrite (cswap_iff1 Bignum);
                ecancel_assumption
            | |- context [WeakestPrecondition.cmd] => idtac
            | _ => solve_field_subgoals_with_cswap
            end.

        repeat safe_compile_step.

        (* TODO: use nlet to do this rename automatically *)
        let locals := lazymatch goal with
                      | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
        let b := lazymatch goal with x := xorb ?b _ |- _ => b end in
        let swap_var := lazymatch locals with
                          context [map.put _ ?x (word.of_Z (Z.b2z b))] => x end in
        eapply compile_rename_bool with (var := swap_var);
          [ solve [repeat compile_step] .. | ].
        intro.

        (* unset loop-local variables *)
        repeat remove_unused_var.

        compile_done.
        { (* prove locals postcondition *)
          autorewrite with mapsimpl.
          ssplit; [ | reflexivity ].
          subst_lets_in_goal. reflexivity. }
        { (* prove loop invariant held *)
          cbv [downto_inv downto_ghost_step].
          cbv [LadderStepResult] in *.
          cleanup; sepsimpl_hyps.
          repeat match goal with
                 | H : ?x = (_, _) |- context [fst ?x] =>
                   rewrite H; progress cbn [fst snd]
                 end.
          clear_old_seps.
          lift_eexists. sepsimpl.
          (* first, resolve evars *)
          all:lazymatch goal with
              | |- @sep _ _ Semantics.mem _ _ _ =>
                change Placeholder with Bignum; ecancel_assumption
              | |- @sep _ _ Semantics.locals _ _ ?locals =>
                subst_lets_in_goal; push_map_remove;
                  let locals := match goal with |- ?P ?l => l end in
                  sep_from_literal_locals locals;
                    ecancel_assumption
              | _ => idtac
              end.
          (* now solve other subgoals *)
          all:subst_lets_in_goal;
              rewrite ?Z.mod_mod by apply M_nonzero; eauto.
          match goal with
          | H : if ?gst then _ else _ |-
            if xorb ?gst ?x then _ else _ =>
            destr gst; cleanup; subst;
              cbn [xorb]; destr x
          end.
          all:cbn [cswap fst snd]; ssplit; reflexivity. } }
      { (* loop done; rest of function *)
        intros. destruct_products.
        cbv [downto_inv downto_inv] in *.
        sepsimpl_hyps.

        (* convert locals back to literal map using the separation-logic
           condition; an alternative would be to have all lemmas play nice with
           locals in separation logic *)
        match goal with H : sep _ _ (map.remove _ ?i_var),
                            Hget : map.get _ ?i_var = Some ?wi |- _ =>
                        eapply Var_put_remove with (v:=wi) in H;
                          eapply sep_assoc in H;
                          rewrite map.put_noop in H by assumption
        end.
        literal_locals_from_sep.

        repeat safe_compile_step.
        cbv match zeta.

        (* pull the eval out of all the swaps so field lemmas work *)
        repeat match goal with
               | H1 : ?y mod ?M = ?y, H2 : eval ?x mod M = ?y mod M |- _ =>
                 rewrite <-H2 in H1
               | _ => erewrite <-eval_fst_cswap_small by eauto
               | x := cswap _ _ _ |- _ => subst x
               end.

        safe_field_compile_step.
        repeat safe_compile_step.

        (* the output of this last operation needs to be stored in the pointer
           for the output, so we guide the automation to the right pointer *)
        clear_old_seps. change Placeholder with Bignum in *.
        lazymatch goal with
        | H : context [Bignum ?p U] |- _ =>
          change (Bignum p) with (Placeholder p) in H
        end.

        safe_field_compile_step.
        repeat safe_compile_step.
        compile_done. cbv [MontLadderResult].
        (* destruct the hypothesis identifying the new pointers as some swapping
           of the original ones *)
        destruct_one_match_hyp_of_type bool.
        all:cleanup; subst.
        all:lift_eexists.
        all:sepsimpl; [ reflexivity | ].
        all:ecancel_assumption. }
    Qed.
  End MontLadder.
End __.

(*
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Coercion expr.var : string >-> Syntax.expr.
Local Open Scope bedrock_expr.
Print montladder_body.
*)
(* fun (field_parameters : FieldParameters)
 *   (scalar_field_parameters : ScalarFieldParameters)
 *   (zbound : Z) =>
 * (cmd.call [] bignum_literal [(uintptr_t)1ULL; "X1"];;
 *  cmd.call [] bignum_literal [(uintptr_t)0ULL; "Z1"];;
 *  cmd.call [] bignum_copy ["U"; "X2"];;
 *  cmd.call [] bignum_literal [(uintptr_t)1ULL; "Z2"];;
 *  "v6" = (uintptr_t)0ULL;;
 *  "v7" = (uintptr_t)zboundULL;;
 *  (while ((uintptr_t)0ULL < "v7") {{
 *     "v7" = "v7" - (uintptr_t)1ULL;;
 *     cmd.call ["v8"] sctestbit ["K"; "v7"];;
 *     "v9" = "v6" .^ "v8";;
 *     (if ("v9") {{
 *        (("tmp" = "X1";;
 *          "X1" = "X2");;
 *         "X2" = "tmp");;
 *        cmd.unset "tmp"
 *      }});;
 *     (if ("v9") {{
 *        (("tmp" = "Z1";;
 *          "Z1" = "Z2");;
 *         "Z2" = "tmp");;
 *        cmd.unset "tmp"
 *      }});;
 *     cmd.call [] "ladderstep"
 *       ["U"; "X1"; "Z1"; "X2"; "Z2"; "A"; "AA"; "B"; "BB"; "E"; "C"; "D";
 *       "DA"; "CB"];;
 *     "v6" = "v8";;
 *     cmd.unset "v9";;
 *     cmd.unset "v8";;
 *     /*skip*/
 *   }});;
 *  (if ("v6") {{
 *     (("tmp" = "X1";;
 *       "X1" = "X2");;
 *      "X2" = "tmp");;
 *     cmd.unset "tmp"
 *   }});;
 *  (if ("v6") {{
 *     (("tmp" = "Z1";;
 *       "Z1" = "Z2");;
 *      "Z2" = "tmp");;
 *     cmd.unset "tmp"
 *   }});;
 *  cmd.call [] inv ["Z1"; "A"];;
 *  cmd.call [] mul ["X1"; "A"; "U"];;
 *  /*skip*/)%bedrock_cmd
 *      : FieldParameters -> ScalarFieldParameters -> Z -> cmd
 *)
