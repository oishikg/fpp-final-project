(* week-15_a-commutative-diagram.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Spelled-out version of Sun 26 Nov 2017 *)
(* was: *)
(* Version of Sat 25 Nov 2017 *)

(* ********** *)

(*
   name: Oishik Ganguly
   student ID number: A0138306J
   e-mail address: oishik.ganguly@u.yale-nus.edu.sg
*)

(* ********** *)
(*

The goal of this term project is to prove the following theorem:

  Theorem the_commutative_diagram :
    forall sp : source_program,
      interpret sp = run (compile sp).

for

* a source language of arithmetic expressions:

    Inductive arithmetic_expression : Type :=
    | Literal : nat -> arithmetic_expression
    | Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
    | Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.
    
    Inductive source_program : Type :=
    | Source_program : arithmetic_expression -> source_program.

* a target language of byte-code instructions:

    Inductive byte_code_instruction : Type :=
    | PUSH : nat -> byte_code_instruction
    | ADD : byte_code_instruction
    | SUB : byte_code_instruction.
    
    Inductive target_program : Type :=
    | Target_program : list byte_code_instruction -> target_program.

* a semantics of expressible values:

    Inductive expressible_value : Type :=
    | Expressible_nat : nat -> expressible_value
    | Expressible_msg : string -> expressible_value.

The source for errors is subtraction,
since subtracting two natural numbers does not always yield a natural number:
for example, 3 - 2 is defined but not 2 - 3.

You are expected, at the very least:

* to implement a source interpreter
  and to verify that it satisfies its specification

* to implement a target interpreter (i.e., a virtual machine)
  and to verify that it satisfies its specification

* to implement a compiler
  and to verify that it satisfies its specification

* to prove that the diagram commutes, i.e., to show that
  interpreting any given expression
  gives the same result as
  compiling this expression and then running the resulting compiled program
  (to this end, the injection tactic illustrated in Lemma new_and_useful just below will come handy)

Beyond this absolute minimum, in decreasing importance, it would be good:

* to write an accumulator-based compiler and to prove that it satisfies the specification

* to investigate byte-code verification

* to revisit good old Magritte

* to write a continuation-based interpreter and to prove that it satisfies the specification

* to prove that each of the specifications specifies a unique function

*)

(* ********** *)

Lemma new_and_useful :
  forall i j : nat,
    Some i = Some j -> i = j.
Proof. 
  intros i j H_Some.
  injection H_Some as H_i_j.  (* <--[new and useful]-- *)
  exact H_i_j.
Qed.

(* ********** *)

Ltac unfold_tactic name :=
  intros;
  unfold name; (* fold name; *)
  reflexivity.
  
Require Import Arith Bool List String.

(* n2 > n1 ? *)
Fixpoint ltb (n1 n2 : nat) : bool :=
  match n1 with
  | O =>
    match n2 with
    | O =>
      false
    | S n2' =>
      true
    end
  | S n1' =>
    match n2 with
    | O =>
      false
    | S n2' =>
      ltb n1' n2'
    end
  end.

    
           





Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).



(* ********** *)

(* Arithmetic expressions: *)

Inductive arithmetic_expression : Type :=
| Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Source programs: *)

Inductive source_program : Type :=
| Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Semantics: *)

Inductive expressible_value : Type :=
| Expressible_msg : string -> expressible_value
| Expressible_nat : nat -> expressible_value.


(* ********** *)

(* Task 1: 
   prove that each of the definitions below specifies a unique function,
   implement these two functions,
   and verify that each of your functions satisfies its specification.
 *)

(* We first define a notion of equality for expressible values *)

Definition expressible_val_eq (e1 : expressible_value) (e2 : expressible_value) :=
  match e1 with
  | Expressible_nat n1 =>
    match e2 with
    | Expressible_nat n2 =>
      n1 =n= n2
    | _ =>
      false
    end
  | Expressible_msg _ =>
    match e2 with
    | Expressible_msg _ =>
      true
    | _ =>
      false
    end
  end.

Notation "A =e= B" := (expressible_val_eq A B) (at level 70, right associativity).


Definition specification_of_evaluate (evaluate : arithmetic_expression -> expressible_value) :=
  (forall n : nat,
      (* specification for literals *)
     evaluate (Literal n) = Expressible_nat n)
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 -> 
       evaluate (Plus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       evaluate (Plus ae1 ae2) = Expressible_nat (n1 + n2)))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       ltb n1 n2 = true ->
       evaluate (Minus ae1 ae2) = Expressible_msg "numerical underflow")
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       ltb n1 n2 = false ->
       evaluate (Minus ae1 ae2) = Expressible_nat (n1 - n2))).


(* Proving that specification_of_evaluate is sound *)
Theorem specification_of_evaluate_is_sound :
  forall (ev1 ev2 : arithmetic_expression -> expressible_value),
    specification_of_evaluate ev1 ->
    specification_of_evaluate ev2 ->
    forall (ae : arithmetic_expression),
      ev1 ae = ev2 ae.
Proof.
  intros ev1 ev2.
  unfold specification_of_evaluate.
  intros
    [ev1_lit [[ev1_add_err_arg1 [ev1_add_err_arg2 ev1_add_eval]]
                [ev1_sub_err_arg1 [ev1_sub_err_arg2 [ev1_sub_err_ufl ev1_sub_eval]]]]]
    [ev2_lit [[ev2_add_err_arg1 [ev2_add_err_arg2 ev2_add_eval]]
                [ev2_sub_err_arg1 [ev2_sub_err_arg2 [ev2_sub_err_ufl ev2_sub_eval]]]]].
  intro ae.
  (* our proof will proceed by structural induction over arithmetic expressions *)
  induction ae as [ n' | e1 IH_e1 e2 IH_e2 | e1 IH_e1 e2 IH_e2].

  (* proof for literals *)
  rewrite -> (ev1_lit n').
  rewrite -> (ev2_lit n').
  reflexivity.

  (* proof for addition expressions *)
  (* we consider all possible evaluations of the subexpression e1 and e2 *)
  (* case 1: e1 evaluates to a string *)
  case (ev2 e1) as [str_val_e1 | nat_val_e1] eqn : e1_eval_case.
  rewrite -> (ev1_add_err_arg1 e1 e2 str_val_e1 IH_e1).
  rewrite -> (ev2_add_err_arg1 e1 e2 str_val_e1 e1_eval_case).
  reflexivity.
  (* case 2: e1 is a natural value, and e2 evaluates to a string *)
  case (ev2 e2) as [str_val_e2 | nat_val_e2] eqn : e2_eval_case.
  rewrite -> (ev1_add_err_arg2 e1 e2 nat_val_e1 str_val_e2 IH_e1 IH_e2).
  rewrite -> (ev2_add_err_arg2 e1 e2 nat_val_e1 str_val_e2 e1_eval_case e2_eval_case).
  reflexivity.
  (* case 3: both e1, e2 evaluate to natural values *)
  rewrite -> (ev1_add_eval e1 e2 nat_val_e1 nat_val_e2 IH_e1 IH_e2).
  rewrite -> (ev2_add_eval e1 e2 nat_val_e1 nat_val_e2 e1_eval_case e2_eval_case).
  reflexivity.

  (* proof for subtraction expressions; once again, consider all possible evaluated
   * cases of the expression e1 and e2 *)
  (* case 1: e1 evaluates to a string *)
  case (ev2 e1) as [str_val_e1 | nat_val_e1] eqn : e1_eval_case.
  rewrite -> (ev1_sub_err_arg1 e1 e2 str_val_e1 IH_e1).
  rewrite -> (ev2_sub_err_arg1 e1 e2 str_val_e1 e1_eval_case).
  reflexivity.
  (* case 2: e1 is a natural value, and e2 evaluates to a string *)
  case (ev2 e2) as [str_val_e2 | nat_val_e2] eqn : e2_eval_case.
  rewrite -> (ev1_sub_err_arg2 e1 e2 nat_val_e1 str_val_e2 IH_e1 IH_e2).
  rewrite -> (ev2_sub_err_arg2 e1 e2 nat_val_e1 str_val_e2 e1_eval_case e2_eval_case).
  reflexivity.
  (* case 3: both e1 and e2 are natural values, but n1 < n2 *)
  case (ltb nat_val_e1 nat_val_e2) eqn : ltb_bool_val.
  rewrite -> (ev1_sub_err_ufl e1 e2 nat_val_e1 nat_val_e2 IH_e1 IH_e2 ltb_bool_val).
  rewrite -> (ev2_sub_err_ufl e1 e2 nat_val_e1 nat_val_e2 e1_eval_case e2_eval_case
                              ltb_bool_val).
  reflexivity.
  (* case 4: both e1 and e2 and natural values, and n1 > n2 *)
  rewrite -> (ev1_sub_eval e1 e2 nat_val_e1 nat_val_e2 IH_e1 IH_e2).
  rewrite -> (ev2_sub_eval e1 e2 nat_val_e1 nat_val_e2 e1_eval_case e2_eval_case).
  reflexivity.
  exact ltb_bool_val.
  exact ltb_bool_val.
Qed.

(* Implement unit tests for evaluators *)
Definition unit_test_for_evaluate
           (evaluate : arithmetic_expression -> expressible_value) : bool :=
  (evaluate
     (Plus (Literal 2)
           (Literal 3)) =e= Expressible_nat 5)
    &&
    (evaluate
       (Minus (Literal 7)
              (Plus (Literal 5)
                    (Minus (Literal 5) (Literal 4))
              )
       ) =e= Expressible_nat 1)
    &&
    (evaluate
       ( Plus (Literal 5)
              (Plus (Literal 6)
                    (Minus (Literal 4) (Literal 6))
              )
       ) =e= Expressible_msg "numerical underflow")
    &&
    (evaluate
        ( Minus (Literal 21)
                (Plus (Literal 4)
                      (Minus
                         (Plus (Literal 14)
                               (Literal 1)
                         )
                         (Literal 10)
                      )
                )
        ) =e= Expressible_nat 12)
    &&
    (evaluate
       (Plus
          (Plus (Literal 3)
                (Minus (Literal 6)
                       (Literal 7)
                )
          )
          (Literal 3)
       ) =e= Expressible_msg "numerical underflow").
       

(* Naive recursive implementation of evaluate *)
Fixpoint evaluate_v0 (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
    Expressible_nat n
  | Plus e1 e2 =>
    (* evaluate the first expression *)
    match (evaluate_v0 e1) with
    | Expressible_msg s =>
      Expressible_msg s
    (* If the first expression is a natural value, evaluate the second expression **)
    | Expressible_nat n1 =>
      match (evaluate_v0 e2) with
      | Expressible_msg s =>
        Expressible_msg s
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      end
    end
  | Minus e1 e2 =>
    match (evaluate_v0 e1) with
    | Expressible_msg s =>
      Expressible_msg s
    | Expressible_nat n1 =>
      match (evaluate_v0 e2) with
      | Expressible_msg s =>
        Expressible_msg s
      | Expressible_nat n2 =>
        (* now check whether n1 < n2 *)
        if (ltb n1 n2)
        then Expressible_msg "numerical underflow"
        else Expressible_nat (n1 - n2)
      end
    end
  end.

(* Unit test *)
Compute (unit_test_for_evaluate (evaluate_v0)).

(* Standard unfold lemmas *)
Lemma unfold_evaluate_v0_literal :
  forall (n : nat),
    evaluate_v0 (Literal n) = Expressible_nat n.
Proof.
  unfold_tactic evaluate_v0.
Qed.    


Lemma unfold_evaluate_v0_plus : 
  forall (e1 e2 : arithmetic_expression),
    evaluate_v0 (Plus e1 e2) =
    (match (evaluate_v0 e1) with
    | Expressible_msg s =>
      Expressible_msg s
    | Expressible_nat n1 =>
      match (evaluate_v0 e2) with
      | Expressible_msg s =>
        Expressible_msg s
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      end
    end).
Proof.
  unfold_tactic evaluate_v0.
Qed.    

Lemma unfold_evaluate_v0_minus :
  forall (e1 e2 : arithmetic_expression),
    evaluate_v0 (Minus e1 e2) =
    (match (evaluate_v0 e1) with
    | Expressible_msg s =>
      Expressible_msg s
    | Expressible_nat n1 =>
      match (evaluate_v0 e2) with
      | Expressible_msg s =>
        Expressible_msg s
      | Expressible_nat n2 =>
        (* now check whether n1 < n2 *)
        if (ltb n1 n2)
        then Expressible_msg "numerical underflow"
        else Expressible_nat (n1 - n2)
      end
     end).
Proof.
  unfold_tactic evaluate_v0.
Qed.


    
(* Proving that evaluate_v0 meets the specification_of_evaluate, thereby proving
 * that specification_of_evaluate is complete *)
Theorem evaluate_v0_meets_the_specification_of_evaluate :
  specification_of_evaluate evaluate_v0.
Proof.
  unfold specification_of_evaluate.

  (* literal *)
  split.
  intro n.
  exact (unfold_evaluate_v0_literal n).

  (* Plus : error on arg 1 *)
  split.
  split.
  intros ae1 ae2 s1 H_about_ae1.
  (* use any value to instantiate the natural values in the unfold lemma *)
  rewrite -> (unfold_evaluate_v0_plus ae1 ae2).
  rewrite -> H_about_ae1.
  reflexivity.
  
  (* Plus : error on arg 2 *)
  split.
  intros ae1 ae2 n1 s2 H_about_ae1 H_about_ae2.
  rewrite -> (unfold_evaluate_v0_plus ae1 ae2).
  rewrite -> H_about_ae1 ; rewrite -> H_about_ae2.
  reflexivity.

  (* Plus : both args evaluate to expressible nats *)
  intros ae1 ae2 n1 n2 H_about_ae1 H_about_ae2.
  rewrite -> (unfold_evaluate_v0_plus ae1 ae2).
  rewrite -> H_about_ae1 ; rewrite -> H_about_ae2.
  reflexivity.

  (* Minus : error on arg 1 *)
  split.
  intros ae1 ae2 s1 H_about_ae1.
  (* use any value to instantiate the natural values in the unfold lemma *)
  rewrite -> (unfold_evaluate_v0_minus ae1 ae2).
  rewrite -> H_about_ae1.
  reflexivity.

  (* Minus : error on arg 2 *)
  split.
  intros ae1 ae2 n1 s2 H_about_ae1 H_about_ae2.
  rewrite -> (unfold_evaluate_v0_minus ae1 ae2).
  rewrite -> H_about_ae1 ; rewrite -> H_about_ae2.
  reflexivity.

  (* Minus : both args are expressible nats, but n1 < n2 (underflow *)
  split.
  (* note : we name the variables m1 and m2 to avoid clashed with the names in 
   * the unfold lemma. Coq automatically modifies the variable names, but we 
   * would rather be in control *)
  intros ae1 ae2 m1 m2 H_about_ae1 H_about_ae2 H_about_n1_and_n2.
  rewrite -> (unfold_evaluate_v0_minus ae1 ae2).
  rewrite -> H_about_ae1 ; rewrite -> H_about_ae2;
    rewrite -> H_about_n1_and_n2.
  reflexivity.

  (* Minus : both args are expressible nats, and there is no underflow *)
  intros ae1 ae2 n1 n2 H_about_ae1 H_about_ae2 H_about_n1_and_n2.
  rewrite -> (unfold_evaluate_v0_minus ae1 ae2).
  rewrite -> H_about_ae1 ; rewrite -> H_about_ae2 ;
    rewrite -> H_about_n1_and_n2.
  reflexivity.
Qed.


(* We have thus shown that the specification_of_evaluate is sound and complete, and
 * also defined a function that evaluates a given arithmetic_expression *)

Definition specification_of_interpret (interpret : source_program -> expressible_value) :=
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      interpret (Source_program ae) = evaluate ae.

(* Theorem to prove soundness of the specification_of_interpret *)
Theorem specification_of_interpret_is_sound :
  forall (i1 i2 : source_program -> expressible_value),
    specification_of_interpret i1 ->
    specification_of_interpret i2 ->
    forall (ae : arithmetic_expression),
      i1 (Source_program ae) = i2 (Source_program ae).
Proof.
  intros i1 i2.
  unfold specification_of_interpret.
  intros H1 H2 ae.
  (* since evaluate_v0 is a function of type of arithmetic_expression ->
   * expressible_value, and it meets the specification_of_evaluate, 
   * we may use it to instantiate the evaluate variable in the hypotheses *)
  rewrite -> (H1 evaluate_v0 evaluate_v0_meets_the_specification_of_evaluate ae).
  rewrite -> (H2 evaluate_v0 evaluate_v0_meets_the_specification_of_evaluate ae).
  reflexivity.
Qed.

(* implementation of interpret *)
Definition interpret_v0 (sp : source_program ) : expressible_value :=
  match sp with
  | Source_program ae =>
    evaluate_v0 ae
  end.

(* interpret_v0 meets the specification of interpret *)
Theorem interpret_v0_meets_the_specification_of_interpret :
  specification_of_interpret interpret_v0.
Proof.
  unfold specification_of_interpret.
  intros evaluate_var H_about_evaluate_var.
  intro ae.
  unfold interpret_v0.
  rewrite ->
          (specification_of_evaluate_is_sound
          evaluate_var
          evaluate_v0
          H_about_evaluate_var
          evaluate_v0_meets_the_specification_of_evaluate
          ae).
  reflexivity.
Qed.

(* ********** *)

(* Task 2 (if there is time):
   Define an interpreter with a function in continuation-passing style
   that satisfies the specification above,
   and that only apply the current continuation to the result of evaluating
   an expression if evaluating this expression did not yield an error.
*)

(* ********** *)

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
| PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

(* Target programs: *)

Inductive target_program : Type :=
| Target_program : list byte_code_instruction -> target_program.

(* Data stack: *)

Definition data_stack := list nat.

(* ********** *)

Inductive result_of_decoding_and_execution : Type :=
| OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

Definition specification_of_decode_execute (decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  (* pushing natural value onto the data stack (or the operation stack) *)
  (forall (n : nat)
          (ds : data_stack),
     decode_execute (PUSH n) ds = OK (n :: ds))
  /\
  (* pushing an ADD instruction onto the stack; only if the stack has at least two 
   * natural values can the addition be performed *)
  ((decode_execute ADD nil = KO "ADD: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute ADD (n2 :: nil) = KO "ADD: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       decode_execute ADD (n2 :: n1 :: ds) = OK ((n1 + n2) :: ds)))
  /\
  (* likewise for the SUB instruction *)
  ((decode_execute SUB nil = KO "SUB: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute SUB (n2 :: nil) = KO "SUB: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       ltb n1 n2 = true ->
       decode_execute SUB (n2 :: n1 :: ds) = KO "numerical underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       ltb n1 n2 = false ->
       decode_execute SUB (n2 :: n1 :: ds) = OK ((n1 - n2) :: ds))).

(* Task 3:
   prove that the definition above specifies a unique function,
   implement this function,
   and verify that your function satisfies the specification.
 *)

(* proving that specification_of_decode_execute is sound *)
Theorem specification_of_decode_execute_is_sound :
  forall (de1 de2 : byte_code_instruction -> data_stack ->
                    result_of_decoding_and_execution),
    specification_of_decode_execute de1 ->
    specification_of_decode_execute de2 ->
    forall (bcis : byte_code_instruction) (ds :data_stack),
      de1 bcis ds = de2 bcis ds.
Proof.
  intros de1 de2.
  unfold specification_of_decode_execute.
  intros [de1_push [[de1_add_err1 [de1_add_err2 de1_add_eval]]
                      [de1_sub_err1 [de1_sub_err2 [de1_sub_err_ufl de1_sub_eval]]]]]
         [de2_push [[de2_add_err1 [de2_add_err2 de2_add_eval]]
                      [de2_sub_err1 [de2_sub_err2 [de2_sub_err_ufl de2_sub_eval]]]]].
  intros bcis ds.

  (* we now consider all possible bcis on a case by case basis *)
  case bcis as [ n'| | ].

  (* PUSH *)
  rewrite -> (de1_push n' ds); rewrite -> (de2_push n' ds); reflexivity.

  (* ADD *)
  (* now consider different cases of ds *)
  case ds as [ | n' ds'].
  
  (* case 1: ds is NIL, stack underflow *)
  rewrite -> de1_add_err1 ; rewrite -> de2_add_err1; reflexivity.

  (* case 2: ds is of the form n'::ds' ; we now consider two case for ds'; 
   * when ds' is NIL, we still have a stack underflow *)
  case ds' as [ |n'' ds''].
  rewrite -> (de1_add_err2 n'); rewrite -> (de2_add_err2 n'); reflexivity.

  (* case 3 : ds is of the form n' :: (n'' :: ds'') *)
  rewrite -> (de1_add_eval n'' n' ds''); rewrite -> (de2_add_eval n'' n' ds'');
    reflexivity.

  (* SUB *)
  (* now consider different cases of ds *)
  case ds as [ | n' ds'].
  
  (* case 1: ds is NIL, stack underflow *)
  rewrite -> de1_sub_err1 ; rewrite -> de2_sub_err1; reflexivity.

  (* case 2: ds is of the form n'::ds' ; we now consider two case for ds'; 
   * when ds' is NIL, we still have a stack underflow *)
  case ds' as [ |n'' ds''].
  rewrite -> (de1_sub_err2 n'); rewrite -> (de2_sub_err2 n'); reflexivity.

  (* case 3: ds is of the form n'::n''::ds'' ; now we consider cases of numerical
   * underflow *)
  case (ltb n'' n') as [ | ] eqn : val_of_ltb_n''_n'.
  rewrite -> (de1_sub_err_ufl n'' n' ds'' val_of_ltb_n''_n');
    rewrite -> (de2_sub_err_ufl n'' n' ds'' val_of_ltb_n''_n');
    reflexivity.

  (* case 4: no numerical underflow *)
  rewrite -> (de1_sub_eval n'' n' ds'' val_of_ltb_n''_n');
    rewrite -> (de2_sub_eval n'' n' ds'' val_of_ltb_n''_n');
    reflexivity.
Qed.
  


Definition decode_execute (bcis : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | PUSH n =>
  OK (n::ds) 
  | ADD =>
    match ds with
    | nil =>
      KO "ADD: stack underflow"
    | n':: nil =>
      KO "ADD: stack underflow"
    | n2 :: n1 :: ds'' =>
      OK ( (n1 + n2) :: ds'' )
    end
  |SUB =>
    match ds with
    | nil =>
      KO "SUB: stack underflow"
    | n':: nil =>
      KO "SUB: stack underflow"
    | n2 :: n1 :: ds'' =>
      if (ltb n1 n2)
      then KO "numerical underflow"
      else OK ( (n1 - n2) :: ds'' )
    end
  end.

(* the implementtation of decode_execute satisfies the specification 8*)
Theorem decode_execute_satisfies_the_specification_of_decode_execute :
  specification_of_decode_execute decode_execute.
Proof.
  unfold specification_of_decode_execute.

  (* PUSH *)
  split.
  intros n ds.
  unfold decode_execute.
  reflexivity.

  (* ADD *)
  split.
  split.
  unfold decode_execute.
  reflexivity.

  split.
  intro n2.
  unfold decode_execute.
  reflexivity.

  intros n1 n2 ds.
  unfold decode_execute.
  reflexivity.

  (* SUB *)
  split.
  unfold decode_execute.
  reflexivity.

  split.
  intro n2.
  unfold decode_execute.
  reflexivity.

  (* killing two birds with one do *)
  do 2 (split;
  intros n1 n2 ds H_about_n1_and_n2;
  unfold decode_execute;
  rewrite -> H_about_n1_and_n2;
  reflexivity).
Qed.


(* ********** *)

(* Specification of the virtual machine: *)

Definition specification_of_fetch_decode_execute_loop (fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  forall decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_decode_execute decode_execute ->
    (forall ds : data_stack,
        fetch_decode_execute_loop nil ds = OK ds)
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds ds' : data_stack),
        decode_execute bci ds = OK ds' ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        fetch_decode_execute_loop bcis' ds')
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds : data_stack)
            (s : string),
        decode_execute bci ds = KO s ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        KO s).

(* Task 4:
   prove that the definition above specifies a unique function,
   implement this function,
   and verify that your function satisfies the specification.
 *)

(* specification_of_fetch_decode_execute_loop is sound *)
Theorem specification_of_fetch_decode_execute_loop_is_sound :
  forall (fdel1 fdel2 : list byte_code_instruction -> data_stack ->
                        result_of_decoding_and_execution),
    specification_of_fetch_decode_execute_loop fdel1 ->
    specification_of_fetch_decode_execute_loop fdel2 ->
    forall (bcis : list byte_code_instruction)
           (ds : data_stack),
      fdel1 bcis ds = fdel2 bcis ds.
Proof.
  intros fdel1 fdel2.
  unfold specification_of_fetch_decode_execute_loop.
  (* to obtain the hypotheses for the conjunctive branches of the specificaiton,
   * we must use destruct *)
  intros H1 H2.
  destruct  (H1 decode_execute
            decode_execute_satisfies_the_specification_of_decode_execute) as
      [fdel1_completion [fdel1_execution fdel1_error]].
  destruct  (H2 decode_execute
                decode_execute_satisfies_the_specification_of_decode_execute) as
      [fdel2_completion [fdel2_execution fdel2_error]].
  (* don't introduce ds, we will use this parameterize our induction proof *)
  intros bcis.
  (* induct over the list of byte code instructions *)
  induction bcis as [ | i' i's IH_i'].
  
  (* case 1: the bci list is empty *)
  intro ds.
  rewrite -> (fdel1_completion ds).
  rewrite -> (fdel2_completion ds).
  reflexivity.

  (* case 2: the bci list is of the form bci'::bcis';  we must now consider 
   * the evaluation of the bci at the head of the list ; first condier the
   * situation where it evaluates to OK (ds) *)
  intro ds.
  case (decode_execute i' ds) as [new_ds | error_string]
                                   eqn : decode_execute_value_for_i'.
  rewrite -> (fdel1_execution i' i's ds new_ds decode_execute_value_for_i').
  rewrite -> (fdel2_execution i' i's ds new_ds decode_execute_value_for_i').
  rewrite -> (IH_i' new_ds).
  reflexivity.

  (* case 3: the bci' evaluates to KO (s) *)
  rewrite -> (fdel1_error i' i's ds error_string decode_execute_value_for_i').
  rewrite -> (fdel2_error i' i's ds error_string decode_execute_value_for_i').
  reflexivity.
Qed.


(* implementation of the specification_of_fetch_decode_execute_loop *)
Fixpoint fetch_decode_execute_loop
         (insts : list byte_code_instruction)
         (ds : data_stack) : result_of_decoding_and_execution :=
  match insts with
  | nil =>
    OK ds
  | inst :: inst' =>
    match (decode_execute inst ds) with
    | OK new_ds =>
      fetch_decode_execute_loop inst' new_ds
    | KO s =>
      KO s
    end
  end.

(* Standard unfold lemmas *)
Lemma unfold_fetch_decode_execute_loop_nil :
  forall (ds : data_stack),
    fetch_decode_execute_loop nil ds = OK ds.
Proof.
  unfold_tactic fetch_decode_execute_loop.
Qed.

Lemma unfold_fetch_decode_execute_loop_bcis : 
  forall (inst : byte_code_instruction)
         (inst' : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop (inst :: inst') ds =
    match (decode_execute inst ds) with
    | OK new_ds =>
      fetch_decode_execute_loop inst' new_ds
    | KO s =>
      KO s
     end.
Proof.
  unfold_tactic fetch_decode_execute_loop.
Qed.

(* Now we prove that the implementation of fetch_decode_execute_loop satifies the 
 * specification *)
Theorem fetch_decode_execute_loop_satisfies_the_specification :
  specification_of_fetch_decode_execute_loop fetch_decode_execute_loop.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  intros decode_execute_var H_about_decode_execute_var.
  
  (* nil case *)
  split.
  intro ds.
  exact (unfold_fetch_decode_execute_loop_nil ds).

  (* cons case with continued execution *)
  split.
  intros bci bcis' ds ds' H_about_decode_execute_bci.
  rewrite -> (unfold_fetch_decode_execute_loop_bcis
                bci bcis' ds).
  (* use the soundness of the specification_of_decode_execute to replace 
   * decode_execute_var with decode_execute *)
  rewrite ->
          (specification_of_decode_execute_is_sound
             decode_execute_var
             decode_execute
             H_about_decode_execute_var
             decode_execute_satisfies_the_specification_of_decode_execute
             bci ds) in H_about_decode_execute_bci.
  rewrite -> H_about_decode_execute_bci.
  reflexivity.

  (* cons case with error *)
  intros bci bcis' ds s H_about_decode_execute_bci.
  rewrite ->
          (specification_of_decode_execute_is_sound
             decode_execute_var
             decode_execute
             H_about_decode_execute_var
             decode_execute_satisfies_the_specification_of_decode_execute
             bci ds) in H_about_decode_execute_bci.
  (* note: we will not be needing the new_ds variable; thus we may pass any 
   * value of the type list nat. *)
  rewrite -> (unfold_fetch_decode_execute_loop_bcis
                bci bcis' ds).
  rewrite -> H_about_decode_execute_bci.
reflexivity.  
Qed.

(* ********** *)

Lemma unfold_append_nil :
  forall bcis2 : list byte_code_instruction,
    nil ++ bcis2 = bcis2.
Proof.
  unfold_tactic List.app.
Qed.

Lemma unfold_append_cons :
  forall (bci1 : byte_code_instruction)
         (bci1s bci2s : list byte_code_instruction),
    (bci1 :: bci1s) ++ bci2s =
    bci1 :: (bci1s ++ bci2s).
Proof.
  unfold_tactic List.app.
Qed.

(* Task 5:
   Prove that for any lists of byte-code instructions bcis1 and bcis2,
   and for any data stack ds,
   executing the concatenation of bcis1 and bcis2 (i.e., bcis1 ++ bcis2) with ds
   gives the same result as
   (1) executing bcis1 with ds, and then
   (2) executing bcis2 with the resulting data stack, if there exists one.
*)


Theorem relation_between_execution_of_two_bcis_and_their_appended_version :
  forall (bci1s bci2s : list byte_code_instruction),
    (forall (ds : data_stack)
            (ds_new : data_stack),
        fetch_decode_execute_loop bci1s ds = OK ds_new ->
        fetch_decode_execute_loop (bci1s ++ bci2s) ds =
        fetch_decode_execute_loop (bci2s) ds_new) /\
    (forall (ds : data_stack) (s : string),
        fetch_decode_execute_loop bci1s ds = KO s ->
        fetch_decode_execute_loop (bci1s ++ bci2s) ds = KO s).
Proof.
  intros bci1s bci2s.

  (* consider the first conjunctive clause *)
  split.
  induction bci1s as [ | i' is' IH_is'].

  (* base case *)
  intros ds ds_new H_when_bcis_is_nil.
  rewrite -> unfold_append_nil.
  rewrite -> (unfold_fetch_decode_execute_loop_nil) in H_when_bcis_is_nil.
  injection H_when_bcis_is_nil as H_about_ds_and_ds_new.
  rewrite -> H_about_ds_and_ds_new.
  reflexivity.

  (* inductive case *)
  intros ds ds_new H_when_bcis_is_cons.
  rewrite -> unfold_append_cons.
  case (decode_execute i' ds) as [ ds_after_de_i' | s] eqn : value_of_de_i'.
  (* rewrite the goal for when (decode_execute i') = OK _ *)
  rewrite -> (unfold_fetch_decode_execute_loop_bcis i' (is' ++ bci2s) ds).
  rewrite -> value_of_de_i'.
  (* rewrite H_when_bcis_is_cons *)
  rewrite -> (unfold_fetch_decode_execute_loop_bcis i' is' ds) in H_when_bcis_is_cons.
  rewrite -> value_of_de_i' in H_when_bcis_is_cons.
  Check (IH_is' ds_after_de_i' ds_new).
  apply (IH_is' ds_after_de_i' ds_new) in H_when_bcis_is_cons.
  rewrite -> H_when_bcis_is_cons.
  reflexivity.

  (* now consider the case where (decode_execute i') = KO _; clearly this gives
   * rise to an absurd situation, so we use the discriminate tactic *)
  rewrite ->  (unfold_fetch_decode_execute_loop_bcis i' is' ds) 
                                                    in H_when_bcis_is_cons.
  rewrite -> value_of_de_i' in H_when_bcis_is_cons.
  discriminate.

  (* consider the second conjunctive clause *)
  induction bci1s as [ | i' is'  IH_is'].
  intros ds s H_about_bcis_nil.

  (* base case *)
  rewrite -> unfold_fetch_decode_execute_loop_nil in H_about_bcis_nil.
  discriminate.

  (* inductive case *)
  intros ds s H_about_bcis_cons.
  rewrite -> unfold_append_cons.
  (* once again, consider the cases of decode_execute i' *)
  case (decode_execute i' ds) as [ds_returned | error_msg] eqn : value_of_de_i'.

  (* case 1: decode_execute i' = OK _ *)
  (* modify H_about_bcis_cons *)
  rewrite -> (unfold_fetch_decode_execute_loop_bcis i' is' ds)
                                                    in H_about_bcis_cons.
  rewrite -> value_of_de_i' in H_about_bcis_cons.
  apply (IH_is' ds_returned s) in H_about_bcis_cons.
  rewrite <- H_about_bcis_cons.
  (* modify the goal *)
  rewrite ->
          (unfold_fetch_decode_execute_loop_bcis i' (is' ++ bci2s) ds).
  rewrite -> value_of_de_i'.
  reflexivity.

  (* case 2: decode_execute i' = KO _ *)
  (* modify H_about_bcis_cons *)
  rewrite -> (unfold_fetch_decode_execute_loop_bcis i' is' ds)
    in H_about_bcis_cons.
  rewrite -> value_of_de_i' in H_about_bcis_cons.
  (* modify the goal *)
  rewrite -> (unfold_fetch_decode_execute_loop_bcis i' (is' ++ bci2s) ds).
  rewrite -> value_of_de_i'.
  exact H_about_bcis_cons.
  (* note : since the loop stops executing the remaining instructions in bci1s as soon
   * as an error message is encountered, we did not need the induction hypothesis *)
Qed.  


(* ********** *)

Definition specification_of_run (run : target_program -> expressible_value) :=
  forall fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
    (forall (bcis : list byte_code_instruction),
       fetch_decode_execute_loop bcis nil = OK nil ->
       run (Target_program bcis) = Expressible_msg "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (n : nat),
       fetch_decode_execute_loop bcis nil = OK (n :: nil) ->
       run (Target_program bcis) = Expressible_nat n)
    /\
    (forall (bcis : list byte_code_instruction)
            (n n' : nat)
            (ds'' : data_stack),
       fetch_decode_execute_loop bcis nil = OK (n :: n' :: ds'') ->
       run (Target_program bcis) = Expressible_msg "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
       fetch_decode_execute_loop bcis nil = KO s ->
       run (Target_program bcis) = Expressible_msg s).

(* Task 6:
   prove that the definition above specifies a unique function,
   implement this function,
   and verify that your function satisfies the specification.
 *)

(* the specification_of_run is sound *)
Theorem specification_of_run_is_sound :
  forall (run1 run2 : target_program -> expressible_value),
    specification_of_run run1 ->
    specification_of_run run2 ->
    forall (bcis : list byte_code_instruction),
      run1 (Target_program bcis) = run2 (Target_program bcis).
Proof.
  intros run1 run2.
  unfold specification_of_run.
  intros H1 H2.
  destruct (H1 fetch_decode_execute_loop
               fetch_decode_execute_loop_satisfies_the_specification)
    as [ run1_no_result [run1_one_result [run1_too_many_results
                                             run1_error_message ]]].
  destruct (H2 fetch_decode_execute_loop
               fetch_decode_execute_loop_satisfies_the_specification)
    as [ run2_no_result [run2_one_result [run2_too_many_results
                                             run2_error_message ]]].
  intro bcis.
  (* now consider the multiple cases of applying the fetch_decode_execute_loop to
   * bcis and nil *)
  case (fetch_decode_execute_loop bcis nil) as [ return_ds | runtime_error_msg]
                                                 eqn : value_of_bcis_execution.
  (* for the case where a data stack is returned, consider the 3 cases of no results,
   * one result, and too many results *)
  case return_ds as [ | d1 [ | d2 ds']] eqn : value_of_return_ds.
  
  (* case 1: no result on stack *)
  rewrite -> (run1_no_result bcis value_of_bcis_execution);
    rewrite -> (run2_no_result bcis value_of_bcis_execution);
    reflexivity.

  (* case 2: one result on stack *)
  rewrite -> (run1_one_result bcis d1 value_of_bcis_execution);
    rewrite -> (run2_one_result bcis d1 value_of_bcis_execution);
    reflexivity.

  (* case 3 : too many results on stack *)
  rewrite -> (run1_too_many_results bcis d1 d2 ds' value_of_bcis_execution);
    rewrite -> (run2_too_many_results bcis d1 d2 ds' value_of_bcis_execution);
    reflexivity.

  (* case 4 : run time error *)
  rewrite -> (run1_error_message bcis runtime_error_msg value_of_bcis_execution);
  rewrite -> (run2_error_message bcis runtime_error_msg value_of_bcis_execution);
  reflexivity.
Qed.

(* Implementation of the specification_of_run *)

Definition run (prog : target_program) : expressible_value :=
  match prog with
  |Target_program bcis =>
   match (fetch_decode_execute_loop bcis nil) with
   | OK nil =>
     Expressible_msg "no result on the data stack"
   | OK (n :: nil) =>
     Expressible_nat n
   | OK (n :: n' :: ds) =>
     Expressible_msg "too many results on the data stack"
   | KO error_msg =>
     Expressible_msg error_msg
   end
  end.


(* proof that this implementation satisfies the given specification *)
Theorem run_satisfies_the_specification_of_run :
  specification_of_run run.
Proof.
  unfold specification_of_run.
  intros fetch_decode_execute_loop_var H_about_fetch_decode_execute_loop_var.
  
  split.
  intros bcis H_about_evaluation_of_bcis.
  (* we would like to replace fetch_decode_execute_loop_var with
   * fetch_decode_execute_loop, since run uses this function *)
  rewrite ->
          (specification_of_fetch_decode_execute_loop_is_sound
          fetch_decode_execute_loop_var
          fetch_decode_execute_loop
          H_about_fetch_decode_execute_loop_var
          fetch_decode_execute_loop_satisfies_the_specification
          bcis nil) in H_about_evaluation_of_bcis.
  unfold run.
  rewrite -> H_about_evaluation_of_bcis.
  reflexivity.

  (* the proofs for the remaining three cases is similar to the case above ; 
   * the only different is in the values that require to be introed *)
  split.
  intros bcis n H_about_evaluation_of_bcis.
  rewrite ->
          (specification_of_fetch_decode_execute_loop_is_sound
          fetch_decode_execute_loop_var
          fetch_decode_execute_loop
          H_about_fetch_decode_execute_loop_var
          fetch_decode_execute_loop_satisfies_the_specification
          bcis nil) in H_about_evaluation_of_bcis.
  unfold run.
  rewrite -> H_about_evaluation_of_bcis.
  reflexivity.

  split.
  intros bcis n n' ds'' H_about_evaluation_of_bcis.
  rewrite ->
          (specification_of_fetch_decode_execute_loop_is_sound
          fetch_decode_execute_loop_var
          fetch_decode_execute_loop
          H_about_fetch_decode_execute_loop_var
          fetch_decode_execute_loop_satisfies_the_specification
          bcis nil) in H_about_evaluation_of_bcis.
  unfold run.
  rewrite -> H_about_evaluation_of_bcis.
  reflexivity.

  intros bcis s H_about_evaluation_of_bcis.
  unfold run.
  rewrite ->
          (specification_of_fetch_decode_execute_loop_is_sound
          fetch_decode_execute_loop_var
          fetch_decode_execute_loop
          H_about_fetch_decode_execute_loop_var
          fetch_decode_execute_loop_satisfies_the_specification
          bcis nil) in H_about_evaluation_of_bcis.
  rewrite -> H_about_evaluation_of_bcis.
  reflexivity.
Qed.

(* ********** *)

Definition specification_of_compile_aux (compile_aux : arithmetic_expression -> list byte_code_instruction) :=
  (forall n : nat,
     compile_aux (Literal n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)).

(* Task 6:
   prove that the definition above specifies a unique function,
   implement this function using list concatenation, i.e., ++,
   and verify that your function satisfies the specification.
 *)

(* the specification_of_compile_aux is sound *)
Theorem specification_of_compile_aux_is_sound :
  forall (compile_aux_1 compile_aux_2 : arithmetic_expression ->
                                        list byte_code_instruction),
    specification_of_compile_aux compile_aux_1 ->
    specification_of_compile_aux compile_aux_2 ->
    forall (ae : arithmetic_expression),
      compile_aux_1 ae = compile_aux_2 ae.
Proof.
  intros compile_aux_1 compile_aux_2.
  unfold specification_of_compile_aux.
  intros [compile_aux_1_push [compile_aux_1_add compile_aux_1_sub]]
         [compile_aux_2_push [compile_aux_2_add compile_aux_2_sub]].
  intro ae.
  (* now consider and induction over ae *)
  induction ae as [ n | exp1 IH_exp1_add exp2 IH_exp2_add
                    | exp1 IH_exp1_sub exp2 IH_exp2_sub].

  (* case 1 : Literal *)
  rewrite -> (compile_aux_1_push n) ; rewrite -> (compile_aux_2_push n) ;
    reflexivity.

  (* case 2 : Addition of expressions *)
  rewrite -> (compile_aux_1_add exp1 exp2); rewrite -> (compile_aux_2_add exp1 exp2).
  rewrite -> IH_exp1_add; rewrite -> IH_exp2_add.
  reflexivity.

  (* case 3: subtraction of expressions *)
  rewrite -> (compile_aux_1_sub exp1 exp2); rewrite -> (compile_aux_2_sub exp1 exp2).
  rewrite -> IH_exp1_sub; rewrite -> IH_exp2_sub.
  reflexivity.
Qed.

(* implementation of compilation using concatenation of bci lists *)
Fixpoint compile_aux_v0 (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
  | Literal n =>
    (PUSH n) :: nil
  | Plus ae1 ae2 =>
    (compile_aux_v0 ae1) ++ (compile_aux_v0 ae2) ++ (ADD :: nil)
  | Minus ae1 ae2 =>
    (compile_aux_v0 ae1) ++ (compile_aux_v0 ae2) ++ (SUB :: nil)
  end.

(* standard unfold lemmas *)
Lemma unfold_compile_aux_v0_literal :
  forall (n : nat),
    compile_aux_v0 (Literal n) = (PUSH n) :: nil.
Proof.
  unfold_tactic compile_aux_v0.
Qed.


Lemma unfold_compile_aux_v0_plus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_aux_v0 (Plus ae1 ae2)  =
    (compile_aux_v0 ae1) ++ (compile_aux_v0 ae2) ++ (ADD :: nil).
Proof.
  unfold_tactic compile_aux_v0.
Qed.


Lemma unfold_compile_aux_v0_minus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_aux_v0 (Minus ae1 ae2)  =
    (compile_aux_v0 ae1) ++ (compile_aux_v0 ae2) ++ (SUB :: nil).
Proof.
  unfold_tactic compile_aux_v0.
Qed.


(* proof that compile_aux_v0 meets the specification *)
Theorem compile_aux_v0_meets_specification_of_compile_aux :
  specification_of_compile_aux compile_aux_v0.
Proof.
  unfold specification_of_compile_aux.
  
  split.
  intro n.
  rewrite -> (unfold_compile_aux_v0_literal n).
  reflexivity.

  split.
  intros ae1 ae2.
  rewrite -> (unfold_compile_aux_v0_plus ae1 ae2).
  reflexivity.

  intros ae1 ae2.
  rewrite -> (unfold_compile_aux_v0_minus ae1 ae2).
  reflexivity.
Qed.



Definition specification_of_compile (compile : source_program -> target_program) :=
  forall compile_aux : arithmetic_expression -> list byte_code_instruction,
    specification_of_compile_aux compile_aux ->
    forall ae : arithmetic_expression,
      compile (Source_program ae) = Target_program (compile_aux ae).

(* Task 7:
   prove that the definition above specifies a unique function,
   implement this function,
   and verify that your function satisfies the specification.
 *)
(* the specification_of_compile is sound *)
Theorem specification_of_compile_is_sound :
  forall (compiler1 compiler2 : source_program -> target_program),
    specification_of_compile compiler1 ->
    specification_of_compile compiler2 ->
    forall (ae : arithmetic_expression),
      compiler1 (Source_program ae) =
      compiler2 (Source_program ae).
Proof.
  intros compiler1 compiler2.
  unfold specification_of_compile.
  intros H1 H2.
  intro ae.
  rewrite -> (H1 compile_aux_v0 compile_aux_v0_meets_specification_of_compile_aux ae).
  rewrite -> (H2 compile_aux_v0 compile_aux_v0_meets_specification_of_compile_aux ae).
  reflexivity.
Qed.

(* implementation of the specification_of_compile *)
Definition compile_v0 (sp : source_program) : target_program :=
  match sp with
  | Source_program sp =>
    Target_program (compile_aux_v0 sp)
  end.

(* Proof that compile_v0 meets the specification_of_compile *)
Theorem compile_v0_meets_the_specification_of_compile :
  specification_of_compile compile_v0.
Proof.
  unfold specification_of_compile.
  intros compile_aux_var H_about_compile_aux_var.
  intro ae.
  unfold compile_v0.
  rewrite ->
          (specification_of_compile_aux_is_sound
          compile_aux_var
          compile_aux_v0
          H_about_compile_aux_var
          compile_aux_v0_meets_specification_of_compile_aux
          ae).
  reflexivity.
Qed.


(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.
 *)

(* auxiliary compile function implemented with accumulator *)
Fixpoint compile_aux_v1 (ae : arithmetic_expression)
         (acc : list byte_code_instruction) : list byte_code_instruction :=
  match ae with
  | Literal n =>
    (PUSH n) :: acc
  | Plus ae1 ae2 =>
    compile_aux_v1 ae1 (compile_aux_v1 ae2 (ADD :: acc))
  | Minus ae1 ae2 =>
    compile_aux_v1 ae1 (compile_aux_v1 ae2 (SUB :: acc))
  end.

(* unfold lemmas *)
Lemma unfold_compile_aux_v1_literal :
  forall (n : nat)
         (acc : list byte_code_instruction),
    compile_aux_v1 (Literal n) acc = (PUSH n) :: acc.
Proof.
  unfold_tactic compile_aux_v1.
Qed.


Lemma unfold_compile_aux_v1_plus :
  forall (ae1 ae2 : arithmetic_expression)
         (acc :list byte_code_instruction),
    compile_aux_v1 (Plus ae1 ae2) acc =
    compile_aux_v1 ae1 (compile_aux_v1 ae2 (ADD :: acc)).
Proof.
  unfold_tactic compile_aux_v1.
Qed.

Lemma unfold_compile_aux_v1_minus :
  forall (ae1 ae2 : arithmetic_expression)
         (acc :list byte_code_instruction),
    compile_aux_v1 (Minus ae1 ae2) acc =
    compile_aux_v1 ae1 (compile_aux_v1 ae2 (SUB :: acc)).
Proof.
  unfold_tactic compile_aux_v1.
Qed.

(* Master lemma concerning the relation between compile_aux_v1 and compile_aux_v0 *)
Lemma master_lemma_about_compile_aux_v1 :
  forall (ae : arithmetic_expression)
         (acc : list byte_code_instruction),
    compile_aux_v1 ae acc =  (compile_aux_v0 ae) ++ acc.
Proof.
  intros ae.
  induction ae as [ n | exp1 IH_exp1_add exp2 IH_exp2_add |
                    exp1 IH_exp1_sub exp2 IH_exp2_sub ].

  (* literals *)
  intro acc.
  rewrite -> (unfold_compile_aux_v1_literal n acc).
  rewrite -> (unfold_compile_aux_v0_literal n).
  Search (_ ++ _ = _).
  rewrite -> (unfold_append_cons (PUSH n) nil acc).
  rewrite -> (unfold_append_nil).
  reflexivity.

  (* plus *)
  intro acc.
  rewrite -> (unfold_compile_aux_v1_plus exp1 exp2 acc).
  rewrite -> (unfold_compile_aux_v0_plus exp1 exp2).
  rewrite -> (IH_exp2_add (ADD :: acc)).
  rewrite -> (IH_exp1_add (compile_aux_v0 exp2 ++ ADD :: acc)).
  Search (_ ++ _ = _).
  rewrite -> app_assoc_reverse.
  rewrite -> app_assoc_reverse.
  rewrite -> unfold_append_cons.
  rewrite -> unfold_append_nil.
  reflexivity.

  (* the proof for minus will be very similar *)
  intro acc.
  rewrite -> (unfold_compile_aux_v1_minus exp1 exp2 acc).
  rewrite -> (unfold_compile_aux_v0_minus exp1 exp2).
  rewrite -> (IH_exp2_sub (SUB :: acc)).
  rewrite -> (IH_exp1_sub (compile_aux_v0 exp2 ++ SUB :: acc)).
  Search (_ ++ _ = _).
  rewrite -> app_assoc_reverse.
  rewrite -> app_assoc_reverse.
  rewrite -> unfold_append_cons.
  rewrite -> unfold_append_nil.
  reflexivity.
Qed.



(* compiler implementation that uses an accumulator based auxiliary function *)
Definition compile_v1 (sp : source_program) : target_program :=
  match sp with
  | Source_program sp =>
    Target_program (compile_aux_v1 sp nil)
  end.


(* Proof that compile_v1 meets the specification_of_compile *)
Theorem compile_v1_meets_the_specification_of_compile :
  specification_of_compile compile_v1.
Proof.
  unfold specification_of_compile.
  intros compile_aux_var H_about_compile_aux_var.
  intro ae.
  unfold compile_v1.
  rewrite -> (master_lemma_about_compile_aux_v1 ae nil).
  Search ( _ ++ _ = _).
  rewrite -> app_nil_r.
  rewrite ->
          (specification_of_compile_aux_is_sound
          compile_aux_var
          compile_aux_v0
          H_about_compile_aux_var
          compile_aux_v0_meets_specification_of_compile_aux
          ae).
  reflexivity.
Qed.


(* ********** *)



(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
 *)

Lemma master_lemma_for_commutative_diagram :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
      fetch_decode_execute_loop (compile_aux_v0 ae) ds =     
      match (evaluate_v0 ae) with
      | Expressible_nat num =>
       OK (num :: ds)
      | Expressible_msg err_msg =>
        KO err_msg
      end.  
Proof.
  (* we will prove this lemma by induction over arithmetic expressions *)
  induction ae as [ nat_val | e1 IH_e1_plus e2 IH_e2_plus |
                    e1 IH_e1_minus e2 IH_e2_minus].

  (* literals *)
  intro ds_for_lemma.
  (* unfold L.H.S. *)
  rewrite -> unfold_compile_aux_v0_literal.
  rewrite ->
          (unfold_fetch_decode_execute_loop_bcis (PUSH nat_val) nil ds_for_lemma).
  unfold decode_execute.
  rewrite -> unfold_fetch_decode_execute_loop_nil.
  (* unfold R.H.S. *)
  rewrite -> unfold_evaluate_v0_literal.
  reflexivity.

  (* plus expressions *)
  intro ds_for_lemma.
  (* unfold R.H.S and L.H.S. expressions *)
  rewrite -> (unfold_evaluate_v0_plus e1 e2).
  rewrite -> (unfold_compile_aux_v0_plus e1 e2).
  (* consider cases of evaluate_v0 first *)
  case (evaluate_v0 e1) as [err_msg_e1 | nat_val_e1] eqn : val_of_eval_v0_e1.

  (* evaluate_v0 e1 = Expressible_msg _ *)
  (* introduce lemma we proved about running the append of two bci lists *)
  Check (relation_between_execution_of_two_bcis_and_their_appended_version).
  destruct (relation_between_execution_of_two_bcis_and_their_appended_version
              (compile_aux_v0 e1)
              (compile_aux_v0 e2 ++ ADD :: nil)) as [H_OK H_KO].
  (* use the introduced hypotheses to modify the induction hypotheses, and use this
   * to prove the goal *)
  apply (H_KO ds_for_lemma err_msg_e1) in IH_e1_plus.
  rewrite -> IH_e1_plus. 
  reflexivity.

  (* evaluate_v0 e1 = Expressible_nat _ *)
  (* once again, introduce this hypothesis *)
  destruct (relation_between_execution_of_two_bcis_and_their_appended_version
              (compile_aux_v0 e1)
              (compile_aux_v0 e2 ++ ADD :: nil)) as [H_OK H_KO]. 
  apply (H_OK ds_for_lemma (nat_val_e1 :: ds_for_lemma)) in IH_e1_plus.
  rewrite -> IH_e1_plus.
  clear H_OK H_KO.
  (* now consider cases of (evaluate_v0 e2) *)
  case (evaluate_v0 e2) as [err_msg_e2 | nat_val_e2] eqn : val_of_eval_v0_e2.

  (* evaluate_v0 e2 = Expressible_msg _ *)
  destruct (relation_between_execution_of_two_bcis_and_their_appended_version
              (compile_aux_v0 e2)
              (ADD :: nil)) as [H_OK H_KO].
  apply (H_KO (nat_val_e1 :: ds_for_lemma) err_msg_e2) in IH_e2_plus.
  rewrite -> IH_e2_plus.
  reflexivity.

  (* evaluate_v0 e2 = Expressible_msg _ *)
  destruct (relation_between_execution_of_two_bcis_and_their_appended_version
              (compile_aux_v0 e2)
              (ADD :: nil)) as [H_OK H_KO].
   apply (H_OK (nat_val_e1 :: ds_for_lemma)
              (nat_val_e2 :: nat_val_e1 :: ds_for_lemma)) in
            IH_e2_plus.
   rewrite -> IH_e2_plus.
   rewrite -> (unfold_fetch_decode_execute_loop_bcis ADD nil).
   unfold decode_execute.
   rewrite -> unfold_fetch_decode_execute_loop_nil.
   reflexivity.

   (* minus *)
   (* the structure of this section of the proof is very simlar to that of plus *)
   intro ds_for_lemma.
  (* unfold R.H.S and L.H.S. expressions *)
  rewrite -> (unfold_evaluate_v0_minus e1 e2).
  rewrite -> (unfold_compile_aux_v0_minus e1 e2).
  (* consider cases of evaluate_v0 first *)
  case (evaluate_v0 e1) as [err_msg_e1 | nat_val_e1] eqn : val_of_eval_v0_e1.

  (* evaluate_v0 e1 = Expressible_msg _ *)
  (* introduce lemma we proved about running the append of two bci lists *)
  Check (relation_between_execution_of_two_bcis_and_their_appended_version).
  destruct (relation_between_execution_of_two_bcis_and_their_appended_version
              (compile_aux_v0 e1)
              (compile_aux_v0 e2 ++ SUB :: nil)) as [H_OK H_KO].
  (* use the introduced hypotheses to modify the induction hypotheses, and use this
   * to prove the goal *)
  apply (H_KO ds_for_lemma err_msg_e1) in IH_e1_minus.
  rewrite -> IH_e1_minus. 
  reflexivity.

  (* evaluate_v0 e1 = Expressible_nat _ *)
  (* once again, introduce this hypothesis *)
  destruct (relation_between_execution_of_two_bcis_and_their_appended_version
              (compile_aux_v0 e1)
              (compile_aux_v0 e2 ++ SUB :: nil)) as [H_OK H_KO]. 
  apply (H_OK ds_for_lemma (nat_val_e1 :: ds_for_lemma)) in IH_e1_minus.
  rewrite -> IH_e1_minus.
  clear H_OK H_KO.
  (* now consider cases of (evaluate_v0 e2) *)
  case (evaluate_v0 e2) as [err_msg_e2 | nat_val_e2] eqn : val_of_eval_v0_e2.

  (* evaluate_v0 e2 = Expressible_msg _ *)
  destruct (relation_between_execution_of_two_bcis_and_their_appended_version
              (compile_aux_v0 e2)
              (SUB :: nil)) as [H_OK H_KO].
  apply (H_KO (nat_val_e1 :: ds_for_lemma) err_msg_e2) in IH_e2_minus.
  rewrite -> IH_e2_minus.
  reflexivity.

  (* evaluate_v0 e2 = Expressible_msg _ *)
  (* now we consider the cases of ltb nat_val_e1 and nat_val_e2 *)
  case (ltb nat_val_e1 nat_val_e2) eqn : value_of_ltb_nat_val_e1_nat_val_e2.

  (* ltb nat_val_e1 nat_val_e2 = true *)
  destruct (relation_between_execution_of_two_bcis_and_their_appended_version
              (compile_aux_v0 e2)
              (SUB :: nil)) as [H_OK H_KO].
  apply (H_OK (nat_val_e1 :: ds_for_lemma)
              (nat_val_e2 :: nat_val_e1 :: ds_for_lemma)) in
      IH_e2_minus.
  rewrite -> IH_e2_minus.
  rewrite -> (unfold_fetch_decode_execute_loop_bcis SUB nil).
  unfold decode_execute.
  rewrite -> value_of_ltb_nat_val_e1_nat_val_e2.
  reflexivity.

  (* ltb nat_val_e1 nat_val_e2 = false *)
  destruct (relation_between_execution_of_two_bcis_and_their_appended_version
              (compile_aux_v0 e2)
              (SUB :: nil)) as [H_OK H_KO].
  apply (H_OK (nat_val_e1 :: ds_for_lemma)
              (nat_val_e2 :: nat_val_e1 :: ds_for_lemma)) in
      IH_e2_minus.
  rewrite -> IH_e2_minus.
  rewrite -> (unfold_fetch_decode_execute_loop_bcis SUB nil).
  unfold decode_execute.
  rewrite -> value_of_ltb_nat_val_e1_nat_val_e2.
  rewrite -> unfold_fetch_decode_execute_loop_nil.
  reflexivity.
Qed.  


Theorem the_commutative_diagram :
    forall sp : source_program,
      interpret_v0 sp = run (compile_v0 sp).
Proof.
  intro sp.
  case sp as [ae].
  unfold interpret_v0; unfold compile_v0; unfold run.
  (* Use master lemma to finish off the proof *)
  Check (master_lemma_for_commutative_diagram).
  Check (master_lemma_for_commutative_diagram ae nil).
  rewrite ->
          (master_lemma_for_commutative_diagram ae nil).
  case (evaluate_v0 ae) as [err_msg | nat_val].
  reflexivity.
  reflexivity.
Qed.






(* ********** *)

(* Task 10 (if there is time):

   a. Write a Magritte interpreter for the source language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.

   b. Write a Magritte interpreter for the target language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.

   c. Prove that interpreting an arithmetic expression with the Magritte source interpreter
      gives the same result as first compiling it and then executing the compiled program
      with the Magritte target interpreter over an empty data stack.

   d. Prove that the Magritte target interpreter is (essentially)
      a left inverse of the compiler, i.e., it is a decompiler.
*)

(* ********** *)

(* Byte-code verification:
   the following verifier symbolically executes a byte-code program
   to check whether no underflow occurs during execution
   and whether when the program completes,
   there is one and one only natural number on top of the stack.
   The second argument of verify_aux is a natural number
   that represents the size of the stack.
*)

Fixpoint verify_aux (bcis : list byte_code_instruction) (n : nat) : option nat :=
  match bcis with
    | nil =>
      Some n
    | bci :: bcis' =>
      match bci with
        | PUSH _ =>
          verify_aux bcis' (S n)
        | _ =>
          match n with
            | S (S n') =>
              verify_aux bcis' (S n')
            | _ =>
              None
          end
      end
  end.

(* Unfold Lemmas *)
Lemma unfold_verify_aux_nil :
  forall (n : nat),
    verify_aux nil n = Some n.
Proof.
  unfold_tactic verify_aux.
Qed.

Lemma unfold_verify_aux_cons :
  forall (bci : byte_code_instruction)
         (bcis : list byte_code_instruction)
         (n : nat),
    verify_aux (bci :: bcis) n =
    match bci with
        | PUSH _ =>
          verify_aux bcis (S n)
        | _ =>
          match n with
            | S (S n') =>
              verify_aux bcis (S n')
            | _ =>
              None
          end
      end.
Proof.
  unfold_tactic verify_aux.
Qed.



Definition verify (p : target_program) : bool :=
  match p with
  | Target_program bcis =>
    match verify_aux bcis 0 with
    | Some n =>
      match n with
      | 1 =>
        true
      | _ =>
        false
      end
    | _ =>
      false
    end
  end.

(* Task 11:
   Prove that the compiler emits code
   that is accepted by the verifier.
*)

    

Lemma relation_between_bcis_and_verify_aux:
  forall (bci1s bci2s: list byte_code_instruction),
    (forall (n n': nat),
    verify_aux bci1s n = Some n' ->
    verify_aux (bci1s ++ bci2s) n = verify_aux (bci2s) n') /\
    (forall (n : nat),
        verify_aux bci1s n = None ->
        verify_aux (bci1s ++ bci2s) n = None).
Proof.
  Admitted.


Theorem the_compiler_emits_well_behaved_code :
  forall ae : arithmetic_expression,
    verify (compile_v0 (Source_program ae)) = true.
Proof.
  Abort.





(* What are the consequences of this theorem? *)

(* ********** *)

(* end of week-15_a-commutative-diagram.v *)
