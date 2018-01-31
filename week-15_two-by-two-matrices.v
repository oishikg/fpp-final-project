(* week-15_two-by-two-matrices.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Tue 21 Nov 2017 *)

(* ********** *)

(*
   name: Oishik Ganguly
   student ID number: A0138306J
   e-mail address: oishik.ganguly@u.yale-nus.edu.sg
 *)

(* ******** Paraphernalia ******** *)

Ltac unfold_tactic name :=
  intros;
  unfold name; (* fold name; *)
  reflexivity.

Require Import Arith Bool.

Inductive m22 : Type :=
| M22 : nat -> nat -> nat -> nat -> m22.

 
Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

(* Definition to capture the equality of 2*2 matrices *)
Definition eq_matrices (matrix_a : m22) (matrix_b : m22) :=
  match matrix_a with
  | M22 a11 a12 a21 a22 =>
    match matrix_b with
    | M22 b11 b12 b21 b22 =>
      (a11 =n= b11) && (a12 =n= b12) && (a21 =n= b21) && (a22 =n= b22)
    end
  end.

(* User defined induction principle for two base cases *)
Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall i : nat,
      P i -> P (S i) -> P (S (S i))) ->
    forall n : nat,
      P n.
Proof.
  intros P H_bc0 H_bc1 H_ic n.
  assert (H_Pn_PSn : P n /\ P (S n)).
    induction n as [ | n' [IH_n' IH_Sn']].
  
    split.

      apply H_bc0.

    apply H_bc1.
  
    split.

      apply IH_Sn'.

    apply (H_ic n' IH_n' IH_Sn').

  destruct H_Pn_PSn as [H_Pn _].
  apply H_Pn.
Qed.



(* We define a special notation to capture the equality of matrices. Two 2*2 matrices
 * are equal if every ijth term of the matrices are equal *)
Notation "A =m= B" :=
  (eq_matrices A B) (at level 70, right associativity).

(* This lemma allow us to substitute S n = n+1. This is useful in proving the theorem *)
Lemma Sn_is_n_plus_1:
  forall (n : nat),
    S n = n + 1.
Proof. 
  intro n.
  Check (plus_n_Sm).
  rewrite <- (plus_n_Sm).
  Search (_+ 0 = _).
  rewrite -> (plus_0_r n).
  reflexivity.
Qed.

 
(* ********** *)

(* The goal of this project is to study 2x2 matrices,
   along the lines of Section 5 of
     http://users-cs.au.dk/danvy/more-about-induction-proofs.pdf
 *)


(* implement Definition 9 (i.e., the multiplication of 2*2-matrices) *)
Definition m22_multiplication (matrix_a : m22) (matrix_b : m22) : m22 :=
  match matrix_a with
  | M22 a11 a12 a21 a22 =>
    match matrix_b with
    | M22 b11 b12 b21 b22 =>
      M22 (a11*b11 + a12*b21) (a11*b12 + a12*b22) (a21*b11 + a22*b21) (a21*b12 + a22*b22)
    end
  end.


(* Unit tests for m22_multiplication() *)
Definition unit_test_for_m22_multiplication : bool :=
  (m22_multiplication (M22 1 1 1 1) (M22 2 2 2 2) =m= M22 4 4 4 4)
    &&
    (m22_multiplication (M22 1 5 6 7) (M22 3 2 0 1) =m= M22 3 7 18 19)
    &&
    (m22_multiplication (M22 1 2 3 4) (M22 4 3 2 1) =m= M22 8 5 20 13)
    &&
    (m22_multiplication (M22 1 0 1 1) (M22 4 0 4 1) =m= M22 4 0 8 1)
    &&
    (m22_multiplication (M22 9 8 1 1) (M22 4 5 2 3) =m= M22 52 69 6 8).

Compute (unit_test_for_m22_multiplication).
                                                                  

(* implement the addition of 2*2-matrices *)
Definition m22_addition (matrix_a : m22) (matrix_b : m22) : m22 :=
  match matrix_a with
  | M22 a11 a12 a21 a22 =>
    match matrix_b with
    | M22 b11 b12 b21 b22 =>
      M22 (a11 + b11) (a12 + b12) (a21 + b21) (a22 + b22)
    end
  end.


(* Unit tests for m22_addition() *)
Definition unit_test_for_m22_addition : bool :=
  (m22_addition (M22 1 1 1 1) (M22 2 2 2 2) =m= M22 3 3 3 3)
    &&
    (m22_addition (M22 1 5 6 7) (M22 3 2 0 1) =m= M22 4 7 6 8)
    &&
    (m22_addition (M22 1 2 3 4) (M22 4 3 2 1) =m= M22 5 5 5 5)
    &&
    (m22_addition (M22 1 0 1 1) (M22 4 0 4 1) =m= M22 5 0 5 2)
    &&
    (m22_addition (M22 9 8 1 1) (M22 4 5 2 3) =m= M22 13 13 3 4).

Compute (unit_test_for_m22_addition).


(* implement Definitions 11 and 13 *)

(* Definition 11: The identity matrix *)
Definition m22_identity : m22 :=
  M22 1 0 0 1.

(* define the identity multiplication lemmas *)
Lemma m22_mult_identity_r :
  forall (matrix_a : m22),
    m22_multiplication matrix_a m22_identity = matrix_a.
Proof.
  intro matrix_a.
  unfold m22_identity.
  induction matrix_a as [a11 a12 a21 a22].
  unfold m22_multiplication.
  do 4 ( rewrite -> mult_1_r ; rewrite -> mult_0_r).
  do 2 ( rewrite -> plus_0_r ; rewrite -> plus_0_l).
  reflexivity.
Qed.


Lemma m22_mult_identity_l :
  forall (matrix_a : m22),
    m22_multiplication m22_identity matrix_a = matrix_a.
Proof.
  intro matrix_a.
  unfold m22_identity.
  induction matrix_a as [a11 a12 a21 a22].
  unfold m22_multiplication.
  do 4 ( rewrite -> mult_1_l ; rewrite -> mult_0_l).
  do 2 ( rewrite -> plus_0_l ; rewrite -> plus_0_r).
  reflexivity.
Qed.



(* Definition 13: Exponentiation of a matrix. We take two arguments for this defintion
 * , namely the matrix, and the exponent *)

Fixpoint m22_exponentiation (matrix_a : m22) (exponent : nat) : m22 :=
  match exponent with
  | 0 =>
    m22_identity
  | S n =>
    m22_multiplication (m22_exponentiation matrix_a n) matrix_a
  end.

(* Unfold lemmas *)
Lemma unfold_m22_exponentiation_0 :
  forall (matrix_a : m22),
    m22_exponentiation matrix_a 0 = m22_identity.
Proof.
  unfold_tactic m22_exponentiation.
Qed.

Lemma unfold_m22_exponentiation_S :
  forall (matrix_a : m22) (n :  nat),
    m22_exponentiation matrix_a (S n) =
    m22_multiplication (m22_exponentiation matrix_a n) matrix_a.
Proof.
  unfold_tactic m22_exponentiation.
Qed.

(* quick unit test for the exponentiation definition *)
Definition unit_test_for_m22_exponentiation : bool :=
  (m22_exponentiation (M22 2 3 4 5) 2 =m= M22 16 21 28 37)
    &&
    (m22_exponentiation (M22 0 3 2 5) 5 =m= M22 1110 3333 2222 6665)
    &&
    (m22_exponentiation (M22 1 3 2 1) 3 =m= M22 19 27 18 19)
    &&
    (m22_exponentiation (M22 1 0 9 7) 3 =m= M22 1 0 513 343)
    &&
    (m22_exponentiation (M22 1 2 2 1) 5 =m= M22 121 122 122 121).

Compute (unit_test_for_m22_exponentiation).

(* prove Properties 10 and 12 *)

(* Property 10: 2*2 multiplication is associative *)

Proposition m22_multiplication_is_associative :
  forall (matrix_a matrix_b matrix_c : m22),
    m22_multiplication matrix_a (m22_multiplication matrix_b matrix_c) =
    m22_multiplication (m22_multiplication matrix_a matrix_b) matrix_c.
Proof.
  intros matrix_a matrix_b matrix_c.
  (* use the inductive structure of a matrix for the proof *)
  induction matrix_a as [a11 a12 a21 a22].
  induction matrix_b as [b11 b12 b21 b22].
  induction matrix_c as [c11 c12 c21 c22].
  (* unfold matrix multiplication; since we are using the inductive structures, 
   * match statements are exectued *)
  unfold m22_multiplication.
  Search ( _ * (_ + _) = _).
  (* now we must simplify each of the natural numbers nested in the M22 constructor.
   * since the same set of tactics must be used for each of the four natural values 
   * on the left and right hand side, we use coq's loop facility to reduce the 
   * amount of code *)
  do 4
     (
       rewrite -> mult_plus_distr_l;
       rewrite -> mult_assoc;
       rewrite -> mult_assoc;
       rewrite -> mult_plus_distr_l;
       rewrite -> mult_assoc;
       rewrite -> mult_assoc;
       rewrite -> plus_assoc
     ).
  do 4
     (
       rewrite -> mult_plus_distr_r;
       rewrite -> mult_plus_distr_r;
       rewrite -> plus_permute_2_in_4;
       rewrite -> plus_assoc
     ).
  reflexivity.
Qed.

(* Before formalizing proposition 14, we define the special matrix we are dealing with
 * ; we call this matrix M1 *)
Definition M1 : m22 := M22 1 1 0 1.

(* formalize Proposition 14 and its proof in Coq *)
Proposition about_M1 : 
  forall (n : nat),
    m22_exponentiation M1  n = M22 1 n 0 1.
Proof.
  intro n.
  unfold M1.
  induction n as [ | n' IH_n'].

  (* base case *)
  rewrite -> (unfold_m22_exponentiation_0 (M22 1 1 0 1) ). 
  unfold m22_identity.
  reflexivity.

  (* inductive case *)
  rewrite -> (unfold_m22_exponentiation_S (M22 1 1 0 1) n').
  rewrite -> IH_n'.
  unfold m22_multiplication.
  Search (1*_ = _).
  (* some algebraic manipulation to reach the required goal *)
  rewrite mult_0_l.
  do 2 (rewrite -> mult_0_r ; rewrite -> mult_1_r ; rewrite -> plus_0_r).
  rewrite -> plus_0_l.
  rewrite -> (plus_comm 1 n').
  rewrite <- (Sn_is_n_plus_1 n').
  reflexivity.
Qed.

(* implement Definition 27 *)
Fixpoint m22_exponentiation_alternative (matrix_a : m22) (exponent :nat) : m22 :=
  match exponent with
  | 0 =>
    m22_identity
  | S n =>
    m22_multiplication (matrix_a) (m22_exponentiation_alternative matrix_a n)
  end.

(* We use the same unit tests as in the first definition of exponentiation *)
Definition unit_test_for_m22_exponentiation_alternative : bool :=
  (m22_exponentiation_alternative (M22 2 3 4 5) 2 =m= M22 16 21 28 37)
    &&
    (m22_exponentiation_alternative (M22 0 3 2 5) 5 =m= M22 1110 3333 2222 6665)
    &&
    (m22_exponentiation_alternative (M22 1 3 2 1) 3 =m= M22 19 27 18 19)
    &&
    (m22_exponentiation_alternative (M22 1 0 9 7) 3 =m= M22 1 0 513 343)
    &&
    (m22_exponentiation_alternative (M22 1 2 2 1) 5 =m= M22 121 122 122 121).

Compute (unit_test_for_m22_exponentiation_alternative).

(* Standard unfold lemmas *)
Lemma unfold_m22_exponentiation_alternative_0 :
  forall (matrix_a : m22) ,
    m22_exponentiation_alternative matrix_a 0 = m22_identity.
Proof.
  unfold_tactic m22_exponentiation_alternative.
Qed.

Lemma unfold_m22_exponentiation_alternative_S :
  forall (matrix_a : m22) (n : nat),
    m22_exponentiation_alternative matrix_a (S n) =
    m22_multiplication (matrix_a) (m22_exponentiation_alternative matrix_a n).
Proof.
  unfold_tactic m22_exponentiation_alternative.
Qed.

(* solve Exercise 28 : reproving proposition 14 using this definition *)
Proposition about_M1_alternative :
  forall (n : nat),
    m22_exponentiation_alternative M1 n = M22 1 n 0 1.
Proof.
  intro n.
  unfold M1.
  induction n as [ | n' IH_n'].

  (* base case *)
  rewrite -> (unfold_m22_exponentiation_alternative_0 (M22 1 1 0 1)).
  unfold m22_identity.
  reflexivity.

  (* inductive case *)
  rewrite -> (unfold_m22_exponentiation_alternative_S (M22 1 1 0 1) n').
  rewrite -> IH_n'.
  unfold m22_multiplication.
  (* some algebraic manipulation to get to the requried goal *)
  rewrite -> mult_0_r.
  do 2 (rewrite -> mult_0_l ; rewrite -> mult_1_l ; rewrite -> plus_0_l).
  rewrite -> plus_0_r.
  rewrite <- (Sn_is_n_plus_1 n').
  reflexivity.
Qed.

(* formalize Proposition 29 and its proof in Coq *)
Proposition m22_exponentiation_is_commutative :
  forall (matrix_a : m22) (n : nat),
    m22_multiplication (matrix_a) (m22_exponentiation matrix_a n) =
    m22_multiplication (m22_exponentiation matrix_a n) (matrix_a).
Proof.
  intros matrix_a n.
  induction n as [ | n' IH_n'].

  (* base case *)
  rewrite -> unfold_m22_exponentiation_0.
  (* using the lemmas we had already defined *)
  rewrite -> m22_mult_identity_l.
  rewrite -> m22_mult_identity_r.
  reflexivity.

  (* inductive case *)
  rewrite -> unfold_m22_exponentiation_S.
  (* use the associativity of matrix multiplication *)
  rewrite -> m22_multiplication_is_associative.
  rewrite -> IH_n'.
  reflexivity.
Qed.

(* solve Exercise 31 *)
Proposition m22_exponentiation_alternative_is_commutative :
  forall (matrix_a : m22) (n : nat),
    m22_multiplication matrix_a (m22_exponentiation_alternative matrix_a n) =
    m22_multiplication (m22_exponentiation_alternative matrix_a n) matrix_a.
Proof.
  intros matrix_a n.
  induction n as [ |n' IH_n'].

  (* base case *)
  rewrite -> unfold_m22_exponentiation_alternative_0.
  (* using the lemmas we had already defined *)
  rewrite -> m22_mult_identity_l.
  rewrite -> m22_mult_identity_r.
  reflexivity.

   (* inductive case *)
  rewrite -> unfold_m22_exponentiation_alternative_S.
  (* use the associativity of matrix multiplication *)
  rewrite <-  m22_multiplication_is_associative.
  rewrite -> IH_n'.
  reflexivity.
Qed.

(* implement Corollary 32 *)
Corollary m22_exponentiation_is_equivalent_to_m22_exponentiation_alternative :
  forall (matrix_a : m22) (n : nat),
    m22_exponentiation matrix_a n = m22_exponentiation_alternative matrix_a n.
Proof.
  intros matrix_a n.

  (* base case *)
  induction n as [ |n' IH_n'].
  rewrite -> unfold_m22_exponentiation_0.
  rewrite -> unfold_m22_exponentiation_alternative_0.
  reflexivity.

  (* inductive case *)
  rewrite -> unfold_m22_exponentiation_S.
  rewrite -> unfold_m22_exponentiation_alternative_S.
  rewrite <-  m22_exponentiation_is_commutative.
  rewrite -> IH_n'.
  reflexivity.
Qed.

(* Before solving 34, we will define the matrix in it, and call it M2 *)
Definition M2 : m22 := M22 1 0 1 1.
(* solve Exercise 34 *)

(* We will use the first definition of exponentiation (def 13) *)
Proposition about_M2 :
  forall (n : nat),
    m22_exponentiation M2 n = M22 1 0 n 1.
Proof.
  intro n.
  unfold M2.
  induction n as [ | n' IH_n'].

  (* base case *)
  rewrite -> unfold_m22_exponentiation_0.
  unfold m22_identity.
  reflexivity.

  (* inductive case *)
  rewrite -> unfold_m22_exponentiation_S.
  rewrite -> IH_n'.
  unfold m22_multiplication.
  rewrite -> mult_0_l.
  do 2 (rewrite -> mult_0_r; rewrite -> mult_1_r; rewrite -> plus_0_l).
  rewrite -> plus_0_r.
  rewrite <- Sn_is_n_plus_1.
  reflexivity.
Qed.  

(* implement Definition 35 *)

(* defining the transpose a 2*2 matrix *)
Definition m22_transpose (matrix_a : m22) : m22 :=
  match matrix_a with
  | M22 a11 a12 a21 a22 =>
    M22 a11 a21 a12 a22
  end.

(* prove Property 36 *)
Proposition m22_transposition_is_involutive :
  forall (matrix_a : m22),
    m22_transpose (m22_transpose matrix_a) = matrix_a.
Proof.
  intro matrix_a.
  induction matrix_a as [a11 a12 a21 a22].
  unfold m22_transpose.
  reflexivity.
Qed.


(* formalize Proposition 37 and its proof in Coq *)
Proposition m22_transpose_of_product :
  forall (matrix_x : m22) (matrix_y : m22),
    m22_transpose (m22_multiplication matrix_x matrix_y) =
    m22_multiplication (m22_transpose matrix_y) (m22_transpose matrix_x).
Proof.
  intros matrix_x matrix_y.
  induction matrix_x as [x11 x12 x21 x22].
  induction matrix_y as [y11 y12 y21 y22].
  unfold m22_multiplication.
  unfold m22_transpose.
  (* now we do some algebraic manipulation *)
  Search (_*_ = _*_).
  rewrite -> (mult_comm x11 y11);
    rewrite -> (mult_comm x12 y21);
    rewrite -> (mult_comm x21 y11);
    rewrite -> (mult_comm x22 y21);
    rewrite -> (mult_comm x11 y12);
    rewrite -> (mult_comm x12 y22);
    rewrite -> (mult_comm x21 y12);
    rewrite -> (mult_comm x22 y22).
  reflexivity.
Qed.  

(* before proving proposition 38, we prove a simple lemma about the tranpose of the 
 * identity matrix *)
Lemma tranpose_of_m22_identity_is_identity :
  m22_transpose (m22_identity) = m22_identity.
Proof.
  unfold m22_identity.
  unfold m22_transpose.
  reflexivity.
Qed.


(* formalize Proposition 38 and its proof in Coq *)
Proposition m22_transposition_and_exponentiation_commute :
  forall (matrix_a : m22) (n : nat),
    m22_transpose (m22_exponentiation matrix_a n) =
    m22_exponentiation (m22_transpose matrix_a) n.
Proof.
  intros matrix_a n.
  induction n as [ |n' IH_n'].

  (* base case *)
  do 2 (rewrite -> unfold_m22_exponentiation_0).
  rewrite -> tranpose_of_m22_identity_is_identity.
  reflexivity.

  (* inductive case *)
  rewrite -> (unfold_m22_exponentiation_S (matrix_a) n').
  rewrite -> m22_transpose_of_product.
  rewrite -> IH_n'.
  (* Rewrite L.H.S. using the alternative definiton of exponentiation *)
  rewrite -> (m22_exponentiation_is_equivalent_to_m22_exponentiation_alternative
                (m22_transpose matrix_a) n').
  Check (unfold_m22_exponentiation_alternative_S (m22_transpose matrix_a) n').
  rewrite <- (unfold_m22_exponentiation_alternative_S (m22_transpose matrix_a) n').
  (* since both definitions of exponentiation are equivalent, we use this equivalence 
   * to reach our goal *)
  rewrite -> (m22_exponentiation_is_equivalent_to_m22_exponentiation_alternative
                (m22_transpose matrix_a) (S n')). 
  
  reflexivity.
Qed.

(* We prove a very quick lemma about the two matrices dealt with in proposition 40 *)
Lemma M2_is_the_tranpose_of_M1 :
  M2 = m22_transpose M1.
Proof.
  
  unfold m22_transpose.
  reflexivity.
Qed.
  
(* solve Exercise 40 *)
Proposition about_M2_without_induction :
  forall (n : nat),
    m22_exponentiation M2 n = M22 1 0 n 1.
Proof.
  intro n.
  rewrite -> M2_is_the_tranpose_of_M1.
  rewrite <- m22_transposition_and_exponentiation_commute.
  (* now we use the theorem about m22_1101 *)
  rewrite -> (about_M1 n).
  reflexivity.
Qed.

(* solve Exercise 25 *)

(* We will use the fixpoint defintion for exponentiation to check F^0, ..., F^n *)
Definition F : m22 := M22 1 1 1 0.

Compute (m22_exponentiation F 0).
Compute (m22_exponentiation F 1).
Compute (m22_exponentiation F 2).
Compute (m22_exponentiation F 3).
Compute (m22_exponentiation F 4).

(* We observe that for all n >= 0, F^n returns a matrix with the nth element of the 
 * fibonacci sequence in row 1 column 2. Furthermore, we find that forall n, 
 * F^ (S (S n)) = F^(S n) + F^n. Thus the function (m22_exponentiation F) 
 * which takes n as input, satisfies the specifcation for a fibonacci function *)

(* To prove this, we initially defined and tried to prove a lemma that formalized
 * the above characterization of F. However, we soon realized that we would 
 * first have to prove that F^(n+2) = F^(n+1) + F^n to proceed with our proof. 
 * We completed the subsidiary characterization for function F below first *)
 

(*Subsidiary question for Exercise 25:
   characterize the result of adding F^n and F^(n+1), for any n : nat *)

(* Clearly, exponentiating F has the following property : 
 * F^0 = M22 1 0 0 1
 * F^1 = M22 1 1 1 0
 * F^n + F^(n+1) = F^(n+2) *)

(* We will now show this characterization holds; but first, we define two auxiliary
 * lemmas concerning the distributive properties of matrices *)

Lemma  m22_distr_mult_l :
  forall (matrix_a matrix_b matrix_c : m22),
    m22_multiplication matrix_a (m22_addition matrix_b matrix_c) =
    m22_addition (m22_multiplication matrix_a matrix_b)
                 (m22_multiplication matrix_a matrix_c).
Proof.
  intros matrix_a matrix_b matrix_c.
  induction matrix_a as [a11 a12 a21 a22];
    induction matrix_b as [b11 b12 b21 b22];
    induction matrix_c as [c11 c12 c21 c22].
  unfold m22_multiplication; unfold m22_addition.
  Search (_* (_ + _) = _).
  do 8 (rewrite -> mult_plus_distr_l).
  Check (plus_permute_2_in_4).
  rewrite -> (plus_permute_2_in_4 (a11*b11) _ _ _).
  rewrite -> (plus_permute_2_in_4 (a11*b12) _ _ _).
  rewrite -> (plus_permute_2_in_4 (a21*b11) _ _ _).
  rewrite -> (plus_permute_2_in_4 (a21*b12) _ _ _).
  reflexivity.
Qed.

Lemma  m22_distr_mult_r :
  forall (matrix_a matrix_b matrix_c : m22),
    m22_multiplication (m22_addition matrix_b matrix_c) matrix_a = 
    m22_addition (m22_multiplication matrix_b matrix_a)
                 (m22_multiplication matrix_c matrix_a).
Proof.
  intros matrix_a matrix_b matrix_c.
  induction matrix_a as [a11 a12 a21 a22];
    induction matrix_b as [b11 b12 b21 b22];
    induction matrix_c as [c11 c12 c21 c22].
  unfold m22_multiplication; unfold m22_addition.
  Search (_* (_ + _) = _).
  do 8 (rewrite -> mult_plus_distr_r).
  Check (plus_permute_2_in_4).
  rewrite -> (plus_permute_2_in_4 (b11*a11) _ _ _).
  rewrite -> (plus_permute_2_in_4 (b11*a12) _ _ _).
  rewrite -> (plus_permute_2_in_4 (b21*a11) _ _ _).
  rewrite -> (plus_permute_2_in_4 (b21*a12) _ _ _).
  reflexivity.
Qed.

(* Armed with these lemmas, we now show that the above characterization of F holds *)
Proposition about_F :
  forall (n : nat),
    m22_addition (m22_exponentiation F n) (m22_exponentiation F (S n)) =
    m22_exponentiation F (S (S n)).
Proof.
  intro n.
  induction n as [ | | n' IH_n' IH_Sn'] using nat_ind2.

  (* base case 0 *)
  do 3 (rewrite -> unfold_m22_exponentiation_S).
  rewrite -> unfold_m22_exponentiation_0.
  rewrite -> m22_mult_identity_l.
  unfold F; unfold m22_identity; unfold m22_addition; unfold m22_multiplication.
  (* Simplifying L.H.S. *)  
  rewrite -> plus_0_l.
  rewrite -> plus_0_r.
  rewrite <- Sn_is_n_plus_1.
  (* Simplifying R.H.S. *)
  rewrite -> mult_1_l.
  do 2 (rewrite -> mult_0_r).
  rewrite -> mult_0_l.
  rewrite -> plus_0_r.
  rewrite <- Sn_is_n_plus_1.
  reflexivity.

  (* base case 1 *)
  do 6 (rewrite -> unfold_m22_exponentiation_S).
  rewrite -> unfold_m22_exponentiation_0.
  rewrite -> m22_mult_identity_l.
  unfold F; unfold m22_identity; unfold m22_addition; unfold m22_multiplication.
  (* Simplifying the L.H.S *)
  rewrite -> mult_1_l.
  do 2 (rewrite -> mult_0_r).
  rewrite -> mult_0_l.
  rewrite -> plus_0_r.
  rewrite -> plus_0_l.
  rewrite <- Sn_is_n_plus_1.
  rewrite -> (plus_comm 1 2).
  rewrite <- Sn_is_n_plus_1.
  (* Simplifying R.H.S. *)
  do 2 (rewrite -> mult_1_l).
    rewrite -> mult_1_r.
  do 2 (rewrite -> plus_0_r).
  do 2 (rewrite <- Sn_is_n_plus_1).
  reflexivity.

  (* inductive case *) 
    (* factorize the L.H.S. as follows: F^(n+2) + F^(n+2) = (F^(n+1) + F^(n+2)).F *)
  rewrite -> (unfold_m22_exponentiation_S F (S n')).
  rewrite -> (unfold_m22_exponentiation_S F (S (S n'))).
  rewrite <- m22_distr_mult_r.
  (* Now use the inductive hypothesis *)
  rewrite -> IH_Sn'.
  rewrite <- unfold_m22_exponentiation_S.
  reflexivity.
Qed.



(* With this characterization proved, we may now prove our hypothesis about the
 * exponentiation of F, namely that F^n returns a matrix such that the 
 * element in the 1st row, 2nd column (a12) is the nth element of the Fibonacci 
 * sequence *)


(* To do so, we first define a function that accepts a nat value n and returns 
 * the nth element of the fibonacci function, and the unfold lemmas that come
 * with it *)

Fixpoint fib_v0 (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => match n' with
            | O => 1
            | S n'' => (fib_v0 n') + (fib_v0 n'')
            end
  end.

(* Unit tests for fib_v0 *)
Definition unit_test_for_fib_v0 :=
  (fib_v0 0 =n= 0)
    &&
    (fib_v0 1 =n= 1)
    &&
    (fib_v0 2 =n= 1)
    &&
    (fib_v0 3 =n= 2)
    &&
    (fib_v0 4 =n= 3)
    &&
    (fib_v0 5 =n= 5)
    &&
    (fib_v0 6 =n= 8).

Compute (unit_test_for_fib_v0).


(* The standard mandatory unfold lemmas: *)

Lemma unfold_fib_v0_O :
  fib_v0 O = 0.
Proof.
  unfold_tactic fib_v0.
Qed.

Lemma unfold_fib_v0_1 :
  fib_v0 1 = 1.
Proof.
  unfold_tactic fib_v0.
Qed.

Lemma unfold_fib_v0_SS :
  forall n'' : nat,
    fib_v0 (S (S n'')) = (fib_v0 (S n'')) + (fib_v0 n'').
Proof.
  unfold_tactic fib_v0.
Qed.


(* We now define our hypothesis about F's fibonacci characteristic as a lemma, and 
 * prove it *)
Lemma the_fiboncci_character_of_F :
  forall (n : nat),
    (match m22_exponentiation F n with
    | M22 _ a12 _ _ =>
      a12
     end) = fib_v0 n.
Proof.
  intro n.
  induction n as [ | | n' IH_n' IH_Sn'] using nat_ind2.

  (* base case 0 *)
  rewrite -> unfold_m22_exponentiation_0.
  unfold m22_identity.
  symmetry.
  exact unfold_fib_v0_O.

  (* base case 1 *)
  rewrite -> (unfold_m22_exponentiation_S F 0).
  rewrite -> unfold_m22_exponentiation_0.
  rewrite -> m22_mult_identity_l.
  unfold F.
  symmetry.
  exact unfold_fib_v0_1.

  (* inductive case *)
  rewrite -> unfold_fib_v0_SS.
  rewrite <- IH_n'.
  rewrite <- IH_Sn'.
  (* use the lemma about_F here to simplify the F^(S (S n)) *)
  rewrite <- about_F.
  (* use the inductive structure of the matrix to get past the match statement *)
  induction (m22_exponentiation F n') as [x11 x12 x21 x22].
  induction (m22_exponentiation F (S n')) as [y11 y12 y21 y22].
  unfold m22_addition.
  rewrite -> plus_comm.
  reflexivity.
Qed.

(* ********** *)

(* end of week-15_two-by-two-matrices.v *)