(* Definition x := y. *)
(* Definition fst(A B : Set) (p : A /\ B) : A =
                                         match p with
                                           pair a b => a.
                                             end.
 *)

(* SET: Bools *)
Inductive Bool : Set :=
  true' : Bool
| false' : Bool.

Definition if' (C : Bool -> Set) (b : Bool) (c1 : C true') (c2 : C false') : C b :=
  match b with
    true' => c1
  | false' => c2
  end.

Theorem elim_rule_bool: forall (C : Bool -> Set) (c1 : C true') (c2 : C false'),
    (if' C true' c1 c2) = c1 /\ (if' C false' c1 c2) = c2.
Proof.
  intros C c1 c2.
  (* Смотрит, правда ли, что можно что-то сократить *)
  (* Можно сделать без simpl с помощью refine *)
  simpl.
  exact (conj (eq_refl c1) (eq_refl c2)).
Qed.

(*
Section Elim_rule.
  Theorem elim_rule_bool': (if' C true' c1 c2) = c1 /\ (if' C false' c1 c2) = c2.
                                                         Variable C : Bool -> Set.
                                                         Variable c1 : C true'.
                                                         Variable c2 : C false'.
End Elim_rule.
 *)

(* if хорошо работает по индуктивным типам из двух конструкторов *)
Definition or' (a b : Bool) : Bool :=
  if a then true' else b.

Definition and' (a b : Bool) : Bool :=
  if a then (if b then true' else false') else false'.

Infix "||" := or' : Bool_scope.
Infix "&&" := and' : Bool_scope.

(* Делаем сейчас скоуп и открываем, в котором будут работать инфиксные операторы *)
(* Local перед Open делает его не импортиться никуда *)
Open Scope Bool_scope.

Inductive True' : Prop :=
  I' : True'.

Inductive False' : Prop := .

Definition not' (A : Prop) := A -> False'.

Notation "~' A" := (not' A) (at level 75, right associativity) : Prop_scope.

Open Scope Prop_scope.

Definition Is_true (a : Bool) : Prop :=
  match a with
    true' => True'
  | false' => False'
  end.

Theorem or_commutes' : forall (a b : Bool), Is_true (a || b) -> Is_true (b || a).
Proof.
  intros a b.
  case a, b.
  simpl.
  intros t.
  exact t.
  simpl.
  intros t.
  exact t.
  simpl.
  intros t.
  exact t.
  simpl.
  intros f.
  exact f.
Qed.


(* SET: Empty sets *)
Inductive Empty : Set := .


(* SET: Id *)
Inductive Id(A: Type) (x: A) : A -> Type :=
  id: Id A x x.


(* SET: Nats *)
Inductive Nat : Set :=
  zero : Nat              (* O в stdlib *)
| succ : Nat -> Nat.      (* S в stdlib *)

(* Fixpoint for recursive *)
Fixpoint natrec
    (C : Nat -> Set)
    (d : C zero)
    (e : forall (x : Nat) (y : C x), C (succ x))
    (n : Nat) : C n :=
  match n with
    zero => d
  | succ m => e m (natrec C d e m)
  end.

Definition plus' (n m : Nat) : Nat :=
  natrec (fun _ => Nat) n (fun x y => succ y) m.

Definition mul' (n m : Nat) : Nat :=
  natrec (fun _ => Nat) zero (fun x y => plus' y n) m.

Infix "+" := plus' : Nat_scope.
Infix "*" := mul'  : Nat_scope.

Open Scope Nat_scope.

Theorem zero_neutral_right : forall n : Nat, Id Nat (n + zero) n.
Proof.
  intros n.
  unfold plus'.
  simpl.
  exact (id Nat n).
Qed.

Theorem zero_neutral_left : forall n : Nat, Id Nat (zero + n) n.
Proof.
  intros n.
  unfold plus'.
  elim n.
  (* base *)
  simpl.
  exact (id Nat zero).
  (* shift *)
  intros n0.
  intros ind_hyp.
  simpl.
  rewrite ind_hyp.
  exact (id _ (succ n0)).
Qed.

Theorem comm_plus : forall (a b : Nat), Id Nat (a + b) (b + a).
Proof.
  intros a b.
  unfold plus'.
  elim a.
  (* base *)
  simpl.
  exact (zero_neutral_left b).
  (* shift *)
  simpl.
  intros n0.
  intros ind_hyp.
  rewrite <- ind_hyp.
  elim b.
  (* base *)
  simpl.
  exact (id Nat (succ n0)).
  (* shift *)
  intros n1 ind_hyp2.
  simpl.
  rewrite ind_hyp2.
  exact (id _ _).
Qed.
