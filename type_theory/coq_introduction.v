(* Definition x := y. *)
(* Definition fst(A B : Set) (p : A /\ B) : A =
                                         match p with
                                           pair a b => a.
                                             end.
*)

(* Propositional Bools *)
Inductive True' : Prop :=
  I' : True'.
Inductive False' : Prop := .
Definition not' (A : Prop) := A -> False'.
Notation "~ A" := (not' A) (at level 75, right associativity) : Prelude_scope.

(* Делаем сейчас скоуп и открываем, в котором будут работать инфиксные операторы *)
(* Local перед Open делает его не импортиться никуда *)
Open Scope Prelude_scope.


(* SET: Id *)
(* Curly braces -- implicit *)
Inductive Id {A: Type} (x: A) : A -> Type :=
  id: Id x x.

Infix "==" := Id (at level 70) : Prelude_scope.
Notation "x /= y" := (~(x == y)) (at level 70) : Prelude_scope.

(* if хорошо работает по индуктивным типам из двух конструкторов *)
Inductive And (A B : Prop) : Prop :=
  conj' : A -> B -> And A B.

Inductive Or (A B : Prop) : Prop :=
  inl' : A -> Or A B
| inr' : B -> Or A B.

Infix "/.\" := And (at level 80) : Prelude_scope.
Infix "\./" := Or (at level 85) : Prelude_scope.

(* Это нужно для:
   Раньше мы писали refine (conj' A B _ _)
   Теперь можно refine (conj' _ _)   *)
Implicit Arguments conj'.
Implicit Arguments inl'.
Implicit Arguments inr'.

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
    (if' C true' c1 c2) = c1 /.\ (if' C false' c1 c2) = c2.
Proof.
  intros C c1 c2.
  (* Смотрит, правда ли, что можно что-то сократить *)
  (* Можно сделать без simpl с помощью refine *)
  simpl.
  exact (conj' (eq_refl c1) (eq_refl c2)).
Qed.

Definition or' (a b : Bool) : Bool :=
  if' (fun x => Bool) a true' (if' (fun x => Bool) b true' false').

Definition and' (a b : Bool) : Bool :=
  if' (fun x => Bool) a (if' (fun x => Bool) b true' false') false'.

Infix "||" := or' : Prelude_scope.
Infix "&&" := and' : Prelude_scope.


Theorem or_commutes' : forall (a b : Bool), a || b == b || a.
Proof.
  intros a b.
  case a, b.
  simpl.
  exact (id true').
  simpl.
  exact (id true').
  simpl.
  exact (id true').
  simpl.
  exact (id false').
Qed.


(* SET: Empty sets *)
Inductive Empty : Set := .

(* SET: Nats *)
Section Natural_Numbers.
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
    natrec (fun _ => Nat) zero (fun x y => plus' n y) m.
  Infix "+" := plus' : Prelude_scope.
  Infix "*" := mul'  : Prelude_scope.

  Section Nat_Lemmas.
    Theorem zero_neutral_right : forall n : Nat, Id (n + zero) n.
    Proof.
      intros n.
      unfold plus'.
      simpl.
      exact (id n).
    Qed.

    Theorem zero_neutral_left : forall n : Nat, Id (zero + n) n.
    Proof.
      intros n.
      unfold plus'.
      elim n.
      (* base *)
      simpl.
      exact (id zero).
      (* shift *)
      intros n0.
      intros ind_hyp.
      simpl.
      rewrite ind_hyp.
      exact (id (succ n0)).
    Qed.

    Theorem comm_plus : forall (a b : Nat), Id (a + b) (b + a).
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
      exact (id (succ n0)).
      (* shift *)
      intros n1 ind_hyp2.
      simpl.
      rewrite ind_hyp2.
      exact (id _).
    Qed.

    Theorem assoc_plus : forall a b c : Nat, Id ((a + b) + c) (a + (b + c)).
    Proof.
      intros a b c.
      unfold plus'.
      elim c.
      (* base *)
      simpl.
      exact (id (a + b)).
      (* shift *)
      intros n ind_hyp.
      simpl.
      rewrite ind_hyp.
      exact (id _).
    Qed.

    Theorem transfer0_plus : forall a b : Nat, Id (succ (a + b)) (a + succ b).
    Proof.
      intros a b.
      elim a.
      exact (id (zero + succ b)).

      intros n0 ind_hyp0.
      exact (id (succ n0 + succ b)).
    Qed.

    Theorem transfer1_plus : forall a b : Nat, Id (succ (a + b)) (succ a + b).
    Proof.
      intros a b.
      rewrite (comm_plus (succ a) b).
      rewrite (comm_plus a b).
      exact (transfer0_plus b a).
    Qed.

    Theorem transfer_plus : forall a b : Nat, Id (succ a + succ b) (a + succ (succ b)).
    Proof.
      intros a b.
      rewrite <- (transfer1_plus a (succ b)).
      rewrite <- (transfer0_plus a (succ b)).
      exact (id _).
     Qed.

    Theorem comm_mul : forall a b c : Nat, Id (a * b) (b * a).
    Proof.
      intros a b c.
      unfold mul'.
      elim a.
      (* base1 *)
      simpl.
      elim b.
      (* base2 *)
      simpl.
      exact (id zero).
      (* shift2 *)
      simpl.
      intros.
      rewrite H.
      exact (id zero).

      (* shift1 *)
      intros.
      unfold plus'.
      unfold plus' in H.
      simpl H.
      simpl.
      rewrite <- H.
      intuition.
      admit.
    Qed.

    Theorem mul_zero_kills : forall a : Nat, Id (zero * a) zero.
    Proof.
      intros.
      elim a.
      exact (id zero).
      intros.
      unfold mul'.
      unfold mul' in H.
      simpl.
      rewrite H.
      exact (id zero).
    Qed.

    Theorem mul_succ_mull : forall a b : Nat, Id (succ a * b) (a * b + b).
    Proof.
      intros.
      elim b.
      exact (id zero).
      intros.
      unfold mul'.
      unfold mul' in H.
      simpl.
      rewrite (comm_plus _ _).
      rewrite H.
      admit.
    Qed.

    Theorem distr_mul : forall a b c : Nat, Id (a * (b + c)) (a * b + a * c).
    Proof.
      intros.
      elim a.
      (* base *)
      rewrite (mul_zero_kills b).
      rewrite (mul_zero_kills c).
      rewrite (mul_zero_kills (b + c)).
      exact (id zero).
      (* shift *)
      intros.
      rewrite (mul_succ_mull n (b + c)).
      rewrite (mul_succ_mull n b).
      rewrite (mul_succ_mull n c).
      rewrite H.
      rewrite (assoc_plus (n * b) b (n * c + c)).
      rewrite <- (assoc_plus b (n * c) c).
      rewrite (comm_plus b (n * c)).
      rewrite (assoc_plus (n * c) b c).
      rewrite <- (assoc_plus (n * b) (n * c) (b + c)).
      exact (id _).
2    Qed.
  End Nat_Lemmas.
End Natural_Numbers.


Inductive Pi (A: Set) (B : A -> Set) : Set :=
  lambda: (forall x: A, B x) -> Pi A B.

Definition apply' (A : Set) (B : A -> Set) (g : Pi A B) (x : A) :=
  match g with
    lambda f => f x
  end.

Notation "A ~> B" := (Pi A (fun _ => B)) (at level 45, right associativity) : Prelude_scope.
Notation "~' A"   := (A ~> Empty) (at level 45).

Definition lambda' (A B : Set) (f : A -> B) : A ~> B :=
  lambda A (fun _ => B) f.

Definition apply'' (A B : Set) (g : A ~> B) (x : A) :=
  apply' A (fun _ => B) g x.

(* A → ¬¬A *)
Theorem add_double_not : forall A : Set, A ~> (~'~'A).
Proof.
  intro A.
  exact (lambda' A (~'~' A) (fun x => lambda' (~'A) Empty (fun y => apply'' A Empty y x))).
Qed.

(* Disjoint union of two sets *)

Inductive orS (A B : Set) : Set :=
  inlS : A -> orS A B
| inrS : B -> orS A B.

Definition when (A B : Set) (C : orS A B -> Set) (p : orS A B) (f : forall x : A, C (inlS A B x))
           (g : forall y : B, C (inrS A B y)) :=
  match p with
    inlS x => f x
  | inrS x => g x
  end.

(* Disjoint union of family of sets *)
Inductive Sigma (A : Set) (B : A -> Set) : Set :=
  pair : forall (a : A) (b : B a), Sigma A B.

Definition split (A : Set)
           (B : A -> Set)
           (C : Sigma A B -> Set)
           (d : forall (a : A) (b : (B a)), C (pair A B a b))
           (p : Sigma A B) :=
  match p with
    pair a b => d a b
  end.

Definition fst' (A : Set) (B : A -> Set) (p : Sigma A B) : A :=
  split A B (fun _ => A) (fun a b => a) p.

Definition snd' (A : Set) (B : A -> Set) (p : Sigma A B) : B (fst' A B p) :=
  split A B (fun x => B (fst' A B x)) (fun _ y => y) p.

(* homework *)
(*
Theorem quantor_equality : forall (A : Set) (B : A -> Set),
    Pi A (fun x => ~'(B x)) ~> ~' Sigma A B.
 *)

(* SET : Lists *)
Inductive List (A : Set) : Set :=
  null : List A
| new : A -> List A -> List A.

(* head with default value *)
Definition head' (A : Set) (default : A) (l: List A) : A :=
  match l with
    null => default
  | new x xs => x
  end.

(* Maybe *)
Inductive Maybe {A : Set} : Set :=
  Nothing : Maybe
| Just : A -> Maybe.

(* head with maybe *)
Definition head'' (A : Set) (l : List A) : Maybe :=
  match l with
    null => Nothing
  | new x xs => Just x
  end.

(* Homework *)
(*
Definition head''' (A : Set) (l: List A) (proof : C /= null A) :A :=
  match l with
  end.
 *)

Definition tail' (A : Set) (l : List A) : List A :=
  match l with
    null => null A
  | new x xs => xs
  end.

Fixpoint foldr (A : Set)
         (C : List A -> Set)
         (accum : C (null A))
         (e : forall (x : A) (y : List A) (z : C(y)), C (new A x y))
         (l : List A) :=
  match l with
    null => accum
  | new x xs => e x xs (foldr A C accum e xs)
  end.

(* отношения и всякое *)

(*
f -- экстенциональна
∀ A B =ₐ =\_b : ∀ x, y ∈ A : x =ₐ y : f(x) =\_b f(y).

Тогда утверждение subst из третьей лекции -- любая функция f экстенциональна
 *)

Section Relation_definitions.
  Variable A : Type.
  Definition Relation (S : Type) := S -> S -> Prop.
  Variable R : Relation A.
  Section General_propertios_of_relations.
    Definition reflexive : Prop := forall a, R a a.
    Definition symmetric : Prop := forall a b, R a b -> R b a.
    Definition transitive : Prop := forall a b c, R a b -> R b c -> R a c.
    Definition equality : Prop := reflexive /.\ symmetric /.\ transitive.
  End General_propertios_of_relations.
  Section Meta_relations.
    Definition inclusion (R1 R2 : Relation A) : Prop :=
      forall x y : A, R1 x y -> R2 x y.
    Definition equal_rels (R1 R2 : Relation A) : Prop :=
      inclusion R1 R2 /.\ inclusion R2 R1.
    Definition min_relation (R : Relation A) : Prop :=
      forall R' : Relation A, inclusion R' R.
  End Meta_relations.
End Relation_definitions.

Definition minimal (A : Type) (R : Relation A) :=
  forall (S : Relation A), reflexive A S -> inclusion _ R S.

Section Extensionality_definition.
  Variable A B : Type.
  Variable R1 : Relation A.
  Variable R2 : Relation B.
  Definition extensional (f : A -> B) : Prop :=
    forall x y, R1 x y -> R2 (f x) (f y).
End Extensionality_definition.

Section Theorem_about_min_refl_relation.
  Variable A: Type.
  Variable R: Relation A.
  Hypothesis reflR : reflexive A R.
  Hypothesis minR : minimal A R.
  Theorem min_reflex_rel_is_equiv_and_ext :
    equality A R /.\
             forall (B : Type) (R2 : Relation B),
               equality B R2 -> forall f : A -> B,
                 extensional A B R R2 f.
  Proof.
    refine (conj' _ _).
    unfold equality.
    intuition.
    pose (S x y := R y x).
    pose (minR' := minR S).
    assert (reflexive A S).
    unfold reflexive.
    intros.
    intuition.
    pose (incl := minR S H).
    unfold symmetric.
    intuition.

    pose (T x y := forall z, R y z -> R x z).
    assert (reflexive A T).
    unfold reflexive, T.
    intros.
    intuition.

    pose (incl'' := minR T H).
    unfold transitive, T.

    intuition.
  Qed.
