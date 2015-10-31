(* Propositional Bools *)
Inductive True' : Prop :=
  I' : True'.
Inductive False' : Prop := .
Definition not' (A : Prop) := A -> False'.
Notation "~ A" := (not' A) (at level 75, right associativity) : Prelude_scope.

Definition prodAbs (x : False') (A : Set) : A.
Proof.
  intuition.
Qed.

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

Definition case' (S : Empty -> Set) (e : Empty) : S e.
Proof.
  intuition.
Qed.

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
    Theorem zero_neutral_right : forall n : Nat, n + zero == n.
    Proof.
      intros n.
      unfold plus'.
      simpl.
      exact (id n).
    Qed.

    Theorem zero_neutral_left : forall n : Nat, zero + n == n.
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

    Theorem comm_plus : forall (a b : Nat), a + b == b + a.
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

    Theorem assoc_plus : forall a b c : Nat, (a + b) + c == a + (b + c).
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

    Theorem succr_plus : forall a b : Nat, succ (a + b) == a + succ b.
    Proof.
      intros a b.
      elim a.
      exact (id (zero + succ b)).

      intros n0 ind_hyp0.
      exact (id (succ n0 + succ b)).
    Qed.

    Theorem succl_plus : forall a b : Nat, succ (a + b) == succ a + b.
    Proof.
      intros a b.
      rewrite (comm_plus (succ a) b).
      rewrite (comm_plus a b).
      exact (succr_plus b a).
    Qed.

    Theorem transfer_plus : forall a b : Nat, succ a + b == a + succ b.
    Proof.
      intros a b.
      rewrite <- (succl_plus a b).
      rewrite <- (succr_plus a b).
      exact (id _).
     Qed.

    Theorem mul_zero_kills : forall a : Nat, zero * a == zero.
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

    Theorem mul_zero_killsr : forall a : Nat, a * zero == zero.
    Proof.
      intros.
      elim a.
      exact (id zero).
      intros.
      unfold mul'.
      unfold mul' in H.
      simpl.
      exact (id zero).
    Qed.

    Theorem mul_one : forall a : Nat, a * succ zero == a.
    Proof.
      intros a.
      elim a.
      rewrite (mul_zero_kills (succ zero)).
      exact (id zero).
      intros.
      unfold mul'.
      simpl.
      exact (id _).
    Qed.

    Theorem succr_mul : forall a b : Nat, a * succ b == a + a * b.
    Proof.
      intros.
      elim b.
      rewrite (mul_zero_killsr a).
      unfold mul'.
      simpl.
      exact (id a).

      intros.
      unfold mul'.
      simpl.
      exact (id _).
    Qed.

    Theorem succl_mul : forall a b : Nat, Id (succ a * b) (b + a * b).
    Proof.
      intros.
      elim b.
      exact (id zero).
      intros n0 ind_hyp0.
      rewrite (succr_mul a n0).
      rewrite (succr_mul (succ a) n0).
      rewrite ind_hyp0.
      rewrite <- (assoc_plus (succ a) n0 (a * n0)).
      rewrite <- (assoc_plus (succ n0) a (a * n0)).
      rewrite (comm_plus (succ a) n0).
      rewrite (transfer_plus n0 a).
      exact (id _).
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
      rewrite (succl_mul n (b + c)).
      rewrite (succl_mul n b).
      rewrite (succl_mul n c).
      rewrite H.
      rewrite (assoc_plus b (n * b) (c + n * c)).
      rewrite <- (assoc_plus (n * b) c (n * c)).
      rewrite (comm_plus (n * b) c).
      rewrite (assoc_plus b c (n * b + n * c)).
      rewrite (assoc_plus c (n * b) (n * c)).
      exact (id _).
    Qed.

    Theorem comm_mul : forall a b c : Nat, Id (a * b) (b * a).
    Proof.
      intros a b c.
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
      rewrite (mul_zero_kills (succ n)).
      rewrite (mul_zero_killsr (succ n)).
      exact (id zero).

      (* shift1 *)
      intros.
      rewrite (succl_mul n b).
      rewrite (succr_mul b n).
      rewrite H.
      exact (id _).
    Qed.

  End Nat_Lemmas.
End Natural_Numbers.

Inductive Pi (A: Set) (B : A -> Set) : Set :=
  lambda: (forall x: A, B x) -> Pi A B.

Definition apply' (A : Set) (B : A -> Set) (g : Pi A B) (x : A) : B x :=
  match g with
    lambda f => f x
  end.

Notation "A ~> B" := (Pi A (fun _ => B)) (at level 90, right associativity) : Prelude_scope.
Notation "~' A"   := (A ~> Empty) (at level 75, right associativity).

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

(* forall theorem ! *)
Theorem forall_exists :
  forall (A:Set) (B : A -> Set),
    (Pi A (fun x => ~'(B x))) ~> ~'(Sigma A B).
Proof.
  intros A B.
  unfold lambda'.
  refine (lambda' (Pi A (fun x : A => ~' B x)) (~' Sigma A B) _).
  intros C.
  refine (lambda' (Sigma A B) Empty _).
  intros D.
  pose (x := fst' A B D).
  pose (y := snd' A B D).
  pose (prod := apply' _ _ C x).
  intuition.
  pose (realb := apply' _ _ prod y).
  intuition.
Qed.



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


Definition head''' (A : Set) (l: List A) (proof : l /= null A) : A.
Proof.
  unfold not' in proof.
  induction l.
  intuition.
  exact a.
Qed.

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
    Definition minimal : Prop :=
      forall R' : Relation A, inclusion R R'.
    Definition extensional
               (B : Type)
               (R2 : Relation B)
               (f : A -> B) : Prop :=
      forall x y, R x y -> R2 (f x) (f y).
  End Meta_relations.
End Relation_definitions.

Section Theorem_about_min_refl_relation.
  Variable A: Type.
  Variable R: Relation A.
  Hypothesis reflR : reflexive A R.
  Hypothesis minR : forall S : Relation A, reflexive A S -> inclusion A R S.

  Theorem min_reflex_is_equiv :
    equality A R.
  Proof.
    split.
    unfold equality.
    intuition.

    pose (S a b := R b a).
    pose (minR' := minR S).
    assert (reflexive A S).
    unfold reflexive.
    intros a0.
    intuition.
    pose (incl := minR S H).
    unfold symmetric.
    intuition.

    pose (T x y := forall z, R y z -> R x z).
    assert (reflexive A T).
    unfold reflexive, T.
    intros.
    exact H.

    pose (incl := minR T H).
    unfold inclusion in incl.
    unfold transitive, T.
    intros.
    exact (incl a b H0 c H1).
  Qed.

  Theorem min_reflex_is_extensional :
    forall (B : Type) (R2 : Relation B),
      equality B R2 -> forall f : A -> B,
        extensional A R B R2 f.
  Proof.
    unfold extensional.
    intros.

    pose (F x y := R2 (f x) (f y)).
    assert (reflexive A F).
    unfold reflexive.
    intros.
    unfold equality in H.
    assert (reflexive B R2).
    intuition.
    unfold reflexive in H1.
    exact (H1 (f a)).

    unfold reflexive in minR.
    unfold inclusion in minR.
    exact (minR F H1 x y H0).
  Qed.

  Theorem rels_equality_is_equivalence : forall T:Type, equality (Relation T) (equal_rels T).
  Proof.
    unfold equality.
    intros.
    intuition.

    unfold reflexive.
    intros.
    unfold equal_rels.
    intuition.

    unfold inclusion.
    intros.
    exact H.

    unfold inclusion.
    intros.
    exact H.

    unfold symmetric.
    intros.
    unfold equal_rels.
    intuition.
    unfold inclusion.
    intros.
    unfold equal_rels in H.
    intuition.

    unfold inclusion.
    intros.
    unfold equal_rels in H.
    intuition.

    unfold transitive.
    intros.
    unfold equal_rels.
    unfold equal_rels in H, H0.
    intuition.
    unfold inclusion.
    unfold inclusion in H, H1, H2, H3.
    intros.
    intuition.

    unfold inclusion.
    intros.
    unfold inclusion.
    unfold inclusion in H, H1, H2, H3.
    intros.
    intuition.
  Qed.
End Theorem_about_min_refl_relation.


Section Null_is_not_one.
  Variable A : Type.
  Theorem id_refl : reflexive A Id.
  Proof.
    unfold reflexive.
    intros.
    exact (id a).
  Qed.
  Theorem null_not_one : zero /= succ(zero).
  Proof.
    admit.
  Qed.
End Null_is_not_one.

Section TT_choice.
  Variable S : Type.
  Variable T : Type.
  Definition Relation' (A : Type) (B : Type) := A -> B -> Prop.
  Variable R : Relation' S T.
  Theorem tt_choice_axiom:
    (Pi S (fun x => Sigma T (fun y => R x y)))
      ->
      (Sigma (S ~> T) (fun (f : S ~> T) =>
                         Pi S (fun x => R x (apply'' S T f x)))).
  Proof.
    intro z.
    pose (zapp1foo := fun (x : S) => fst' _ _
                                       (apply' _ _
                                          z x)).
    pose (zapp1 := lambda' S T zapp1foo).
    pose (zapp2foo := fun (x : S) => snd' _ _
                                        (apply' _ _
                                                z x)).
    pose (zapp2 := lambda' _ _ zapp2foo).
    pose (try1 := pair
                    (S ~> T)
                    (fun (f : S ~> T) => Pi S (fun x => R x (apply'' S T f x)))
                    (fun (x : S) => fst'
                                      _ _
                                      (apply'' S T z x))
                    (fun y => snd' (apply'' _ _ z y))).
  Qed.
End TT_choice.