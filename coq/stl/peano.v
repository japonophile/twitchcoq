(** this makes intros work *)
Declare ML Module "ltac_plugin".
Set Default Proof Mode "Classic".

(** annoying without this *)
Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Notation "A -> B" := (forall _ : A, B).

(** unit/empty is like True/False, but it's a set, not a prop *)
(** Inductive unit : Set := tt. *)
(** Inductive empty : Set :=. *)

(** bool has 2 items *)
(** the bool' was implied on the type of the items *)
Inductive bool' : Set :=
  | true : bool'
  | false : bool'.

(** False has no items *)
Inductive False : Prop :=.
Definition not (A : Prop) := A -> False.

(** True has one item *)
Inductive True : Prop := I : True.

(** Prop is better than Type *)
Inductive eqb' (x : bool') : bool' -> Prop :=
  | eqb'_refl : eqb' x x.

Theorem true_is_true : eqb' true true.
Proof.
  exact (eqb'_refl true).
Qed.

Definition check (e : bool') : Prop :=
  match e with
  | true => True
  | false => False
  end.

Theorem true_is_not_false : not (eqb' true false).
Proof.
  exact (eqb'_ind true check I false).
Qed.

Theorem false_implies_true : False -> True.
Proof.
  intros.
  induction H.
Qed.

Theorem true_not_implies_false : not (True -> False).
Proof.
  unfold not.
  intros.
  assert True.
  exact I.
  apply H in H0.
  apply H0.
Qed.

Print true_is_true.
Print true_is_not_false.
Print false_implies_true.
Print true_not_implies_false.

