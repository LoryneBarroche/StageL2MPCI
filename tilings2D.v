Require Import Bool.
Require Export ZArith.
Require Import Psatz.
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
From mathcomp Require Import seq. (* path fintype. *)
(* From mathcomp Require Import fingraph. *)


(** * Definitions *)

(** We define colors as natural numbers, and we set a few
    names to make things a bit more readable. *)

Definition type_Dec (X: Type) := forall (x y : X), {x = y}+{x <> y}.

Inductive colorX {X : Type}{p : type_Dec X} := ColorX: X -> colorX.


Inductive color := Color: nat -> color.


(** The equality of colors is of course decidable. *)

Definition color_eqb : color -> color -> bool.
Proof.
  intros t u. destruct t, u.
  exact (Nat.eqb n n0).
Defined.


Inductive color1D := Color1D: (list nat) -> color1D.


(** The equality of colors is of course decidable. *)

Definition color1D_eqb : color1D -> color1D -> bool.
Proof.
  intros t u. destruct t, u.
  destruct (list_eq_dec Nat.eq_dec l l0).
  exact true. exact false.
Defined.

Definition Black := Color 0.
Definition White := Color 1.
Definition Red   := Color 2.
Definition Green := Color 3.
Definition Blue  := Color 4.
(* etc... *)


(* Since we restrict ourselves to one dimensional tiles,
   tiles will only have two sides. *)

Inductive side := North | West | East | South.

Record tile := {
    north  : color;
    west  : color;
    east : color;
    south : color;
}.

(* A cell is just one place on the 1-dimensional line,
defined by its coordinate. *)

Inductive cell:= C : Z -> Z -> cell.

Definition configuration := cell -> tile.


(* So far, we say that colors are compatible if equal,
 but this might not be general enough afterwards. *)

Definition compatible_color : color -> color -> bool:=
  color_eqb.

Transparent compatible_color.
Hint Unfold compatible_color.

Definition compatible_north : tile -> tile -> bool:=
fun tile1 tile2 => color_eqb (@north tile1) (@south tile2).

Definition compatible_west : tile -> tile -> bool:=
fun tile1 tile2 => color_eqb (@west tile1) (@east tile2).

Definition compatible_east : tile -> tile -> bool:=
fun tile1 tile2 => color_eqb (@east tile1) (@west tile2).

Definition compatible_south : tile -> tile -> bool:=
fun tile1 tile2 => color_eqb (@south tile1) (@north tile2).

Print Z.eqb.

Infix "=z=":=Z.eqb (at level 75).

Print option.

Definition neighbour: cell -> cell -> option side:=
 fun c d =>
    match c with
    | C x1 y1 =>
        match d with
        | C x2 y2 =>
            if  (x2 =z= Z.pred x1) && (y2 =z= y1)
              then Some West
            else
              if (x2 =z= Z.succ x1) && (y2 =z= y1)
                then Some East
            else
              if (x2 =z= x1) && (y2 =z= Z.pred y1)
                then Some South
            else
              if (x2 =z= x1) && (y2 =z= Z.succ y1)
                then Some North
            else
              None
        end 
    end.
 
Inductive neighbour_spec: cell -> cell-> option side -> Type:=
|Neighbour_west (x1 y1 x2 y2:Z) (p:x2 = Z.pred x1) (q:y2 = y1): neighbour_spec (C x1 y1) (C x2  y2) (Some West)
|Neighbour_east x1 y1 x2 y2     (p:x2 = Z.succ x1) (q:y2 = y1): neighbour_spec (C x1 y1) (C x2 y2) (Some East)
|Neighbour_south x1 y1 x2 y2 (p:x2 = x1) (q:y2 = Z.pred y1): neighbour_spec (C x1 y1) (C x2 y2) (Some South)
|Neighbour_north x1 y1 x2 y2 (p:x2 = x1) (q:y2 = Z.succ y1): neighbour_spec (C x1 y1) (C x2 y2) (Some North)
|Neighbour_none x1 y1 x2 y2
(p : not ((x2 = Z.pred x1) /\ (y2 = y1)))
(q : not((x2 = Z.succ x1) /\ (y2 = y1)))
(r : not((x2 = x1) /\ (y2 = Z.pred y1)))
(s : not((x2 = x1) /\ (y2 = Z.succ y1))) : neighbour_spec (C x1 y1) (C x2 y2) None.


Lemma Zeq_is_neq_zeq_false : forall x y, x <> y -> (x =z= y) = false. 
Proof. 
  intros. assert (x = y <->  (x =z= y) = true).
  exact (Zeq_is_eq_bool x y). destruct (x =z= y). 
  - destruct H0. edestruct H. apply H1. auto. 
  - auto.
Qed.

Lemma Zeq_is_eq_zeq_true : forall x y, x = y -> (x =z= y) = true. 
Proof. 
  intros.
  assert (x = y <->  (x =z= y) = true).
  exact (Zeq_is_eq_bool x y). destruct (x =z= y). 
  - auto. 
  -  destruct H0. apply H0. auto.
Qed.

Lemma neighbourP:
  forall c1 c2, neighbour_spec c1 c2 (neighbour c1 c2).
Proof.
  intros. destruct c1 as [x1 y1], c2 as [x2 y2].
  unfold neighbour.
  - case:ifP. intro. 
  apply andb_prop in i. destruct i. apply Z.eqb_eq in H, H0.
  apply Neighbour_west. apply H. apply H0.
  - case:ifP. intros. 
  apply andb_prop in i. destruct i. apply Z.eqb_eq in H, H0.
  apply Neighbour_east. apply H. apply H0.
  - case:ifP. intros. 
  apply andb_prop in i. destruct i. apply Z.eqb_eq in H, H0.
  apply Neighbour_south. apply H. apply H0.
  - case:ifP. intros. 
  apply andb_prop in i. destruct i. apply Z.eqb_eq in H, H0.
  apply Neighbour_north. apply H. apply H0. 
  - intros. constructor.
    + intro. destruct H. rewrite H in n2. rewrite H0 in n2. 
      rewrite (Zeq_is_eq_zeq_true (Z.pred x1) (Z.pred x1)) in n2.
      rewrite (Zeq_is_eq_zeq_true (y1) (y1)) in n2.
      simpl in n2. discriminate. auto. auto.
    + intro. destruct H. 
    rewrite (Zeq_is_eq_zeq_true (x2) (Z.succ x1)) in n1.
    rewrite (Zeq_is_eq_zeq_true (y2) (y1)) in n1.
    discriminate. 
    auto. auto. 
+ Admitted.


Definition compatible: (P :configuration) (C1 : cell) (C2 : Cell) : bool:=
match neighbour C1 C2 with
| Some North => compatible_right (T c) (T d)
| Some South =>
| Some East =>
| Some West =>
| None => true
end. 
 
