Require Import Bool.
Require Export ZArith.
Require Import Psatz.
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
From mathcomp Require Import seq. (* path fintype. *)
(* From mathcomp Require Import fingraph. *)

Open Scope Z_scope. (* wahou ça change la vie !*)

(** * Definitions *)



(*****************************************************************************)
(************************************* In 2D *********************************)
(*****************************************************************************)



(** We define colors as natural numbers, and we set a few
    names to make things a bit more readable. *)


Inductive color := Color: nat -> color.


(** The equality of colors is of course decidable. *)

Definition color_eqb : color -> color -> bool.
Proof.
  intros t u. destruct t, u.
  exact (Nat.eqb n n0).
Defined.



Definition Black := Color 0.
Definition White := Color 1.
Definition Red   := Color 2.
Definition Green := Color 3.
Definition Blue  := Color 4.
(* etc... *)


(* tiles will have four sides. *)

Inductive side := North | West | South | East.

Record tile := {
    north  : color;
    west  : color;
    south : color;
    east : color;
}.

(* A cell is just one place on the 2-dimensional space,
defined by its coordinate. *)

Inductive cell:= C : Z -> Z -> cell.


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
  intros. apply Z.eqb_neq. exact H.
Qed.


Lemma Zeq_is_eq_zeq_true : forall x y, x = y -> (x =z= y) = true. 
Proof.
intros. apply Z.eqb_eq. exact H.
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
      exact H0.
      exact H. 
    + intro. destruct H. 
      rewrite (Zeq_is_eq_zeq_true (x2) (x1)) in n0.
      rewrite (Zeq_is_eq_zeq_true (y2) (Z.pred y1)) in n0. 
      discriminate.
      exact H0.
      exact H.
    + intro. destruct H.
      rewrite (Zeq_is_eq_zeq_true (x2) (x1)) in n.
      rewrite (Zeq_is_eq_zeq_true (y2) (Z.succ y1)) in n.
      discriminate.
      exact H0.
      exact H. 
Qed.

Definition configuration := cell -> tile.

Definition compatible (P : configuration) (C1 : cell) (C2 : cell) : bool :=
  match neighbour C1 C2 with
  | Some North => compatible_north (P C1) (P C2)
  | Some South => compatible_south (P C1) (P C2)
  | Some East => compatible_east (P C1) (P C2)
  | Some West => compatible_west (P C1) (P C2)
  | None => true
  end.


Definition valid_tiling (P:configuration): Prop := 
  forall C1 C2, compatible P C1 C2.


(*
Definition pattern := cell -> option tile. (* pk option tile déjà ?*)

Definition view:= cell -> bool.



  Definition conf_from_view : configuration -> view -> pattern:=
    fun T view c => if view c then Some (T c) else None. 

Definition conf_from_view (P : configuration) (view : view) (c : cell) : pattern:=
    if view c then Some (P c) 
    else None. *)
    
Record vec := {
  vx : Z;
  vy : Z
}.

Definition translation (c : cell) (u : vec) (k : Z) : cell :=
  match c with
  | C x y =>
      C (x + k * vx u) (y + k * vy u)
  end.

Definition weak_periodic (P:configuration): Prop :=
  exists (u : vec), (vx u <> 0)\/(vy u <> 0) /\
  (forall (c : cell), 
  forall (k : Z), 
  P (translation c u k) = P (c)).

Definition strong_periodic (P:configuration): Prop :=
  exists (u : vec), 
  (vx u <> 0)\/(vy u <> 0) /\ (
    exists (v : vec), 
    ((vx v <> 0)\/(vy v <> 0) /\ 
    ~(exists (a b : Z), ((a*(vx u) + b*vx v) = 0 /\ (a*(vy u) + b*vy v) = 0))) /\ (
      forall (c : cell), 
      forall (k1 k2 : Z),
        P (translation (translation c u k1) v k2) = P c)).




(****************************************************************************************)
(**************************************** In 1D *****************************************)
(****************************************************************************************)



(* We define 1D tiles where colors are now of type list nat. *)


Inductive color1D := Color1D: (list nat) -> color1D.


(** The equality of colors is decidable also in 1D. *)

Definition color1D_eqb : color1D -> color1D -> bool.
Proof.
  intros t u. destruct t, u.
  destruct (list_eq_dec Nat.eq_dec l l0).
  exact true. exact false.
Defined.

Inductive side1D :=  West1D | East1D.

Record tile1D := {
    east1D : color1D;
    west1D  : color1D;
    length1D : nat;
}.

Fixpoint length_list (l : list nat) : nat :=
match l with
| nil => 0
| cons a l1 => 1 + length_list l1
end.

Definition color1D_to_list (c : color1D) : list nat :=
  match c with 
  | Color1D l => l
  end.

Definition compatible_west1D : tile1D -> tile1D -> bool :=
fun tile1 tile2 =>
  andb 
  (
    andb
      (color1D_eqb (west1D tile1) (east1D tile2))
      (Nat.eqb
        (length_list (color1D_to_list (west1D tile1)))
        (length_list (color1D_to_list (east1D tile2))))
  )
  (Nat.eqb
    (length1D tile1)
    (length1D tile2)).

Definition compatible_east1D : tile1D -> tile1D -> bool :=
fun tile1 tile2 =>
  andb 
  (
    andb
      (color1D_eqb (east1D tile1) (west1D tile2))
      (Nat.eqb
        (length_list (color1D_to_list (east1D tile1)))
        (length_list (color1D_to_list (west1D tile2))))
  )
  (Nat.eqb
    (length1D tile1)
    (length1D tile2)).

(* les cellules ici sont un intervalle de Z le longueur length1D \in nat*)
(* on choisit par défaut que la coordonnée x est sur la première case de l'intervalle
donc x1 + n1 nous donne la coordonnée x2 de la cellule suivante et x1 - n0 nous donne
celle de la précédente, x0. *)
    
Inductive cell1D:= C1D : Z -> nat -> cell1D.


Definition neighbour1D: cell1D -> cell1D -> option side1D:=
 fun c d =>
    match c with
    | C1D x1 n1 =>
        match d with
        | C1D x2 n2 =>
            if  (x2 =z= x1 - Z.of_nat(n2))
              then Some West1D
            else
              if (x2 =z= x1 + Z.of_nat(n1))
                then Some East1D
            else
              None
        end 
    end.


Inductive neighbour1D_spec: cell1D -> cell1D-> option side1D -> Type:=
|Neighbour1D_west (x1 x2 : Z) (n1 n2 : nat) (p:x2 = x1 - Z.of_nat(n2)): neighbour1D_spec (C1D x1 n1) (C1D x2 n2) (Some West1D)
|Neighbour1D_east (x1 x2 : Z) (n1 n2 : nat) (p:x2 = x1 + Z.of_nat(n1)): neighbour1D_spec (C1D x1 n1) (C1D x2 n2) (Some East1D)
|Neighbour1D_none (x1 x2 : Z) (n1 n2 : nat)
(p : not (x2 = x1 - Z.of_nat(n2)))
(q : not(x2 = x1 + Z.of_nat(n1))): neighbour1D_spec (C1D x1 n1) (C1D x2 n2) None.

Lemma neighbour1DP:
  forall c1 c2, neighbour1D_spec c1 c2 (neighbour1D c1 c2).
Proof.
intros. destruct c1 as [x1 n1]. destruct c2 as [x2 n2]. unfold neighbour1D.
  - case:ifP. intro. 
  apply Z.eqb_eq in i. apply Neighbour1D_west. exact i.
  - case:ifP. intros.
  apply Z.eqb_eq in i. apply Neighbour1D_east. exact i.
  - intros. apply Neighbour1D_none. 
    + apply Z.eqb_neq in n0. exact n0.
    + apply Z.eqb_neq in n. exact n.
Qed.


Definition configuration1D := cell1D -> tile1D.

Definition valid_configuration1D (P : configuration1D) : Prop :=
  forall x n,
    length1D (P (C1D x n)) = n.

Definition compatible1D (P : configuration1D) (C1 C2 : cell1D) : bool :=
  match neighbour1D C1 C2 with
  | Some East1D => compatible_east1D (P C1) (P C2)
  | Some West1D => compatible_west1D (P C1) (P C2)
  | None => true
  end. 


Definition valid_tiling1D (P:configuration1D): Prop := 
  forall C1 C2, compatible1D P C1 C2.



(****************************************************************************************)
(**********************************Counter example***************************************)
(****************************************************************************************)

Lemma eq_pair : forall u v : (Z * Z), u.1 = v.1 -> u.2 = v.2 -> u = v.
Proof.
    apply injective_projections.
Qed.

 
Definition vecI : Set := Z * Z. 

Definition cellI : Set := Z * Z.

Definition configurationI := cellI -> tile.

Definition translationI (c : cellI) (u : vecI) (k : Z) : cellI :=
       (c.1 + k * u.1 , c.2 + k * u.2).

Definition is_VP (v:vecI) (P: configurationI) :=   
  forall c,  forall k,  P (translationI c v k) = P c.

Definition sum_vec (u v : vecI) : vecI := (u.1 + v.1, u.2 + v.2).

Notation "u + v" := (sum_vec u v).

Lemma translationI_sum : forall c u v k, translationI c (u + v) k 
= translationI (translationI c u k) v k.
Proof.
intros.
unfold translationI. simpl. apply eq_pair.
- simpl. lia.
- simpl. lia.
Qed.

Lemma sum_VP : forall P u v, is_VP u P -> is_VP v P -> is_VP (u + v) P.
Proof.
intros.
unfold is_VP. intros.
rewrite translationI_sum.
unfold is_VP in H. rewrite H0. rewrite H. reflexivity.
Qed.

Definition mult_vec (k:Z) (u : vecI) : vecI := (k * u.1,k * u.2).

Notation "k * u" := (mult_vec k u).

Lemma translationI_prod : forall c u k' k, translationI c (k'*u) k = translationI c u (k * k').
Proof.
intros. unfold translationI. simpl. apply eq_pair.
- simpl. lia.
- simpl. lia.
Qed.

Lemma prod_VP : forall P u k, is_VP u P -> is_VP (k * u) P.
Proof.
intros. unfold is_VP. intros.
unfold is_VP in H. rewrite translationI_prod. rewrite H. reflexivity.
Qed.

Lemma counter_example : forall P : configurationI, is_VP (1,1) P 
-> (forall a, a <> 0 -> not (is_VP (a ,0) P)) -> forall u, (u.1) <> (u.2) -> not(is_VP u P). 
Proof.
intros. intro. apply (H0 (u.1 - u.2)). lia. 
replace (u.1 - u.2, 0) with (u + (-u.2) * (1,1)).
- eapply sum_VP. exact H2. eapply prod_VP. exact H.
- unfold sum_vec. unfold mult_vec. simpl. apply injective_projections.
  + simpl. lia.
  + simpl. lia.
Qed. 

(** we prove that if P is Sp then it has a VP colinear with (1,0)**)
      
Definition SP (P:configurationI): Prop :=
  exists u, u <> (0,0) /\ 
    exists v, 
      v <> (0,0) /\ (v.2 *  u.1 -  u.2 *  v.1 <> 0) /\ 
       is_VP u P /\ is_VP v P.


Lemma SP_to_VP : forall P, SP P -> exists a, a<> 0 /\ is_VP (a,0) P.
Proof.
intros. destruct H as [u [Hu [v [Hv [Hnc [HuVP HvVP]]]]]].
  exists (v.2 * u.1 - u.2 * v.1).  
  split. exact Hnc. 
  replace (v.2 * u.1 - u.2 * v.1, 0) with (v.2 * u + (-u.2) * v). 
  - eapply sum_VP. eapply prod_VP. exact HuVP. 
    eapply prod_VP. exact HvVP. 
  - unfold sum_vec. unfold mult_vec. simpl.
    apply injective_projections.
    + simpl. lia. 
    + simpl. lia. 
Qed. 
