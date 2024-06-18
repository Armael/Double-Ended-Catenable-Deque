From Coq Require Import ssreflect.
From Coq Require Import Program List ZArith Lia.
Import ListNotations.
From Equations Require Import Equations.
From Hammer Require Import Tactics.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import ncdeque.
From Deque Require Import buffer.

Set Equations Transparent.

(* Types *)

Inductive preferred_child : Type :=
  | Preferred : bool -> bool -> preferred_child.

Notation preferred_left := (Preferred true false).
Notation preferred_right := (Preferred false true).

Derive NoConfusion for preferred_child.

Inductive kind : Type := Only | Left | Right.

(* Here, [green_hue], [yellow_hue], [orange_hue] and [red_hue] will be utilized 
   to generate the colors essential for our program. They function as boolean 
   variables, indicating whether or not a specific hue is present in our color. *)

Inductive green_hue  : Type := SomeGreen  | NoGreen.
Inductive yellow_hue : Type := SomeYellow | NoYellow.
Inductive orange_hue : Type := SomeOrange | NoOrange.
Inductive red_hue    : Type := SomeRed    | NoRed.

(* Colors are generated through the constructor [Mix], which accepts amount 
   of each hue as arguments. *)

Inductive color : Type :=
  | Mix : green_hue -> yellow_hue -> orange_hue -> red_hue -> color.

(* In order for [Equations] to work on hues and colors, instances of 
   [NoConfusion] are added to these types. *)

Derive NoConfusion for kind.
Derive NoConfusion for green_hue.
Derive NoConfusion for yellow_hue.
Derive NoConfusion for orange_hue.
Derive NoConfusion for red_hue.
Derive NoConfusion for color.

(* Some basic colors that we'll need. *)

Notation green := (Mix SomeGreen NoYellow NoOrange NoRed).
Notation yellow := (Mix NoGreen SomeYellow NoOrange NoRed).
Notation yellorange := (Mix NoGreen SomeYellow SomeOrange NoRed).
Notation orange := (Mix NoGreen NoYellow SomeOrange NoRed).
Notation red := (Mix NoGreen NoYellow NoOrange SomeRed).

(* Types for general prefix and suffix, they are simply aliases for buffer.t. *)

Definition prefix' := buffer.t.
Definition suffix' := buffer.t.

Inductive small_triple_size : nat -> nat -> kind -> Type :=
  | SOnly {q : nat} : small_triple_size (S q) 0 Only
  | SLeft {q : nat} : small_triple_size (5 + q) 2 Left
  | SRight {q : nat} : small_triple_size 2 (5 + q) Right.

Inductive big_triple_size : nat -> nat -> nat -> kind -> Type :=
  | BOnly {p qp qs : nat} : big_triple_size p (p + qp) (p + qs) Only
  | BLeft {p q : nat} : big_triple_size p (p + q) 2 Left
  | BRight {p q : nat} : big_triple_size p 2 (p + q) Right.

Inductive stored_triple (A : Type) : nat -> Type :=
  | ST_ground : A -> stored_triple A 0
  | ST_small {lvl q : nat} : 
      prefix' (stored_triple A lvl) (3 + q) -> 
      stored_triple A (S lvl)
  | ST_triple {lvl qp qs : nat} {C : color} :
      prefix' (stored_triple A lvl) (3 + qp) -> 
      cdeque A (S lvl) C -> 
      suffix' (stored_triple A lvl) (3 + qs) -> 
      stored_triple A (S lvl)

with triple (A : Type) : nat -> nat -> bool -> kind -> kind -> color -> Type :=
  | Hole {lvl : nat} {K : kind} : 
      triple A lvl 0 true K K yellorange
  | Small {lvl qp qs : nat} {K : kind} : 
      prefix' (stored_triple A lvl) qp -> 
      suffix' (stored_triple A lvl) qs ->
      small_triple_size qp qs K ->
      triple A lvl 0 false K K green
  | Green {lvl qp qs : nat} {K : kind} {G R} :
      prefix' (stored_triple A lvl) qp ->
      non_empty_cdeque A (S lvl) (Mix G NoYellow NoOrange R) ->
      suffix' (stored_triple A lvl) qs ->
      big_triple_size 8 qp qs K ->
      triple A lvl 0 false K K green
  | Yellow {lvl len qp qs : nat} {K1 K2 : kind} :
      prefix' (stored_triple A lvl) qp ->
      packet A (S lvl) len preferred_left K2 ->
      suffix' (stored_triple A lvl) qs ->
      big_triple_size 7 qp qs K1 ->
      triple A lvl (S len) false K1 K2 yellow
  | Orange {lvl len qp qs : nat} {K1 K2 : kind} :
      prefix' (stored_triple A lvl) qp ->
      packet A (S lvl) len preferred_right K2 ->
      suffix' (stored_triple A lvl) qs ->
      big_triple_size 6 qp qs K1 ->
      triple A lvl (S len) false K1 K2 orange
  | Red {lvl qp qs : nat} {K : kind} :
      prefix' (stored_triple A lvl) qp ->
      non_empty_cdeque A (S lvl) green ->
      suffix' (stored_triple A lvl) qs ->
      big_triple_size 5 qp qs K ->
      triple A lvl 0 false K K red

with packet (A : Type) : nat -> nat -> preferred_child -> kind -> Type :=
  | Only_child {lvl len : nat} {is_hole : bool} {K : kind} {Y O} {left right : bool} :
      triple A lvl len is_hole Only K (Mix NoGreen Y O NoRed) ->
      packet A lvl len (Preferred left right) K
  | Left_child {lvl len : nat} {is_hole : bool} {K : kind} {Y O C} :
      triple A lvl len is_hole Left K (Mix NoGreen Y O NoRed) ->
      path A lvl Right C ->
      packet A lvl len preferred_left K
  | Right_child {lvl len : nat} {is_hole : bool} {K : kind} {Y O} :
      path A lvl Left green ->
      triple A lvl len is_hole Right K (Mix NoGreen Y O NoRed) ->
      packet A lvl len preferred_right K

with path (A : Type) : nat -> kind -> color -> Type := 
  | Children {lvl len nlvl : nat} {is_hole : bool} {K1 K2 : kind} {G Y O R} :
      triple A lvl len is_hole K1 K2 (Mix NoGreen Y O NoRed) ->
      triple A nlvl 0 false K2 K2 (Mix G NoYellow NoOrange R) ->
      nlvl = len + lvl ->
      path A lvl K1 (Mix G NoYellow NoOrange R)

with non_empty_cdeque (A : Type) : nat -> color -> Type :=
  | Only_path {lvl : nat} {G R} :
      path A lvl Only (Mix G NoYellow NoOrange R) ->
      non_empty_cdeque A lvl (Mix G NoYellow NoOrange R)
  | Pair_green {lvl : nat} :
      path A lvl Left green ->
      path A lvl Right green ->
      non_empty_cdeque A lvl green
  | Pair_red {lvl : nat} {Cl Cr : color} :
      path A lvl Left Cl ->
      path A lvl Right Cr ->
      non_empty_cdeque A lvl red

with cdeque (A : Type) : nat -> color -> Type :=
  | Empty {lvl : nat} : cdeque A lvl green
  | NonEmpty {lvl G R} : 
      non_empty_cdeque A lvl (Mix G NoYellow NoOrange R) ->
      cdeque A lvl (Mix G NoYellow NoOrange R).

Arguments ST_ground {A}.
Arguments ST_small {A lvl q}.
Arguments ST_triple {A lvl qp qs C}.

Arguments Hole {A lvl K}.
Arguments Small {A lvl qp qs K}.
Arguments Green {A lvl qp qs K G R}.
Arguments Yellow {A lvl len qp qs K1 K2}.
Arguments Orange {A lvl len qp qs K1 K2}.
Arguments Red {A lvl qp qs K}.

Arguments Only_child {A lvl len is_hole K Y O left right}.
Arguments Left_child {A lvl len is_hole K Y O C}.
Arguments Right_child {A lvl len is_hole K Y O}.

Arguments Children {A lvl len nlvl is_hole K1 K2 G Y O R}.

Arguments Only_path {A lvl G R}.
Arguments Pair_green {A lvl}.
Arguments Pair_red {A lvl Cl Cr}.

Arguments Empty {A lvl}.
Arguments NonEmpty {A lvl G R}.

Definition prefix (A : Type) (lvl : nat) := prefix' (stored_triple A lvl).
Definition suffix (A : Type) (lvl : nat) := suffix' (stored_triple A lvl).

Definition only_triple (A : Type) (lvl len : nat) (is_hole : bool) := 
  triple A lvl len is_hole Only.
Definition left_triple (A : Type) (lvl len : nat) (is_hole : bool) := 
  triple A lvl len is_hole Left.
Definition right_triple (A : Type) (lvl len : nat) (is_hole : bool) := 
  triple A lvl len is_hole Right.

Inductive pref_left (A : Type) (lvl : nat) : Type :=
  | Pref_left {len nlvl K G R} : 
      packet A lvl len preferred_left K ->
      triple A nlvl 0 false K K (Mix G NoYellow NoOrange R) ->
      nlvl = len + lvl ->
      pref_left A lvl.
Arguments Pref_left {A lvl len nlvl K G R}.

Inductive pref_right (A : Type) (lvl : nat) : Type :=
  | Pref_right {len nlvl K G R} :
      packet A lvl len preferred_right K ->
      triple A nlvl 0 false K K (Mix G NoYellow NoOrange R) ->
      nlvl = len + lvl ->
      pref_right A lvl.
Arguments Pref_right {A lvl len nlvl K G R}.

Definition buffer_12 (A : Type) (lvl : nat) : Type := stored_triple A lvl * vector (stored_triple A lvl) 1.

Inductive path_attempt (A : Type) (lvl : nat) : kind -> color -> Type :=
  | ZeroSix {K : kind} {C : color} : 
      vector (stored_triple A lvl) 6 -> path_attempt A lvl K C
  | Ok {K : kind} {C : color} : 
      path A lvl K C -> path_attempt A lvl K C
  | Any {K : kind} {C : color} :
      path A lvl K C -> path_attempt A lvl K red.
Arguments ZeroSix {A lvl K C}.
Arguments Ok {A lvl K C}.
Arguments Any {A lvl K C}.

Inductive path_uncolored (A : Type) (lvl : nat) (K : kind) : Type :=
  | Six : stored_triple A lvl -> stored_triple A lvl -> stored_triple A lvl ->
          stored_triple A lvl -> stored_triple A lvl -> stored_triple A lvl ->
          path_uncolored A lvl K
  | AnyColor {C : color} : path A lvl K C -> path_uncolored A lvl K.
Arguments Six {A lvl K}.
Arguments AnyColor {A lvl K C}.

Inductive sdeque (A : Type) (lvl : nat) : Type :=
  Sd : forall (C : color), cdeque A lvl C -> sdeque A lvl.
Arguments Sd {A lvl C}.

Inductive unstored (A : Type) (lvl : nat) : Type :=
  | Unstored {q : nat} : 
      prefix A lvl (3 + q) -> sdeque A (S lvl) -> unstored A lvl.
Arguments Unstored {A lvl q}.

Inductive sandwich (A : Type) (lvl : nat) : Type :=
  | Alone : stored_triple A lvl -> sandwich A lvl
  | Sandwich : 
      stored_triple A lvl -> sdeque A lvl -> stored_triple A lvl ->
      sandwich A lvl.
Arguments Alone {A lvl}.
Arguments Sandwich {A lvl}.

Inductive unstored_sandwich (A : Type) (lvl : nat) : Type :=
  | Unstored_alone {q : nat} :
      prefix A lvl (3 + q) -> unstored_sandwich A lvl
  | Unstored_sandwich {qp qs : nat} :
      prefix A lvl (3 + qp) -> 
      sdeque A (S lvl) ->
      suffix A lvl (3 + qs) ->
      unstored_sandwich A lvl.
Arguments Unstored_alone {A lvl q}.
Arguments Unstored_sandwich {A lvl qp qs}.

Inductive deque (A : Type) : Type :=
  T : cdeque A 0 green -> deque A.
Arguments T {A}.

(* Models *)

Set Equations Transparent.

Fixpoint path_seq {A lvl K C} (p : path A lvl K C) {struct p} : list A :=
  let ne_cdeque_seq {B lvl C} (cd : non_empty_cdeque B lvl C) : list B :=
    match cd with
    | Only_path p => path_seq p
    | Pair_green pl pr => path_seq pl ++ path_seq pr
    | Pair_red pl pr => path_seq pl ++ path_seq pr
    end in
  let cdeque_seq {B lvl C} (cd : cdeque B lvl C) : list B :=
    match cd with
    | Empty => []
    | NonEmpty necd => ne_cdeque_seq necd
    end in 
  let fix stored_triple_seq {B lvl} (st : stored_triple B lvl) {struct st} : list B :=
    let buffer_seq {B lvl q} (b : buffer.t (stored_triple B lvl) q) : list B := 
      map_buffer (@stored_triple_seq B) b in
    match st with
    | ST_ground b => [b]
    | ST_small p => buffer_seq p
    | ST_triple p cd s => buffer_seq p ++ cdeque_seq cd ++ buffer_seq s
    end in 
  let buffer_seq {B lvl q} (b : buffer.t (stored_triple B lvl) q) : list B := 
    map_buffer (@stored_triple_seq B) b in
  let fix triple_front_seq {B lvl len is_hole K1 K2 C} (t : triple B lvl len is_hole K1 K2 C) {struct t} : list B :=
    let packet_front_seq {B lvl len pc K} (pkt : packet B lvl len pc K) : list B := 
      match pkt with 
      | Only_child t => triple_front_seq t
      | Left_child t _ => triple_front_seq t
      | Right_child p t => path_seq p ++ triple_front_seq t
      end in 
    match t with 
    | Hole => []
    | Small p _ _ => buffer_seq p
    | Green p cd _ _ => buffer_seq p ++ ne_cdeque_seq cd
    | Yellow p pkt _ _ => buffer_seq p ++ packet_front_seq pkt
    | Orange p pkt _ _ => buffer_seq p ++ packet_front_seq pkt
    | Red p cd _ _ => buffer_seq p ++ ne_cdeque_seq cd 
    end in
  let fix triple_rear_seq {B lvl len is_hole K1 K2 C} (t : triple B lvl len is_hole K1 K2 C) {struct t} : list B :=
    let packet_rear_seq {B lvl len pc K} (pkt : packet B lvl len pc K) : list B :=
      match pkt with 
      | Only_child t => triple_rear_seq t
      | Left_child t p => triple_rear_seq t ++ path_seq p
      | Right_child _ t => triple_rear_seq t
      end in
    match t with 
    | Hole => []
    | Small _ s _ => buffer_seq s
    | Green _ _ s _ => buffer_seq s
    | Yellow _ pkt s _ => packet_rear_seq pkt ++ buffer_seq s
    | Orange _ pkt s _ => packet_rear_seq pkt ++ buffer_seq s
    | Red _ _ s _ => buffer_seq s 
    end in 
  match p with 
  | Children natur adopt _ => 
    triple_front_seq natur ++ triple_front_seq adopt ++
    triple_rear_seq adopt ++ triple_rear_seq natur
  end.

Equations ne_cdeque_seq {A lvl C} : non_empty_cdeque A lvl C -> list A :=
ne_cdeque_seq (Only_path p) := path_seq p;
ne_cdeque_seq (Pair_green pl pd) := path_seq pl ++ path_seq pd;
ne_cdeque_seq (Pair_red pl pd) := path_seq pl ++ path_seq pd.

Equations cdeque_seq {A lvl C} : cdeque A lvl C -> list A :=
cdeque_seq Empty := [];
cdeque_seq (NonEmpty cd) := ne_cdeque_seq cd.

Fixpoint stored_triple_seq {A} {lvl : nat} (st : stored_triple A lvl) {struct st} : list A := 
  let buffer_seq {lvl q} (b : buffer.t (stored_triple A lvl) q) : list A := 
    map_buffer (@stored_triple_seq A) b in
  match st with
  | ST_ground a => [a]
  | ST_small p => buffer_seq p
  | ST_triple p cd s => buffer_seq p ++ cdeque_seq cd ++ buffer_seq s
  end.

Equations buffer_seq {A lvl q} : buffer.t (stored_triple A lvl) q -> list A :=
buffer_seq p := concat (map stored_triple_seq (buffer.seq p)).

Definition path_buffer_seq {A lvl q} (b : buffer.t (stored_triple A lvl) q) : list A := 
  map_buffer ((fix stored_triple_seq (B : Type) (lvl : nat) (st : stored_triple B lvl) {struct st} : list B := match st with
  | ST_ground b => [b]
  | @ST_small _ lvl' q p => map_buffer (stored_triple_seq B) p
  | @ST_triple _ lvl' qp qs _ p cd s => 
    map_buffer (stored_triple_seq B) p ++ 
    cdeque_seq cd ++ 
    map_buffer (stored_triple_seq B) s
  end) A) b.

Lemma correct_path_buffer_seq {A lvl q} (b : buffer.t (stored_triple A lvl) q) :
  path_buffer_seq b = buffer_seq b.
Proof.
  unfold path_buffer_seq; simp buffer_seq. 
  rewrite buffer.correct_mapping. reflexivity.
Qed.

Fixpoint triple_front_seq {A lvl len is_hole K1 K2 C} (t : triple A lvl len is_hole K1 K2 C) : list A :=
  let packet_front_seq {lvl len pc K} (pkt : packet A lvl len pc K) : list A :=
    match pkt with
    | Only_child t => triple_front_seq t
    | Left_child t _ => triple_front_seq t
    | Right_child p t => path_seq p ++ triple_front_seq t
    end in
  match t with
  | Hole => []
  | Small p _ _ => path_buffer_seq p
  | Green p cd _ _ => path_buffer_seq p ++ ne_cdeque_seq cd
  | Yellow p pkt _ _ => path_buffer_seq p ++ packet_front_seq pkt
  | Orange p pkt _ _ => path_buffer_seq p ++ packet_front_seq pkt
  | Red p cd _ _ => path_buffer_seq p ++ ne_cdeque_seq cd
  end.

Equations packet_front_seq {A lvl len pc K} : packet A lvl len pc K -> list A :=
packet_front_seq (Only_child t) := triple_front_seq t;
packet_front_seq (Left_child t _) := triple_front_seq t;
packet_front_seq (Right_child p t) := path_seq p ++ triple_front_seq t.

Fixpoint triple_rear_seq {A lvl len is_hole K1 K2 C} (t : triple A lvl len is_hole K1 K2 C) : list A :=
  let packet_rear_seq {lvl len pc K} (pkt : packet A lvl len pc K) : list A :=
    match pkt with
    | Only_child t => triple_rear_seq t
    | Left_child t p => triple_rear_seq t ++ path_seq p
    | Right_child _ t => triple_rear_seq t
    end in
  match t with
  | Hole => []
  | Small _ s _ => path_buffer_seq s
  | Green _ _ s _ => path_buffer_seq s
  | Yellow _ pkt s _ => packet_rear_seq pkt ++ path_buffer_seq s
  | Orange _ pkt s _ => packet_rear_seq pkt ++ path_buffer_seq s
  | Red _ _ s _ => path_buffer_seq s
  end.

Equations packet_rear_seq {A lvl len pc K} : packet A lvl len pc K -> list A :=
packet_rear_seq (Only_child t) := triple_rear_seq t;
packet_rear_seq (Left_child t p) := triple_rear_seq t ++ path_seq p;
packet_rear_seq (Right_child _ t) := triple_rear_seq t.

Equations triple_seq {A lvl len is_hole K1 K2 C} : 
  triple A lvl len is_hole K1 K2 C -> list A := 
triple_seq t := triple_front_seq t ++ triple_rear_seq t.

Equations pref_left_seq {A lvl} : pref_left A lvl -> list A :=
pref_left_seq (Pref_left pkt t eq_refl) := packet_front_seq pkt ++ triple_seq t ++ packet_rear_seq pkt.

Equations pref_right_seq {A lvl} : pref_right A lvl -> list A :=
pref_right_seq (Pref_right pkt t eq_refl) := packet_front_seq pkt ++ triple_seq t ++ packet_rear_seq pkt.

Equations buffer_12_seq {A lvl} : buffer_12 A lvl -> list A :=
buffer_12_seq (x, v) := stored_triple_seq x ++ concat (map stored_triple_seq (vector_seq v)).

Equations path_attempt_seq {A lvl K C} : path_attempt A lvl K C -> list A :=
path_attempt_seq (ZeroSix v) := concat (map stored_triple_seq (vector_seq v));
path_attempt_seq (Ok p) := path_seq p;
path_attempt_seq (Any p) := path_seq p.

Equations path_uncolored_seq {A lvl K} : path_uncolored A lvl K -> list A :=
path_uncolored_seq (Six x1 x2 x3 x4 x5 x6) := 
  stored_triple_seq x1 ++ stored_triple_seq x2 ++ stored_triple_seq x3 ++
  stored_triple_seq x4 ++ stored_triple_seq x5 ++ stored_triple_seq x6;
path_uncolored_seq (AnyColor p) := path_seq p. 

Equations sdeque_seq {A lvl} : sdeque A lvl -> list A :=
sdeque_seq (Sd cd) := cdeque_seq cd.

Equations unstored_front_seq {A lvl} : unstored A lvl -> list A :=
unstored_front_seq (Unstored p _) := buffer_seq p.

Equations unstored_rear_seq {A lvl} : unstored A lvl -> list A :=
unstored_rear_seq (Unstored _ sd) := sdeque_seq sd.

Equations sandwich_seq {A lvl} : sandwich A lvl -> list A :=
sandwich_seq (Alone x) := stored_triple_seq x;
sandwich_seq (Sandwich xl sd xr) :=
  stored_triple_seq xl ++ sdeque_seq sd ++ stored_triple_seq xr.

Equations unstored_sandwich_seq {A lvl} : unstored_sandwich A lvl -> list A :=
unstored_sandwich_seq (Unstored_alone p) := buffer_seq p;
unstored_sandwich_seq (Unstored_sandwich p sd s) := 
  buffer_seq p ++ sdeque_seq sd ++ buffer_seq s.

Equations deque_seq {A} : deque A -> list A :=
deque_seq (T cd) := cdeque_seq cd.

(* Unset Equations Transparent. *)

(* The list application is made opaque. *)

Opaque app.
Definition singleton {A : Type} (x : A) : list A := [x].
Opaque singleton.

(* A list of tactics to be used when trying to resolve obligations generated by
   Equations. *)

#[export] Hint Rewrite <-app_assoc : rlist.
#[export] Hint Rewrite <-app_comm_cons : rlist.
#[export] Hint Rewrite app_nil_r : rlist.
#[export] Hint Rewrite map_app : rlist.
#[export] Hint Rewrite concat_app : rlist.

Lemma path_children [A lvl nlvl len is_hole K1 K2 G Y O R] 
  (natur : triple A lvl len is_hole K1 K2 (Mix NoGreen Y O NoRed))
  (adopt : triple A nlvl 0 false K2 K2 (Mix G NoYellow NoOrange R)) 
  (e : nlvl = len + lvl) :
  path_seq (Children natur adopt e) = 
    triple_front_seq natur ++ triple_seq adopt ++ triple_rear_seq natur.
Proof. subst; simp triple_seq; autorewrite with rlist; reflexivity. Qed.

Lemma stored_triple_ground [A] (a : A) : stored_triple_seq (ST_ground a) = [a].
Proof. simpl; reflexivity. Qed.

Lemma stored_triple_small [A lvl q] (p : prefix A lvl (3 + q)) : 
  stored_triple_seq (ST_small p) = buffer_seq p.
Proof. apply buffer.correct_mapping. Qed.
  
Lemma stored_triple_triple [A lvl qp qs C] 
  (p : prefix A lvl (3 + qp)) 
  (cd : cdeque A (S lvl) C) 
  (s : suffix A lvl (3 + qs)) : 
  stored_triple_seq (ST_triple p cd s) = 
    buffer_seq p ++ cdeque_seq cd ++ buffer_seq s.
Proof.
  simpl stored_triple_seq;
  (* Separate prefix, child and suffix cases. *)
  repeat apply div_app2;
(* Handle the simple child case. *)
  try reflexivity;
  (* Finish with the buffers. *)
  apply buffer.correct_mapping.
Qed.

Lemma triple_front_hole (A : Type) (lvl : nat) (K : kind) : 
  triple_front_seq (A := A) (lvl := lvl) (K1 := K) Hole = [].
Proof. reflexivity. Qed.

Lemma triple_rear_hole (A : Type) (lvl : nat) (K : kind) :
  triple_rear_seq (A := A) (lvl := lvl) (K1 := K) Hole = [].
Proof. reflexivity. Qed.

Lemma triple_front_small [A lvl qp qs K] 
  (p : prefix A lvl qp) (s : suffix A lvl qs) 
  (ss : small_triple_size qp qs K) :
  triple_front_seq (Small p s ss) = buffer_seq p.
Proof. cbn; apply correct_path_buffer_seq. Qed.
  
Lemma triple_rear_small [A lvl qp qs K] 
  (p : prefix A lvl qp) (s : suffix A lvl qs) 
  (ss : small_triple_size qp qs K) :
  triple_rear_seq (Small p s ss) = buffer_seq s.
Proof. cbn; apply correct_path_buffer_seq. Qed.

Lemma triple_front_green [A lvl qp qs K G R] 
  (p : prefix A lvl qp) 
  (cd : non_empty_cdeque A (S lvl) (Mix G NoYellow NoOrange R)) 
  (s : suffix A lvl qs)
  (bs : big_triple_size 8 qp qs K) :
  triple_front_seq (Green p cd s bs) = buffer_seq p ++ ne_cdeque_seq cd.
Proof. 
  cbn; apply div_app2. 
  - apply correct_path_buffer_seq.
  - reflexivity.
Qed.

Lemma triple_rear_green [A lvl qp qs K G R] 
  (p : prefix A lvl qp) 
  (cd : non_empty_cdeque A (S lvl) (Mix G NoYellow NoOrange R)) 
  (s : suffix A lvl qs)
  (bs : big_triple_size 8 qp qs K) :
  triple_rear_seq (Green p cd s bs) = buffer_seq s.
Proof. cbn; apply correct_path_buffer_seq. Qed.

Lemma triple_front_yellow [A lvl len qp qs K1 K2] 
  (p : prefix A lvl qp)
  (pkt : packet A (S lvl) len preferred_left K2)
  (s : suffix A lvl qs)
  (bs : big_triple_size 7 qp qs K1) :
  triple_front_seq (Yellow p pkt s bs) = buffer_seq p ++ packet_front_seq pkt.
Proof. 
  cbn; apply div_app2.
  - apply correct_path_buffer_seq.
  - reflexivity.
Qed.

Lemma triple_rear_yellow [A lvl len qp qs K1 K2] 
  (p : prefix A lvl qp)
  (pkt : packet A (S lvl) len preferred_left K2)
  (s : suffix A lvl qs)
  (bs : big_triple_size 7 qp qs K1) :
  triple_rear_seq (Yellow p pkt s bs) = packet_rear_seq pkt ++ buffer_seq s.
Proof. 
  cbn; apply div_app2.
  - reflexivity.
  - apply correct_path_buffer_seq.
Qed.

Lemma triple_front_orange [A lvl len qp qs K1 K2] 
  (p : prefix A lvl qp)
  (pkt : packet A (S lvl) len preferred_right K2)
  (s : suffix A lvl qs)
  (bs : big_triple_size 6 qp qs K1) :
  triple_front_seq (Orange p pkt s bs) = buffer_seq p ++ packet_front_seq pkt.
Proof. 
  cbn; apply div_app2.
  - apply correct_path_buffer_seq.
  - reflexivity.
Qed.

Lemma triple_rear_orange [A lvl len qp qs K1 K2] 
  (p : prefix A lvl qp)
  (pkt : packet A (S lvl) len preferred_right K2)
  (s : suffix A lvl qs)
  (bs : big_triple_size 6 qp qs K1) :
  triple_rear_seq (Orange p pkt s bs) = packet_rear_seq pkt ++ buffer_seq s.
Proof. 
  cbn; apply div_app2.
  - reflexivity.
  - apply correct_path_buffer_seq.
Qed.

Lemma triple_front_red [A lvl qp qs K] 
  (p : prefix A lvl qp) 
  (cd : non_empty_cdeque A (S lvl) green) 
  (s : suffix A lvl qs)
  (bs : big_triple_size 5 qp qs K) :
  triple_front_seq (Red p cd s bs) = buffer_seq p ++ ne_cdeque_seq cd.
Proof. 
  cbn; apply div_app2.
  - apply correct_path_buffer_seq.
  - reflexivity.
Qed.

Lemma triple_rear_red [A lvl qp qs K] 
  (p : prefix A lvl qp) 
  (cd : non_empty_cdeque A (S lvl) green) 
  (s : suffix A lvl qs)
  (bs : big_triple_size 5 qp qs K) :
  triple_rear_seq (Red p cd s bs) = buffer_seq s.
Proof. cbn; apply correct_path_buffer_seq. Qed.
      
#[export] Hint Rewrite path_children : rlist.
#[export] Hint Rewrite stored_triple_ground : rlist.
#[export] Hint Rewrite stored_triple_small : rlist.
#[export] Hint Rewrite stored_triple_triple : rlist.
#[export] Hint Rewrite triple_front_hole : rlist.
#[export] Hint Rewrite triple_rear_hole : rlist.
#[export] Hint Rewrite triple_front_small : rlist.
#[export] Hint Rewrite triple_rear_small : rlist.
#[export] Hint Rewrite triple_front_green : rlist.
#[export] Hint Rewrite triple_rear_green : rlist.
#[export] Hint Rewrite triple_front_yellow : rlist.
#[export] Hint Rewrite triple_rear_yellow : rlist.
#[export] Hint Rewrite triple_front_orange : rlist.
#[export] Hint Rewrite triple_rear_orange : rlist.
#[export] Hint Rewrite triple_front_red : rlist.
#[export] Hint Rewrite triple_rear_red : rlist.

Opaque path_seq.
Opaque stored_triple_seq.
Opaque triple_front_seq.
Opaque triple_rear_seq.

(* Lemmas *)

Lemma empty_prefix [A lvl] (p : prefix A lvl 0) : buffer_seq p = [].
Proof.
  unfold buffer_seq; unfold prefix, prefix' in p.
  pose buffer.empty_buffer as H; rewrite H.
  reflexivity.
Qed.

Lemma empty_suffix [A lvl] (s : suffix A lvl 0) : buffer_seq s = [].
Proof. 
  unfold buffer_seq; unfold suffix, suffix' in s. 
  pose buffer.empty_buffer as H; rewrite H.
  reflexivity.
Qed.

#[export] Hint Rewrite empty_buffer : rlist.

#[local] Obligation Tactic :=
  try first [ done | 
    cbn beta iota delta zeta; intros; 
    try simp triple_seq in *;
    autorewrite with rlist;
    try simp buffer_seq in *;
    hauto db:rlist ].

Notation "? x" := (@exist _ _ x _) (at level 100).

(* Elements *)

Equations empty {A} : { d : deque A | deque_seq d = [] } :=
empty := ? T Empty.

(* Functions *)

Equations push_seq_equality {A lvl len K1 K2 C} 
  (x : stored_triple A lvl)
  (t1 t2 : triple A lvl len false K1 K2 C) : Prop :=
push_seq_equality (C := Mix _ NoYellow NoOrange _) x t1 t2 := 
  triple_seq t2 = stored_triple_seq x ++ triple_seq t1;
push_seq_equality (C := Mix NoGreen _ _ NoRed) x t1 t2 :=
  triple_front_seq t2 = stored_triple_seq x ++ triple_front_seq t1 
  /\ triple_rear_seq t2 = triple_rear_seq t1.
Transparent push_seq_equality.

Equations inject_seq_equality {A lvl len K1 K2 C} 
  (t1 : triple A lvl len false K1 K2 C)
  (x : stored_triple A lvl)
  (t2 : triple A lvl len false K1 K2 C) : Prop :=
inject_seq_equality (C := Mix _ NoYellow NoOrange _) t1 x t2 := 
  triple_seq t2 = triple_seq t1 ++ stored_triple_seq x;
inject_seq_equality (C := Mix NoGreen _ _ NoRed) t1 x t2 :=
  triple_front_seq t2 = triple_front_seq t1 /\
  triple_rear_seq t2 = triple_rear_seq t1 ++ stored_triple_seq x.
Transparent inject_seq_equality.

Equations push_only_triple {A lvl len K C}
  (x : stored_triple A lvl) 
  (t : only_triple A lvl len false K C) :
  { t' : only_triple A lvl len false K C | push_seq_equality x t t' } :=
push_only_triple x (Small p s SOnly) with buffer.push x p => {
  | ? p' := ? Small p' s SOnly };
push_only_triple x (Green p cd s BOnly) with buffer.push x p => {
  | ? p' := ? Green p' cd s BOnly };
push_only_triple x (Yellow p pkt s BOnly) with buffer.push x p => {
  | ? p' := ? Yellow p' pkt s BOnly };
push_only_triple x (Orange p pkt s BOnly) with buffer.push x p => {
  | ? p' := ? Orange p' pkt s BOnly };
push_only_triple x (Red p cd s BOnly) with buffer.push x p => {
  | ? p' := ? Red p' cd s BOnly }.

Equations inject_only_triple {A lvl len K C}
  (t : only_triple A lvl len false K C)
  (x : stored_triple A lvl) :
  { t' : only_triple A lvl len false K C | inject_seq_equality t x t' } :=
inject_only_triple (Small p s SOnly) x with buffer.inject p x => {
  | ? p' := ? Small p' s SOnly };
inject_only_triple (Green p cd s BOnly) x with buffer.inject s x => {
  | ? s' := ? Green p cd s' BOnly };
inject_only_triple (Yellow p pkt s BOnly) x with buffer.inject s x => {
  | ? s' := ? Yellow p pkt s' BOnly };
inject_only_triple (Orange p pkt s BOnly) x with buffer.inject s x => {
  | ? s' := ? Orange p pkt s' BOnly };
inject_only_triple (Red p cd s BOnly) x with buffer.inject s x => {
  | ? s' := ? Red p cd s' BOnly }.

Equations push_only_path {A lvl C} 
  (x : stored_triple A lvl) 
  (p : path A lvl Only C) :
  { p' : path A lvl Only C | path_seq p' = stored_triple_seq x ++ path_seq p } :=
push_only_path x (Children Hole natural eq_refl) with push_only_triple x natural => {
  | ? natural' := ? Children Hole natural' eq_refl };
push_only_path x (Children natural adoptive eq_refl) with push_only_triple x natural => {
  | ? natural' := ? Children natural' adoptive eq_refl }.

Equations inject_only_path {A lvl C}
  (p : path A lvl Only C)
  (x : stored_triple A lvl) :
  { p' : path A lvl Only C | path_seq p' = path_seq p ++ stored_triple_seq x } :=
inject_only_path (Children Hole adoptive eq_refl) x with inject_only_triple adoptive x => {
  | ? adoptive' := ? Children Hole adoptive' eq_refl };
inject_only_path (Children natural adoptive eq_refl) x with inject_only_triple natural x => {
  | ? natural' := ? Children natural' adoptive eq_refl }.

Equations push_left_triple {A lvl len K C}
  (x : stored_triple A lvl)
  (t : left_triple A lvl len false K C) :
  { t' : left_triple A lvl len false K C | push_seq_equality x t t' } :=
push_left_triple x (Small p s SLeft) with buffer.push x p => {
  | ? p' := ? Small p' s SLeft };
push_left_triple x (Green p cd s BLeft) with buffer.push x p => {
  | ? p' := ? Green p' cd s BLeft };
push_left_triple x (Yellow p pkt s BLeft) with buffer.push x p => {
  | ? p' := ? Yellow p' pkt s BLeft };
push_left_triple x (Orange p pkt s BLeft) with buffer.push x p => {
  | ? p' := ? Orange p' pkt s BLeft };
push_left_triple x (Red p cd s BLeft) with buffer.push x p => {
  | ? p' := ? Red p' cd s BLeft }.

Equations inject_right_triple {A lvl len K C} 
  (t : right_triple A lvl len false K C) 
  (x : stored_triple A lvl) :
  { t' : right_triple A lvl len false K C | inject_seq_equality t x t' } :=
inject_right_triple (Small p s SRight) x with buffer.inject s x => {
  | ? s' := ? Small p s' SRight };
inject_right_triple (Green p cd s BRight) x with buffer.inject s x => {
  | ? s' := ? Green p cd s' BRight };
inject_right_triple (Yellow p pkt s BRight) x with buffer.inject s x => {
  | ? s' := ? Yellow p pkt s' BRight };
inject_right_triple (Orange p pkt s BRight) x with buffer.inject s x => {
  | ? s' := ? Orange p pkt s' BRight };
inject_right_triple (Red p cd s BRight) x with buffer.inject s x => {
  | ? s' := ? Red p cd s' BRight }.

Equations push_left_path {A lvl C} 
  (x : stored_triple A lvl)
  (p : path A lvl Left C) :
  { p' : path A lvl Left C | path_seq p' = stored_triple_seq x ++ path_seq p } :=
push_left_path x (Children Hole natural eq_refl) with push_left_triple x natural => {
  | ? natural' := ? Children Hole natural' eq_refl };
push_left_path x (Children natural adoptive eq_refl) with push_left_triple x natural => {
  | ? natural' := ? Children natural' adoptive eq_refl }.

Equations inject_right_path {A lvl C}
  (p : path A lvl Right C)
  (x : stored_triple A lvl) :
  { p' : path A lvl Right C | path_seq p' = path_seq p ++ stored_triple_seq x } :=
inject_right_path (Children Hole natural eq_refl) x with inject_right_triple natural x => {
  | ? natural' := ? Children Hole natural' eq_refl };
inject_right_path (Children natural adoptive eq_refl) x with inject_right_triple natural x => {
  | ? natural' := ? Children natural' adoptive eq_refl }.

Equations push_ne_cdeque {A lvl C} 
  (x : stored_triple A lvl) 
  (cd : non_empty_cdeque A lvl C) :
  { cd' : non_empty_cdeque A lvl C | ne_cdeque_seq cd' = stored_triple_seq x ++ ne_cdeque_seq cd } :=
push_ne_cdeque x (Only_path p) with push_only_path x p => {
  | ? p' := ? Only_path p' };
push_ne_cdeque x (Pair_green pl pr) with push_left_path x pl => {
  | ? pl' := ? Pair_green pl' pr };
push_ne_cdeque x (Pair_red pl pr) with push_left_path x pl => {
  | ? pl' := ? Pair_red pl' pr }.

Equations inject_ne_cdeque {A lvl C}
  (cd : non_empty_cdeque A lvl C)
  (x : stored_triple A lvl) :
  { cd' : non_empty_cdeque A lvl C | ne_cdeque_seq cd' = ne_cdeque_seq cd ++ stored_triple_seq x } :=
inject_ne_cdeque (Only_path p) x with inject_only_path p x => {
  | ? p' := ? Only_path p' };
inject_ne_cdeque (Pair_green pl pr) x with inject_right_path pr x => {
  | ? pr' := ? Pair_green pl pr' };
inject_ne_cdeque (Pair_red pl pr) x with inject_right_path pr x => {
  | ? pr' := ? Pair_red pl pr' }.

Equations single_triple {A lvl} (x : stored_triple A lvl) :
  {t : triple A lvl 0 false Only Only green | triple_seq t = stored_triple_seq x } :=
single_triple x with buffer.single x, buffer.empty => { | ? p, ? s := ? Small p s SOnly }.

Equations only_single {A lvl} (x : stored_triple A lvl) :
  {cd : non_empty_cdeque A lvl green | ne_cdeque_seq cd = stored_triple_seq x } :=
only_single x with single_triple x => { | ? t := ? Only_path (Children Hole t eq_refl) }.

Equations single {A lvl} (x : stored_triple A lvl) :
  {cd : cdeque A lvl green | cdeque_seq cd = stored_triple_seq x } :=
single x with only_single x => { | ? cd := ? NonEmpty cd }. 

Equations push_cdeque {A lvl C} 
  (x : stored_triple A lvl) 
  (cd : cdeque A lvl C) :
  { cd' : cdeque A lvl C | cdeque_seq cd' = stored_triple_seq x ++ cdeque_seq cd } :=
push_cdeque x Empty with single x => { | ? cd := ? cd };
push_cdeque x (NonEmpty cd) with push_ne_cdeque x cd => { | ? cd' := ? NonEmpty cd' }.

Equations inject_cdeque {A lvl C}
  (cd : cdeque A lvl C)
  (x : stored_triple A lvl) :
  { cd' : cdeque A lvl C | cdeque_seq cd' = cdeque_seq cd ++ stored_triple_seq x } :=
inject_cdeque Empty x with single x => { | ? cd := ? cd };
inject_cdeque (NonEmpty cd) x with inject_ne_cdeque cd x => { | ? cd' := ? NonEmpty cd' }.

Equations push {A} (x : A) (d : deque A) : 
  { d' : deque A | deque_seq d' = [x] ++ deque_seq d } :=
push x (T cd) with push_cdeque (ST_ground x) cd => { | ? cd' := ? T cd' }.

Equations inject {A} (d : deque A) (x : A) :
  { d' : deque A | deque_seq d' = deque_seq d ++ [x] } :=
inject (T cd) x with inject_cdeque cd (ST_ground x) => { | ? cd' := ? T cd' }.

Equations push_semi {A lvl} 
  (x : stored_triple A lvl)
  (sd : sdeque A lvl) :
  { sd' : sdeque A lvl | sdeque_seq sd' = stored_triple_seq x ++ sdeque_seq sd } :=
push_semi x (Sd cd) with push_cdeque x cd => { | ? cd' := ? Sd cd' }.

Equations inject_semi {A lvl}
  (sd : sdeque A lvl)
  (x : stored_triple A lvl) :
  { sd' : sdeque A lvl | sdeque_seq sd' = sdeque_seq sd ++ stored_triple_seq x } :=
inject_semi (Sd cd) x with inject_cdeque cd x => { | ? cd' := ? Sd cd' }.

Equations push_vector {A lvl n C} 
  (v : vector (stored_triple A lvl) n)
  (cd : cdeque A lvl C) :
  { cd' : cdeque A lvl C |
    cdeque_seq cd' = concat (map stored_triple_seq (vector_seq v)) ++ cdeque_seq cd } :=
push_vector V0 cd1 := ? cd1;
push_vector (V1 a1) cd with push_cdeque a1 cd => { | ? cd1 := ? cd1 };
push_vector (V2 a1 a2) cd with push_cdeque a2 cd => {
  | ? cd2 with push_cdeque a1 cd2 => { | ? cd1 := ? cd1 } };
push_vector (V3 a1 a2 a3) cd with push_cdeque a3 cd => { 
  | ? cd3 with push_cdeque a2 cd3 => { | ? cd2 with push_cdeque a1 cd2 => { 
    | ? cd1 := ? cd1 } } };
push_vector (V4 a1 a2 a3 a4) cd with push_cdeque a4 cd => {
  | ? cd4 with push_cdeque a3 cd4 => { | ? cd3 with push_cdeque a2 cd3 => {
    | ? cd2 with push_cdeque a1 cd2 => { | ? cd1 := ? cd1 } } } };
push_vector (V5 a1 a2 a3 a4 a5) cd with push_cdeque a5 cd => {
  | ? cd5 with push_cdeque a4 cd5 => { | ? cd4 with push_cdeque a3 cd4 => {
    | ? cd3 with push_cdeque a2 cd3 => { | ? cd2 with push_cdeque a1 cd2 => {
      | ? cd1 := ? cd1 } } } } };
push_vector (V6 a1 a2 a3 a4 a5 a6) cd with push_cdeque a6 cd => {
  | ? cd6 with push_cdeque a5 cd6 => { | ? cd5 with push_cdeque a4 cd5 => {
    | ? cd4 with push_cdeque a3 cd4 => { | ? cd3 with push_cdeque a2 cd3 => {
      | ? cd2 with push_cdeque a1 cd2 => { | ? cd1 := ? cd1 } } } } } }.

Equations inject_vector {A lvl n C} 
  (cd : cdeque A lvl C)
  (v : vector (stored_triple A lvl) n) :
  { cd' : cdeque A lvl C |
    cdeque_seq cd' = cdeque_seq cd ++ concat (map stored_triple_seq (vector_seq v)) } :=
inject_vector cd0 V0 := ? cd0;
inject_vector cd (V1 a1) with inject_cdeque cd a1 => { | ? cd1 := ? cd1 };
inject_vector cd (V2 a1 a2) with inject_cdeque cd a1 => {
  | ? cd1 with inject_cdeque cd1 a2 => { | ? cd2 := ? cd2 } };
inject_vector cd (V3 a1 a2 a3) with inject_cdeque cd a1 => { 
  | ? cd1 with inject_cdeque cd1 a2 => { | ? cd2 with inject_cdeque cd2 a3 => { 
    | ? cd3 := ? cd3 } } };
inject_vector cd (V4 a1 a2 a3 a4) with inject_cdeque cd a1 => {
  | ? cd1 with inject_cdeque cd1 a2 => { | ? cd2 with inject_cdeque cd2 a3 => {
    | ? cd3 with inject_cdeque cd3 a4 => { | ? cd4 := ? cd4 } } } };
inject_vector cd (V5 a1 a2 a3 a4 a5) with inject_cdeque cd a1 => {
  | ? cd1 with inject_cdeque cd1 a2 => { | ? cd2 with inject_cdeque cd2 a3 => {
    | ? cd3 with inject_cdeque cd3 a4 => { | ? cd4 with inject_cdeque cd4 a5 => {
      | ? cd5 := ? cd5 } } } } };
inject_vector cd (V6 a1 a2 a3 a4 a5 a6) with inject_cdeque cd a1 => {
  | ? cd1 with inject_cdeque cd1 a2 => { | ? cd2 with inject_cdeque cd2 a3 => {
    | ? cd3 with inject_cdeque cd3 a4 => { | ? cd4 with inject_cdeque cd4 a5 => {
      | ? cd5 with inject_cdeque cd5 a6 => { | ? cd6 := ? cd6 } } } } } }.

#[local] Obligation Tactic :=
  try first [ done | 
    cbn beta iota delta zeta; intros; 
    autorewrite with rlist;
    try simp buffer_seq in *;
    hauto db:rlist ].

Equations to_pref_left {A lvl C} (cd : non_empty_cdeque A lvl C) : 
  { pl : pref_left A lvl | pref_left_seq pl = ne_cdeque_seq cd } :=
to_pref_left (Only_path (Children natur adopt eq_refl)) := 
  ? Pref_left (Only_child natur) adopt eq_refl;
to_pref_left (Pair_green (Children natur adopt eq_refl) pr) := 
  ? Pref_left (Left_child natur pr) adopt eq_refl;
to_pref_left (Pair_red (Children natur adopt eq_refl) pr) := 
  ? Pref_left (Left_child natur pr) adopt eq_refl.

Equations to_pref_right {A lvl len nlvl K} 
  (pkt : packet A lvl len preferred_left K)
  (t : triple A nlvl 0 false K K green) :
  nlvl = len + lvl -> 
  { pr : pref_right A lvl | 
    pref_right_seq pr = packet_front_seq pkt ++ triple_seq t ++ packet_rear_seq pkt } :=
to_pref_right (Only_child t1) t2 eq_refl:= ? Pref_right (Only_child t1) t2 eq_refl;
to_pref_right (Left_child t1 (Children natur adopt eq_refl)) t2 eq_refl := 
  ? Pref_right (Right_child (Children t1 t2 eq_refl) natur) adopt eq_refl.

Equations no_pref {A lvl len nlvl K}
  (pkt : packet A lvl len preferred_right K)
  (t : triple A nlvl 0 false K K green) :
  nlvl = len + lvl ->
  { cd : non_empty_cdeque A lvl green | 
    ne_cdeque_seq cd = packet_front_seq pkt ++ triple_seq t ++ packet_rear_seq pkt } :=
no_pref (Only_child t1) t2 eq_refl := ? Only_path (Children t1 t2 eq_refl);
no_pref (Right_child pl t1) t2 eq_refl := ? Pair_green pl (Children t1 t2 eq_refl).

Equations make_child {A lvl len nlvl pref K G R}
  (pkt : packet A lvl len pref K)
  (t : triple A nlvl 0 false K K (Mix G NoYellow NoOrange R)) :
  nlvl = len + lvl ->
  { sd : sdeque A lvl | 
    sdeque_seq sd = packet_front_seq pkt ++ triple_seq t ++ packet_rear_seq pkt } :=
make_child (Only_child t1) t2 eq_refl :=
  ? Sd (NonEmpty (Only_path (Children t1 t2 eq_refl)));
make_child (Left_child t1 pr) t2 eq_refl :=
  ? Sd (NonEmpty (Pair_red (Children t1 t2 eq_refl) pr));
make_child (G := SomeGreen) (R := NoRed) (Right_child pl t1) t2 eq_refl :=
  ? Sd (NonEmpty (Pair_green pl (Children t1 t2 eq_refl)));
make_child (G := NoGreen) (R := SomeRed) (Right_child pl t1) t2 eq_refl :=
  ? Sd (NonEmpty (Pair_red pl (Children t1 t2 eq_refl))).
 
Equations push_child {A lvl len nlvl pref K G R} 
  (x : stored_triple A lvl) 
  (pkt : packet A lvl len pref K) 
  (t : triple A nlvl 0 false K K (Mix G NoYellow NoOrange R)) :
  nlvl = len + lvl ->
  { '(pkt', t') : packet A lvl len pref K * 
                  triple A nlvl 0 false K K (Mix G NoYellow NoOrange R) | 
    packet_front_seq pkt' ++ triple_seq t' ++ packet_rear_seq pkt' =
      stored_triple_seq x ++ 
      packet_front_seq pkt ++ triple_seq t ++ packet_rear_seq pkt } :=
push_child x (Only_child Hole) t eq_refl with push_only_triple x t => {
  | ? t' := ? (Only_child Hole, t') };
push_child x (Only_child t1) t2 eq_refl with push_only_triple x t1 => {
  | ? t1' := ? (Only_child t1', t2) };
push_child x (Left_child Hole pr) t eq_refl with push_left_triple x t => {
  | ? t' := ? (Left_child Hole pr, t') };
push_child x (Left_child t1 pr) t2 eq_refl with push_left_triple x t1 => {
  | ? t1' := ? (Left_child t1' pr, t2) };
push_child x (Right_child pl t1) t2 eq_refl with push_left_path x pl => {
  | ? pl' := ? (Right_child pl' t1, t2) }.

Equations inject_child {A lvl len nlvl pref K G R} 
  (pkt : packet A lvl len pref K)
  (t : triple A nlvl 0 false K K (Mix G NoYellow NoOrange R)) 
  (x : stored_triple A lvl) :
  nlvl = len + lvl ->
  { '(pkt', t') : packet A lvl len pref K * 
                  triple A nlvl 0 false K K (Mix G NoYellow NoOrange R) | 
    packet_front_seq pkt' ++ triple_seq t' ++ packet_rear_seq pkt' =
      packet_front_seq pkt ++ triple_seq t ++ packet_rear_seq pkt ++
      stored_triple_seq x } :=
inject_child (Only_child Hole) t x eq_refl with inject_only_triple t x => {
  | ? t' := ? (Only_child Hole, t') };
inject_child (Only_child t1) t2 x eq_refl with inject_only_triple t1 x => {
  | ? t1' := ? (Only_child t1', t2) };
inject_child (Left_child t1 pr) t2 x eq_refl with inject_right_path pr x => {
  | ? pr' := ? (Left_child t1 pr', t2) };
inject_child (Right_child pl Hole) t x eq_refl with inject_right_triple t x => {
  | ? t' := ? (Right_child pl Hole, t') };
inject_child (Right_child pl t1) t2 x eq_refl with inject_right_triple t1 x => {
  | ? t1' := ? (Right_child pl t1', t2) }.

Equations stored_left {A lvl q C} 
  (p : prefix A lvl (5 + q))
  (cd : cdeque A (S lvl) C) 
  (s : suffix A lvl 2)
  (b : buffer_12 A lvl) :
  { '(p', x) : prefix A lvl 2 * stored_triple A (S lvl) | 
    buffer_seq p' ++ stored_triple_seq x = 
      buffer_seq p ++ cdeque_seq cd ++ buffer_seq s ++ buffer_12_seq b } :=
stored_left p cd s (x, v) with buffer.inject s x => {
  | ? s1 with buffer.inject_vector s1 v => {
    | ? s2 with buffer.pop2 p => {
      | ? (x1, x2, p1) with buffer.pair x1 x2 => {
        | ? p2 := ? (p2, ST_triple p1 cd s2) } } } }.

Equations stored_right {A lvl q C} 
  (b : buffer_12 A lvl)
  (p : prefix A lvl 2)
  (cd : cdeque A (S lvl) C)
  (s : suffix A lvl (5 + q)) :
  { '(x, s') : stored_triple A (S lvl) * suffix A lvl 2 | 
    stored_triple_seq x ++ buffer_seq s' =
      buffer_12_seq b ++ buffer_seq p ++ cdeque_seq cd ++ buffer_seq s } :=
stored_right (x, v) p cd s with buffer.push_vector v p => {
  | ? p1 with buffer.push x p1 => {
    | ? p2 with buffer.eject2 s => {
      | ? (s1, x1, x2) with buffer.pair x1 x2 => {
        | ? s2 := ? (ST_triple p2 cd s1, s2) } } } }.

Local Ltac rewrite_seq :=
  repeat 
  match goal with 
  | H : _ = seq _ |- _ => rewrite <-H
  end.

#[local] Obligation Tactic :=
  try first [ done | 
    cbn beta iota delta zeta; intros; 
    autorewrite with rlist;
    try simp triple_seq in *;
    autorewrite with rlist in *;
    hauto db:rlist ].

Equations extract_stored_left {A lvl C} 
  (p : path A lvl Left C) (b : buffer_12 A lvl) :
  { '(s, x) : suffix A lvl 2 * stored_triple A (S lvl) | 
    buffer_seq s ++ stored_triple_seq x = path_seq p ++ buffer_12_seq b } :=
extract_stored_left (Children Hole (Small p s SLeft) eq_refl) b
  with stored_left p Empty s b => { | ? (s', x) := ? (s', x) };
extract_stored_left (Children Hole (Green p cd s BLeft) eq_refl) b 
  with stored_left p (NonEmpty cd) s b => { | ? (s', x) := ? (s', x) };
extract_stored_left (Children (Yellow p pkt s BLeft) t eq_refl) b
  with make_child pkt t _ => {
    | ? Sd cd with stored_left p cd s b => { | ? (s', x) := ? (s', x) } };
extract_stored_left (Children (Orange p pkt s BLeft) t eq_refl) b
  with make_child pkt t _ => {
    | ? Sd cd with stored_left p cd s b => { | ? (s', x) := ? (s', x) } };
extract_stored_left (Children Hole (Red p cd s BLeft) eq_refl) b
  with stored_left p (NonEmpty cd) s b => { | ? (s', x) := ? (s', x) }.

Equations extract_stored_right {A lvl C}
  (b : buffer_12 A lvl) (p : path A lvl Right C) :
  { '(x, s) : stored_triple A (S lvl) * suffix A lvl 2 | 
    stored_triple_seq x ++ buffer_seq s = buffer_12_seq b ++ path_seq p } :=
extract_stored_right b (Children Hole (Small p s SRight) eq_refl)
  with stored_right b p Empty s => { | ? (x, s') := ? (x, s') };
extract_stored_right b (Children Hole (Green p cd s BRight) eq_refl) 
  with stored_right b p (NonEmpty cd) s => { | ? (x, s') := ? (x, s') };
extract_stored_right b (Children (Yellow p pkt s BRight) t eq_refl)
  with make_child pkt t _ => {
    | ? Sd cd with stored_right b p cd s => { | ? (x, s') := ? (x, s') } };
extract_stored_right b (Children (Orange p pkt s BRight) t eq_refl)
  with make_child pkt t _ => {
    | ? Sd cd with stored_right b p cd s => { | ? (x, s') := ? (x, s') } };
extract_stored_right b (Children Hole (Red p cd s BRight) eq_refl)
  with stored_right b p (NonEmpty cd) s => { | ? (x, s') := ? (x, s') }.

#[local] Obligation Tactic :=
  try first [ done | 
    cbn beta iota delta zeta; intros; 
    autorewrite with rlist;
    try simp triple_seq in *;
    autorewrite with rlist in *;
    try simp buffer_seq in *;
    hauto db:rlist ];
  cbn beta iota delta zeta; intros; 
  autorewrite with rlist;
  try simp triple_seq in *;
  autorewrite with rlist in *;
  try simp buffer_seq in *.

Equations left_of_pair {A lvl C1 C2}
  (pl : path A lvl Left C1) (pr : path A lvl Right C2) :
  { p : path A lvl Left C1 | path_seq p = path_seq pl ++ path_seq pr } :=
left_of_pair (Children Hole (Small p s SLeft) eq_refl) pr 
  with buffer.two s => { | ? (x1, x2) with buffer.inject p x1 => {
    | ? p' with extract_stored_right (x2, V0) pr => {
      | ? (stored, s') with single_triple stored => {
        | ? t := ? Children (Orange p' (Only_child Hole) s' BLeft) t eq_refl } } } };
left_of_pair (Children Hole (Green p cd s BLeft) eq_refl) pr
  with buffer.two s => { | ? (x1, x2) with extract_stored_right (x1, V1 x2) pr => {
    | ? (stored, s') with inject_ne_cdeque cd stored => {
      | ? cd' := ? Children Hole (Green p cd' s' BLeft) eq_refl } } };
left_of_pair (Children (Yellow p pkt s BLeft) t eq_refl) pr 
  with buffer.two s => { | ? (x1, x2) with extract_stored_right (x1, V1 x2) pr => {
    | ? (stored, s') with inject_child pkt t stored _ => {
      | ? (pkt', t') := ? Children (Yellow p pkt' s' BLeft) t' eq_refl } } };
left_of_pair (Children (Orange p pkt s BLeft) t eq_refl) pr
  with buffer.two s => { | ? (x1, x2) with extract_stored_right (x1, V1 x2) pr => {
    | ? (stored, s') with inject_child pkt t stored _ => {
      | ? (pkt', t') := ? Children (Orange p pkt' s' BLeft) t' eq_refl } } };
left_of_pair (Children Hole (Red p cd s BLeft) eq_refl) pr 
  with buffer.two s => { | ? (x1, x2) with extract_stored_right (x1, V1 x2) pr => {
    | ? (stored, s') with inject_ne_cdeque cd stored => {
      | ? cd' := ? Children Hole (Red p cd' s' BLeft) eq_refl } } }.
Next Obligation. Qed.
Next Obligation.
  aac_rewrite y1; rewrite <-y; hauto db:rlist.
Qed.
Next Obligation.
  aac_rewrite y1; rewrite <-y; hauto db:rlist.
Qed.

Equations right_of_pair {A lvl C1 C2} 
  (pl : path A lvl Left C1) (pr : path A lvl Right C2) :
  { p : path A lvl Right C2 | path_seq p = path_seq pl ++ path_seq pr } :=
right_of_pair pl (Children Hole (Small p s SRight) eq_refl) 
  with buffer.two p => { | ? (x1, x2) with buffer.push x2 s => {
    | ? s' with extract_stored_left pl (x1, V0) => {
      | ? (p', stored) with single_triple stored => {
        | ? t := ? Children (Orange p' (Only_child Hole) s' BRight) t eq_refl } } } };
right_of_pair pl (Children Hole (Green p cd s BRight) eq_refl)
  with buffer.two p => { | ? (x1, x2) with extract_stored_left pl (x1, V1 x2) => {
    | ? (p', stored) with push_ne_cdeque stored cd => {
      | ? cd' := ? Children Hole (Green p' cd' s BRight) eq_refl } } };
right_of_pair pl (Children (Yellow p pkt s BRight) t eq_refl)
  with buffer.two p => { | ? (x1, x2) with extract_stored_left pl (x1, V1 x2) => {
    | ? (p', stored) with push_child stored pkt t _ => {
      | ? (pkt', t') := ? Children (Yellow p' pkt' s BRight) t' eq_refl } } };
right_of_pair pl (Children (Orange p pkt s BRight) t eq_refl)
  with buffer.two p => { | ? (x1, x2) with extract_stored_left pl (x1, V1 x2) => {
    | ? (p', stored) with push_child stored pkt t _ => {
      | ? (pkt', t') := ? Children (Orange p' pkt' s BRight) t' eq_refl } } };
right_of_pair pl (Children Hole (Red p cd s BRight) eq_refl)
  with buffer.two p => { | ? (x1, x2) with extract_stored_left pl (x1, V1 x2) => {
    | ? (p', stored) with push_ne_cdeque stored cd => {
      | ? cd' := ? Children Hole (Red p' cd' s BRight) eq_refl } } }.
Next Obligation.
  aac_rewrite e0; aac_rewrite y0; hauto db:rlist.
Qed.
Next Obligation.
  aac_rewrite e; aac_rewrite y0; hauto db:rlist.
Qed.
Next Obligation.
  aac_rewrite e; aac_rewrite y0; hauto db:rlist.
Qed.
Next Obligation.
  aac_rewrite y1; aac_rewrite y0; hauto db:rlist.
Qed.
Next Obligation.
  aac_rewrite y1; aac_rewrite y0; hauto db:rlist.
Qed.

Equations left_of_only {A lvl C} (p : path A lvl Only C) :
  { p' : path_attempt A lvl Left C | path_attempt_seq p' = path_seq p } :=
left_of_only (Children Hole (Small p _ SOnly) eq_refl) 
  with buffer.has5p2 p => {
    | ? inl v := ? ZeroSix v;
    | ? inr (p', x1, x2) with buffer.pair x1 x2 => {
      | ? s := ? Ok (Children Hole (Small p' s SLeft) eq_refl) } };
left_of_only (Children Hole (Green p cd s BOnly) eq_refl) 
  with buffer.eject2 s => { | ? (s1, x1, x2) with buffer.pair x1 x2 => {
    | ? s' with inject_ne_cdeque cd (ST_small s1) => {
      | ? cd' := ? Ok (Children Hole (Green p cd' s' BLeft) eq_refl) } } };
left_of_only (Children (Yellow p pkt s BOnly) t eq_refl) 
  with buffer.eject2 s => { | ? (s1, x1, x2) with buffer.pair x1 x2 => {
    | ? s' with inject_child pkt t (ST_small s1) _ => {
      | ? (pkt', t') := ? Ok (Children (Yellow p pkt' s' BLeft) t' eq_refl) } } };
left_of_only (Children (Orange p pkt s BOnly) t eq_refl)
  with buffer.eject2 s => { | ? (s1, x1, x2) with buffer.pair x1 x2 => {
    | ? s' with inject_child pkt t (ST_small s1) _ => {
      | ? (pkt', t') := ? Ok (Children (Orange p pkt' s' BLeft) t' eq_refl) } } };
left_of_only (Children Hole (Red p cd s BOnly) eq_refl)
  with buffer.eject2 s => { | ? (s1, x1, x2) with buffer.pair x1 x2 => {
    | ? s' with inject_ne_cdeque cd (ST_small s1) => {
      | ? cd' := ? Ok (Children Hole (Red p cd' s' BLeft) eq_refl) } } }.
Next Obligation.
  aac_rewrite y0; hauto db:rlist.
Qed.
Next Obligation.
  aac_rewrite y0; hauto db:rlist.
Qed.

Equations right_of_only {A lvl C} (p : path A lvl Only C) :
  { p' : path_attempt A lvl Right C | path_attempt_seq p' = path_seq p } :=
right_of_only (Children Hole (Small p _ SOnly) eq_refl) 
  with buffer.has2p5 p => {
    | ? inl v := ? ZeroSix v;
    | ? inr (x1, x2, s') with buffer.pair x1 x2 => {
      | ? p' := ? Ok (Children Hole (Small p' s' SRight) eq_refl) } };
right_of_only (Children Hole (Green p cd s BOnly) eq_refl) 
  with buffer.pop2 p => { | ? (x1, x2, p1) with buffer.pair x1 x2 => {
    | ? p' with push_ne_cdeque (ST_small p1) cd => {
      | ? cd' := ? Ok (Children Hole (Green p' cd' s BRight) eq_refl) } } };
right_of_only (Children (Yellow p pkt s BOnly) t eq_refl)
  with buffer.pop2 p => { | ? (x1, x2, p1) with buffer.pair x1 x2 => {
    | ? p' with push_child (ST_small p1) pkt t _ => {
      | ? (pkt', t') := ? Ok (Children (Yellow p' pkt' s BRight) t' eq_refl) } } };
right_of_only (Children (Orange p pkt s BOnly) t eq_refl) 
  with buffer.pop2 p => { | ? (x1, x2, p1) with buffer.pair x1 x2 => {
    | ? p' with push_child (ST_small p1) pkt t _ => {
      | ? (pkt', t') := ? Ok (Children (Orange p' pkt' s BRight) t' eq_refl) } } };
right_of_only (Children Hole (Red p cd s BOnly) eq_refl)
  with buffer.pop2 p => { | ? (x1, x2, p1) with buffer.pair x1 x2 => {
    | ? p' with push_ne_cdeque (ST_small p1) cd => {
      | ? cd' := ? Ok (Children Hole (Red p' cd' s BRight) eq_refl) } } }.
Next Obligation.
  aac_rewrite y0; hauto db:rlist.
Qed.
Next Obligation.
  aac_rewrite y0; hauto db:rlist.
Qed.

Equations make_left {A lvl C} (cd : cdeque A lvl C) :
  { p : path_attempt A lvl Left C | path_attempt_seq p = cdeque_seq cd } :=
make_left Empty := ? ZeroSix V0;
make_left (NonEmpty (Only_path p)) with left_of_only p => { | ? p' := ? p' };
make_left (NonEmpty (Pair_green pl pr)) with left_of_pair pl pr => {
  | ? p := ? Ok p };
make_left (NonEmpty (Pair_red pl pr)) with left_of_pair pl pr => {
  | ? p := ? Any p }.

Equations make_right {A lvl C} (cd : cdeque A lvl C) :
  { p : path_attempt A lvl Right C | path_attempt_seq p = cdeque_seq cd } :=
make_right Empty := ? ZeroSix V0;
make_right (NonEmpty (Only_path p)) with right_of_only p => { | ? p' := ? p' };
make_right (NonEmpty (Pair_green pl pr)) with right_of_pair pl pr => {
  | ? p := ? Ok p };
make_right (NonEmpty (Pair_red pl pr)) with right_of_pair pl pr => {
  | ? p := ? Any p }.

Equations concat_semi {A lvl} (sd1 sd2 : sdeque A lvl) :
  { sd : sdeque A lvl | sdeque_seq sd = sdeque_seq sd1 ++ sdeque_seq sd2 } :=
concat_semi (Sd cd1) (Sd cd2) with make_left cd1 => {
  | ? ZeroSix v with push_vector v cd2 => {
    | ? cd := ? Sd cd };
  | ? Ok pl with make_right cd2 => {
    | ? ZeroSix v with inject_vector cd1 v => {
      | ? cd := ? Sd cd };
    | ? Ok pr := ? Sd (NonEmpty (Pair_red pl pr));
    | ? Any pr := ? Sd (NonEmpty (Pair_red pl pr)) };
  | ? Any pl with make_right cd2 => {
    | ? ZeroSix v with inject_vector cd1 v => {
      | ? cd := ? Sd cd };
    | ? Ok pr := ? Sd (NonEmpty (Pair_red pl pr));
    | ? Any pr := ? Sd (NonEmpty (Pair_red pl pr)) } }.

Equations concat {A} (d1 d2 : deque A) : 
  { d : deque A | deque_seq d = deque_seq d1 ++ deque_seq d2 } :=
concat (T cd1) (T cd2) with make_left cd1 => {
  | ? ZeroSix v with push_vector v cd2 => {
    | ? cd := ? T cd };
  | ? Ok pl with make_right cd2 => {
    | ? ZeroSix v with inject_vector cd1 v => {
      | ? cd := ? T cd };
    | ? Ok pr := ? T (NonEmpty (Pair_green pl pr)) } }.

(* #[local] Obligation Tactic :=
  try first [ done | 
    cbn beta iota delta zeta; intros; 
    autorewrite with rlist;
    try simp triple_seq in *;
    try simp packet_front_seq packet_rear_seq in *;
    autorewrite with rlist in *;
    try simp buffer_seq in *;
    try rewrite_seq;
    hauto db:rlist ];
  cbn; intros; autorewrite with rlist;
  try simp triple_seq in *;
  try simp packet_front_seq packet_rear_seq in *;
  autorewrite with rlist in *;
  try simp buffer_seq in *. *)

Equations semi_of_left {A lvl C} 
  (p : path A lvl Left C) 
  (x1 x2 x3 x4 x5 x6 : stored_triple A lvl) :
  { sd : sdeque A lvl | 
    sdeque_seq sd = path_seq p ++ stored_triple_seq x1 ++ stored_triple_seq x2 ++ 
                                  stored_triple_seq x3 ++ stored_triple_seq x4 ++ 
                                  stored_triple_seq x5 ++ stored_triple_seq x6 } :=
semi_of_left (Children Hole (Small p s SLeft) eq_refl) x1 x2 x3 x4 x5 x6 
  with buffer.two s => { | ? (y1, y2) with buffer.inject2 p y1 y2 => {
    | ? p1 with buffer.inject6 p1 x1 x2 x3 x4 x5 x6, buffer.empty => {
      | ? p2, ? s2 := 
      ? Sd (NonEmpty (Only_path (Children Hole (Small p2 s2 SOnly) eq_refl))) } } };
semi_of_left (Children Hole (Green p cd s BLeft) eq_refl) x1 x2 x3 x4 x5 x6 
  with buffer.inject6 s x1 x2 x3 x4 x5 x6 => {
    | ? s' := 
    ? Sd (NonEmpty (Only_path (Children Hole (Green p cd s' BOnly) eq_refl))) };
semi_of_left (Children (Yellow p pkt s BLeft) t eq_refl) x1 x2 x3 x4 x5 x6 
  with buffer.inject6 s x1 x2 x3 x4 x5 x6 => {
    | ? s' := 
    ? Sd (NonEmpty (Only_path (Children (Yellow p pkt s' BOnly) t eq_refl))) };
semi_of_left (Children (Orange p pkt s BLeft) t eq_refl) x1 x2 x3 x4 x5 x6
  with buffer.inject6 s x1 x2 x3 x4 x5 x6 => {
    | ? s' :=
    ? Sd (NonEmpty (Only_path (Children (Orange p pkt s' BOnly) t eq_refl))) };
semi_of_left (Children Hole (Red p cd s BLeft) eq_refl) x1 x2 x3 x4 x5 x6
  with buffer.inject6 s x1 x2 x3 x4 x5 x6 => {
    | ? s' := 
    ? Sd (NonEmpty (Only_path (Children Hole (Red p cd s' BOnly) eq_refl))) }.
Next Obligation. 
  rewrite <-y; hauto db:rlist.
Qed.

Equations semi_of_right {A lvl C} 
  (x1 x2 x3 x4 x5 x6 : stored_triple A lvl) 
  (p : path A lvl Right C) :
  { sd : sdeque A lvl | 
    sdeque_seq sd = stored_triple_seq x1 ++ stored_triple_seq x2 ++
                    stored_triple_seq x3 ++ stored_triple_seq x4 ++
                    stored_triple_seq x5 ++ stored_triple_seq x6 ++ path_seq p } :=
semi_of_right x1 x2 x3 x4 x5 x6 (Children Hole (Small p s SRight) eq_refl) 
  with buffer.two p => { | ? (y1, y2) with buffer.push2 y1 y2 s => {
    | ? s1 with buffer.push6 x1 x2 x3 x4 x5 x6 s1, buffer.empty => {
      | ? p2, ? s2 := 
      ? Sd (NonEmpty (Only_path (Children Hole (Small p2 s2 SOnly) eq_refl))) } } };
semi_of_right x1 x2 x3 x4 x5 x6 (Children Hole (Green p cd s BRight) eq_refl)
  with buffer.push6 x1 x2 x3 x4 x5 x6 p => {
    | ? p' :=
    ? Sd (NonEmpty (Only_path (Children Hole (Green p' cd s BOnly) eq_refl))) };
semi_of_right x1 x2 x3 x4 x5 x6 (Children (Yellow p pkt s BRight) t eq_refl) 
  with buffer.push6 x1 x2 x3 x4 x5 x6 p => {
    | ? p' :=
    ? Sd (NonEmpty (Only_path (Children (Yellow p' pkt s BOnly) t eq_refl))) };
semi_of_right x1 x2 x3 x4 x5 x6 (Children (Orange p pkt s BRight) t eq_refl)
  with buffer.push6 x1 x2 x3 x4 x5 x6 p => {
    | ? p' :=
    ? Sd (NonEmpty (Only_path (Children (Orange p' pkt s BOnly) t eq_refl))) };
semi_of_right x1 x2 x3 x4 x5 x6 (Children Hole (Red p cd s BRight) eq_refl)
  with buffer.push6 x1 x2 x3 x4 x5 x6 p => {
    | ? p' := 
    ? Sd (NonEmpty (Only_path (Children Hole (Red p' cd s BOnly) eq_refl))) }.

Equations pop_green_left {A lvl} (p : path A lvl Left green) :
  { '(x, p') : stored_triple A lvl * path_uncolored A lvl Left | 
    stored_triple_seq x ++ path_uncolored_seq p' = path_seq p } :=
pop_green_left (Children Hole (Small p s SLeft) eq_refl) 
  with buffer.pop p => { | ? (x, p1) with buffer.has5 p1 => {
    | ? inl (x1, x2, x3, x4) with buffer.two s => { | ? (x5, x6) := 
      ? (x, Six x1 x2 x3 x4 x5 x6) };
    | ? inr p2 := ? (x, AnyColor (Children Hole (Small p2 s SLeft) eq_refl)) } };
pop_green_left (Children Hole (Green p cd s BLeft) eq_refl)
  with buffer.pop p => { | ? (x, p1) with to_pref_left cd => {
    | ? Pref_left pkt t eq_refl := 
      ? (x, AnyColor (Children (Yellow p1 pkt s BLeft) t _)) } };
pop_green_left (Children (Yellow p pkt s BLeft) t eq_refl) 
  with buffer.pop p => { | ? (x, p1) with to_pref_right pkt t _ => {
    | ? Pref_right pkt' t' eq_refl := 
      ? (x, AnyColor (Children (Orange p1 pkt' s BLeft) t' _)) } };
pop_green_left (Children (Orange p pkt s BLeft) t eq_refl)
  with buffer.pop p => { | ? (x, p1) with no_pref pkt t _ => {
    | ? cd := ? (x, AnyColor (Children Hole (Red p1 cd s BLeft) eq_refl)) } }.
Next Obligation. Qed.
Next Obligation. 
  aac_rewrite e; hauto db:rlist.
Qed.

Equations eject_green_right {A lvl} (p : path A lvl Right green) :
  { '(p', x) : path_uncolored A lvl Right * stored_triple A lvl |
    path_uncolored_seq p' ++ stored_triple_seq x = path_seq p } :=
eject_green_right (Children Hole (Small p s SRight) eq_refl)
  with buffer.eject s => { | ? (s1, x) with buffer.has5 s1 => {
    | ? inl (x3, x4, x5, x6) with buffer.two p => { | ? (x1, x2) := 
      ? (Six x1 x2 x3 x4 x5 x6, x) };
    | ? inr s2 := ? (AnyColor (Children Hole (Small p s2 SRight) eq_refl), x) } };
eject_green_right (Children Hole (Green p cd s BRight) eq_refl)
  with buffer.eject s => { | ? (s1, x) with to_pref_left cd => {
    | ? Pref_left pkt t eq_refl := 
      ? (AnyColor (Children (Yellow p pkt s1 BRight) t _), x) } };
eject_green_right (Children (Yellow p pkt s BRight) t eq_refl)
  with buffer.eject s => { | ? (s1, x) with to_pref_right pkt t _ => {
    | ? Pref_right pkt' t' eq_refl := 
      ? (AnyColor (Children (Orange p pkt' s1 BRight) t' _), x) } };
eject_green_right (Children (Orange p pkt s BRight) t eq_refl)
  with buffer.eject s => { | ? (s1, x) with no_pref pkt t _ => {
    | ? cd := ? (AnyColor (Children Hole (Red p cd s1 BRight) eq_refl), x) } }.
Next Obligation. Qed.
Next Obligation.
  aac_rewrite e; hauto db:rlist.
Qed.

Equations pop_green {A lvl} (cd : non_empty_cdeque A lvl green) :
  { '(x, sd) : stored_triple A lvl * sdeque A lvl | 
    stored_triple_seq x ++ sdeque_seq sd = ne_cdeque_seq cd } :=
pop_green (Only_path (Children Hole (Small p s SOnly) eq_refl)) 
  with buffer.pop p => { | ? (x, p1) with buffer.has1 p1 => {
    | ? None := ? (x, Sd Empty);
    | ? Some p2 := 
    ? (x, Sd (NonEmpty (Only_path (Children Hole (Small p2 s SOnly) eq_refl)))) } };
pop_green (Only_path (Children Hole (Green p cd s BOnly) eq_refl))
  with buffer.pop p => { | ? (x, p1) with to_pref_left cd => {
    | ? Pref_left pkt t eq_refl :=
    ? (x, Sd (NonEmpty (Only_path (Children (Yellow p1 pkt s BOnly) t _)))) } };
pop_green (Only_path (Children (Yellow p pkt s BOnly) t eq_refl))
  with buffer.pop p => { | ? (x, p1) with to_pref_right pkt t _ => {
    | ? Pref_right pkt' t' eq_refl :=
    ? (x, Sd (NonEmpty (Only_path (Children (Orange p1 pkt' s BOnly) t' _)))) } };
pop_green (Only_path (Children (Orange p pkt s BOnly) t eq_refl))
  with buffer.pop p => { | ? (x, p1) with no_pref pkt t _ => 
    | ? cd := 
    ? (x, Sd (NonEmpty (Only_path (Children Hole (Red p1 cd s BOnly) eq_refl)))) };
pop_green (Pair_green pl pr) with pop_green_left pl => {
  | ? (x, Six x1 x2 x3 x4 x5 x6) with semi_of_right x1 x2 x3 x4 x5 x6 pr => {
    | ? sd := ? (x, sd) };
  | ? (x, AnyColor pl') := ? (x, Sd (NonEmpty (Pair_red pl' pr))) }.
Next Obligation. Qed.
Next Obligation.
  aac_rewrite e; hauto db:rlist.
Qed.

Equations eject_green {A lvl} (cd : non_empty_cdeque A lvl green) :
  { '(sd, x) : sdeque A lvl * stored_triple A lvl | 
    sdeque_seq sd ++ stored_triple_seq x = ne_cdeque_seq cd } :=
eject_green (Only_path (Children Hole (Small p s SOnly) eq_refl)) 
  with buffer.eject p => { | ? (p1, x) with buffer.has1 p1 => {
    | ? None := ? (Sd Empty, x);
    | ? Some p2 := 
    ? (Sd (NonEmpty (Only_path (Children Hole (Small p2 s SOnly) eq_refl))), x) } };
eject_green (Only_path (Children Hole (Green p cd s BOnly) eq_refl))
  with buffer.eject s => { | ? (s1, x) with to_pref_left cd => {
    | ? Pref_left pkt t eq_refl :=
    ? (Sd (NonEmpty (Only_path (Children (Yellow p pkt s1 BOnly) t _))), x) } };
eject_green (Only_path (Children (Yellow p pkt s BOnly) t eq_refl))
  with buffer.eject s => { | ? (s1, x) with to_pref_right pkt t _ => {
    | ? Pref_right pkt' t' eq_refl := 
    ? (Sd (NonEmpty (Only_path (Children (Orange p pkt' s1 BOnly) t' _))), x) } };
eject_green (Only_path (Children (Orange p pkt s BOnly) t eq_refl)) 
  with buffer.eject s => { | ? (s1, x) with no_pref pkt t _ => {
    | ? cd := 
    ? (Sd (NonEmpty (Only_path (Children Hole (Red p cd s1 BOnly) eq_refl))), x) } };
eject_green (Pair_green pl pr) with eject_green_right pr => {
  | ? (Six x1 x2 x3 x4 x5 x6, x) with semi_of_left pl x1 x2 x3 x4 x5 x6 => {
    | ? sd := ? (sd, x) };
  | ? (AnyColor pr', x) := ? (Sd (NonEmpty (Pair_red pl pr')), x) }.
Next Obligation. Qed.
Next Obligation. 
  aac_rewrite e; hauto db:rlist.
Qed.

Equations pop_stored {A lvl} (cd : non_empty_cdeque A (S lvl) green) :
  { uns : unstored A lvl | 
    unstored_front_seq uns ++ unstored_rear_seq uns = ne_cdeque_seq cd } :=
pop_stored cd with pop_green cd => {
  | ? (ST_small p, sd) := ? Unstored p sd
  | ? (ST_triple p cd1 s, sd) with push_semi (ST_small s) sd => {
    | ? sd1 with concat_semi (Sd cd1) sd1 => {
      | ? sd2 := ? Unstored p sd2 } } }.

Equations eject_stored {A lvl} (cd : non_empty_cdeque A (S lvl) green) :
  { uns : unstored A lvl | 
    unstored_rear_seq uns ++ unstored_front_seq uns = ne_cdeque_seq cd } :=
eject_stored cd with eject_green cd => {
  | ? (sd, ST_small p) := ? Unstored p sd
  | ? (sd, ST_triple p cd1 s) with inject_semi sd (ST_small p) => {
    | ? sd1 with concat_semi sd1 (Sd cd1) => {
      | ? sd2 := ? Unstored s sd2 } } }.

Equations unsandwich_green {A lvl} (cd : non_empty_cdeque A lvl green) :
  { s : sandwich A lvl | sandwich_seq s = ne_cdeque_seq cd } :=
unsandwich_green (Only_path (Children Hole (Small p s SOnly) eq_refl)) 
  with buffer.pop p => { | ? (x1, p1) with buffer.has1 p1 => {
    | ? None := ? Alone x1;
    | ? Some p2 with buffer.eject p2 => { | ? (p3, x2) with buffer.has1 p3 => {
      | ? None := ? Sandwich x1 (Sd Empty) x2;
      | ? Some p4 := 
        let only := Only_path (Children Hole (Small p4 s SOnly) eq_refl) in 
        ? Sandwich x1 (Sd (NonEmpty only)) x2 } } } };
unsandwich_green (Only_path (Children Hole (Green p cd s BOnly) eq_refl))
  with buffer.pop p => { | ? (x1, p1) with buffer.eject s => { 
    | ? (s1, x2) with to_pref_left cd => { | ? Pref_left pkt t eq_refl := 
    (* If we remove eq_refl, equations fail with "Constructor is applied to too 
       many arguments", when in fact it is the opposite. *)
      let only := Only_path (Children (Yellow p1 pkt s1 BOnly) t _) in 
      ? Sandwich x1 (Sd (NonEmpty only)) x2 } } };
unsandwich_green (Only_path (Children (Yellow p pkt s BOnly) t eq_refl))
  with buffer.pop p => { | ? (x1, p1) with buffer.eject s => {
    | ? (s1, x2) with to_pref_right pkt t _ => { | ? Pref_right pkt' t' eq_refl := 
      let only := Only_path (Children (Orange p1 pkt' s1 BOnly) t' _) in 
      ? Sandwich x1 (Sd (NonEmpty only)) x2 } } };
unsandwich_green (Only_path (Children (Orange p pkt s BOnly) t eq_refl))
  with buffer.pop p => { | ? (x1, p1) with buffer.eject s => {
    | ? (s1, x2) with no_pref pkt t _ => { | ? cd := 
      let only := Only_path (Children Hole (Red p1 cd s1 BOnly) eq_refl) in
      ? Sandwich x1 (Sd (NonEmpty only)) x2 } } };
unsandwich_green (Pair_green pl pr) with pop_green_left pl => {
  | ? (x1, Six x2 x3 x4 x5 x6 x7) with eject_green_right pr => {
    | ? (Six x8 x9 x10 x11 x12 x13, x14) with buffer.empty => {
      | ? b with buffer.push6 x8 x9 x10 x11 x12 x13 b => {
        | ? b1 with buffer.push6 x2 x3 x4 x5 x6 x7 b1 => {
          | ? b2 := 
            let only := Only_path (Children Hole (Small b2 b SOnly) eq_refl) in
            ? Sandwich x1 (Sd (NonEmpty only)) x14 } } };
    | ? (AnyColor pr1, x8) with semi_of_right x2 x3 x4 x5 x6 x7 pr1 => {
      | ? sd := ? Sandwich x1 sd x8 } };
  | ? (x1, AnyColor pl1) with eject_green_right pr => {
    | ? (Six x2 x3 x4 x5 x6 x7, x8) with semi_of_left pl1 x2 x3 x4 x5 x6 x7 => {
      | ? sd := ? Sandwich x1 sd x8 };
    | ? (AnyColor pr1, x2) := 
      ? Sandwich x1 (Sd (NonEmpty (Pair_red pl1 pr1))) x2 } }.
Next Obligation.
  pose (buffer.empty_buffer s) as H; rewrite H; cbn.
  rewrite <-y; rewrite <-e; hauto db:rlist.
Qed.
Next Obligation.
  pose (buffer.empty_buffer s) as H; rewrite H; cbn.
  rewrite <-y; rewrite <-e; hauto db:rlist.
Qed.
Next Obligation. Qed.
Next Obligation.
  aac_rewrite e; hauto db:rlist.
Qed.

Equations unsandwich_stored {A lvl} (cd : non_empty_cdeque A (S lvl) green) :
  { us : unstored_sandwich A lvl | unstored_sandwich_seq us = ne_cdeque_seq cd } :=
unsandwich_stored cd with unsandwich_green cd => {
  | ? Alone (ST_small p) := ? Unstored_alone p;
  | ? Alone (ST_triple p cd1 s) := ? Unstored_sandwich p (Sd cd1) s;
  | ? Sandwich (ST_small p) sd (ST_small s) := ? Unstored_sandwich p sd s;
  | ? Sandwich (ST_small p) sd (ST_triple p1 cd1 s) 
    with inject_semi sd (ST_small p1) => { | ? sd1 with concat_semi sd1 (Sd cd1) => {
      | ? sd2 := ? Unstored_sandwich p sd2 s } };
  | ? Sandwich (ST_triple p cd1 s1) sd (ST_small s) 
    with push_semi (ST_small s1) sd => { | ? sd1 with concat_semi (Sd cd1) sd1 => {
      | ? sd2 := ? Unstored_sandwich p sd2 s } };
  | ? Sandwich (ST_triple p cdl sl) sd (ST_triple pr cdr s) 
    with push_semi (ST_small sl) sd => { 
      | ? sd1 with inject_semi sd1 (ST_small pr) => {
        | ? sd2 with concat_semi (Sd cdl) sd2 => { 
          | ? sd3 with concat_semi sd3 (Sd cdr) => {
            | ? sd4 := ? Unstored_sandwich p sd4 s } } } } }.

Equations only_small {A lvl qp qs} 
  (p : prefix A lvl (8 + qp)) 
  (s : suffix A lvl (8 + qs)) :
  { t : triple A lvl 0 false Only Only green | 
    triple_seq t = buffer_seq p ++ buffer_seq s } :=
only_small p s with buffer.has3p8 s => {
  | ? inl (x1, x2, x3, x4, x5, x6, x7, x8, v) 
    with buffer.inject8 p x1 x2 x3 x4 x5 x6 x7 x8 => {
      | ? p1 with buffer.inject_vector p1 v, buffer.empty => {
          | ? p2, ? s2 := ? Small p2 s2 SOnly } };
  | ? inr (x1, x2, x3, s1) with buffer.triple x1 x2 x3 => {
    | ? b with only_single (ST_small b) => {
      | ? cd := ? Green p cd s1 BOnly } } }.

Equations only_green {A lvl qp qs} 
  (p : prefix A lvl (8 + qp))
  (sd : sdeque A (S lvl))
  (s : suffix A lvl (8 + qs)) :
  { t : triple A lvl 0 false Only Only green | 
    triple_seq t = buffer_seq p ++ sdeque_seq sd ++ buffer_seq s } :=
only_green p (Sd Empty) s with only_small p s => { | ? t := ? t };
only_green p (Sd (NonEmpty cd)) s := ? Green p cd s BOnly.

#[local] Obligation Tactic := 
  cbn; intros; autorewrite with rlist;
  try simp triple_seq in *;
  try simp packet_front_seq packet_rear_seq in *;
  autorewrite with rlist in *;
  try simp buffer_seq in *; 
  try (rewrite_seq; hauto db:rlist). 
  
  (* Returns an error for obligations : hauto failed. *)

Equations green_of_red_only {A lvl} (t : triple A lvl 0 false Only Only red) :
  { t' : triple A lvl 0 false Only Only green | triple_seq t' = triple_seq t } :=
green_of_red_only (Red p cd s BOnly) with buffer.has8 p, buffer.has8 s => {
  | ? inl (x1, x2, x3, x4, x5, vp), ? inl (y1, y2, y3, y4, y5, vs) 
    with unsandwich_stored cd => {
      | ? Unstored_alone center with buffer.push5_vector x1 x2 x3 x4 x5 vp center => {
        | ? center1 with buffer.inject5_vector center1 y1 y2 y3 y4 y5 vs, buffer.empty => {
            | ? center2, ? empty := ? Small center2 empty SOnly } };
      | ? Unstored_sandwich p1 sd s1 
        with buffer.push5_vector x1 x2 x3 x4 x5 vp p1 => {
          | ? p2 with buffer.inject5_vector s1 y1 y2 y3 y4 y5 vs => {
            | ? s2 with only_green p2 sd s2 => { | ? t := ? t } } } };
  | ? inl (x1, x2, x3, x4, x5, vp), ? inr s1 with pop_stored cd => {
    | ? Unstored p1 sd with buffer.push5_vector x1 x2 x3 x4 x5 vp p1 => {
      | ? p2 with only_green p2 sd s1 => { | ? t := ? t } } };
  | ? inr p1, ? inl (y1, y2, y3, y4, y5, vs) with eject_stored cd => {
    | ? Unstored s1 sd with buffer.inject5_vector s1 y1 y2 y3 y4 y5 vs => {
      | ? s2 with only_green p1 sd s2 => { | ? t := ? t } } };
  | ? inr p1, ? inr s1 := ? Green p1 cd s1 BOnly }.
Next Obligation. Qed.
Next Obligation. Qed.
Next Obligation. Qed.
Next Obligation. Qed.

Equations green_of_red_left {A lvl} (t : triple A lvl 0 false Left Left red) :
  { t' : triple A lvl 0 false Left Left green | triple_seq t' = triple_seq t } :=
green_of_red_left (Red p cd s BLeft) with buffer.has8 p => {
  | ? inl (x1, x2, x3, x4, x5, vp) with pop_stored cd => {
    | ? Unstored p1 (Sd cd1) with buffer.push5_vector x1 x2 x3 x4 x5 vp p1 => {
      | ? p2 with cd1 => {
        | Empty := ? Small p2 s SLeft; 
        | NonEmpty cd1' := ? Green p2 cd1' s BLeft } } };
  | ? inr p1 := ? Green p1 cd s BLeft }.

Equations green_of_red_right {A lvl} (t : triple A lvl 0 false Right Right red) :
  { t' : triple A lvl 0 false Right Right green | triple_seq t' = triple_seq t } :=
green_of_red_right (Red p cd s BRight) with buffer.has8 s => {
  | ? inl (y1, y2, y3, y4, y5, vs) with eject_stored cd => {
    | ? Unstored s1 (Sd cd1) with buffer.inject5_vector s1 y1 y2 y3 y4 y5 vs => {
      | ? s2 with cd1 => {
        | Empty := ? Small p s2 SRight;
        | NonEmpty cd1' := ? Green p cd1' s2 BRight } } };
  | ? inr s1 := ? Green p cd s1 BRight }.
Next Obligation. Qed.
Next Obligation. Qed.

#[local] Obligation Tactic :=
  try first [ done | 
    cbn beta iota delta zeta; intros; 
    try simp triple_seq in *;
    autorewrite with rlist;
    try simp buffer_seq in *;
    hauto db:rlist ].

Equations ensure_green {A lvl} (K : kind) (G : green_hue) (R : red_hue) 
  (t : triple A lvl 0 false K K (Mix G NoYellow NoOrange R)) :
  { t' : triple A lvl 0 false K K green | triple_seq t' = triple_seq t } :=
ensure_green _ SomeGreen NoRed t := ? t;
ensure_green Only NoGreen SomeRed t with green_of_red_only t => { 
  | ? t' := ? t' };
ensure_green Left NoGreen SomeRed t with green_of_red_left t => {
  | ? t' := ? t' };
ensure_green Right NoGreen SomeRed t with green_of_red_right t => {
  | ? t' := ? t' }.
Arguments ensure_green {A lvl K G R}.

Equations ensure_green_path {A lvl K C} (p : path A lvl K C) :
  { p' : path A lvl K green | path_seq p' = path_seq p } :=
ensure_green_path (Children natur adopt eq_refl) with ensure_green adopt => {
  | ? adopt' := ? Children natur adopt' eq_refl }.

Equations ensure_green_cdeque {A lvl C} (cd : non_empty_cdeque A lvl C) :
  { cd' : non_empty_cdeque A lvl green | ne_cdeque_seq cd' = ne_cdeque_seq cd } :=
ensure_green_cdeque (Only_path p) with ensure_green_path p => {
  | ? p' := ? Only_path p' };
ensure_green_cdeque (Pair_green pl pr) := ? Pair_green pl pr;
ensure_green_cdeque (Pair_red pl pr) 
  with ensure_green_path pl, ensure_green_path pr => {
    | ? pl', ? pr' := ? Pair_green pl' pr' }.

Equations regular_of_semi {A} (sd : sdeque A 0) : 
  { d : deque A | deque_seq d = sdeque_seq sd } :=
regular_of_semi (Sd Empty) := ? T Empty;
regular_of_semi (Sd (NonEmpty cd)) with ensure_green_cdeque cd => {
  | ? cd' := ? T (NonEmpty cd') }.

Equations pop {A} (d : deque A) : 
  { o : option (A * deque A) | 
    match o with 
    | None => []
    | Some (x, d') => [x] ++ deque_seq d' 
    end = deque_seq d } := 
pop (T Empty) := ? None;
pop (T (NonEmpty cd)) with pop_green cd => {
  | ? (ST_ground x, sd) with regular_of_semi sd => {
    | ? d' := ? Some (x, d') } }.

Equations eject {A} (d : deque A) :
  { o : option (deque A * A) | 
    match o with 
    | None => [] 
    | Some (d', x) => deque_seq d' ++ [x] 
    end = deque_seq d } :=
eject (T Empty) := ? None;
eject (T (NonEmpty cd)) with eject_green cd => {
  | ? (sd, ST_ground x) with regular_of_semi sd => {
    | ? d' := ? Some (d', x) } }.