From Coq Require Import ssreflect.
From Coq Require Import Program List Arith Lia.
Import ListNotations.
From Equations Require Import Equations.
From Hammer Require Import Tactics.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

(* Pas besoin de gérer des power2 lvl en vrai;
   Utiliser égalités dans les arguments des fonctions pour simplifier les preuves. *)

(* Types *)

(* Here, [green_hue], [yellow_hue], and [red_hue] will be utilized to generate 
   the colors essential for our program. They function as boolean variables, 
   indicating whether or not a specific hue is present in our color. *)

Inductive green_hue  : Type := SomeGreen  | NoGreen.
Inductive yellow_hue : Type := SomeYellow | NoYellow.
Inductive red_hue    : Type := SomeRed    | NoRed.

(* Colors are generated through the constructor [Mix], which accepts amount 
   of each hue as arguments. *)

Inductive color : Type :=
  | Mix : green_hue -> yellow_hue -> red_hue -> color.

(* In order for [Equations] to work on hues and colors, instances of 
   [NoConfusion] are added to these types. *)

Derive NoConfusion for green_hue.
Derive NoConfusion for yellow_hue.
Derive NoConfusion for red_hue.
Derive NoConfusion for color.

(* Some basic colors that we'll need. *)

Notation green := (Mix SomeGreen NoYellow NoRed).
Notation yellow := (Mix NoGreen SomeYellow NoRed).
Notation red := (Mix NoGreen NoYellow SomeRed).
Notation uncolored := (Mix NoGreen NoYellow NoRed).

(* A type for iterated products. *)

Inductive prodN (A : Type) : nat -> Type := 
  | prodZ : A -> prodN A 0 
  | prodS {n : nat} : prodN A n -> prodN A n -> prodN A (S n).
Arguments prodZ {A}.
Arguments prodS {A n}.

(* In the following types, an integer parameter is introduced : the [size] of
   the type. The size is simply the number of [prodN A lvl] that are stored in
   the structure encoded. *)

(* A type for sized buffers. *)

Inductive buffer (A : Type) (lvl : nat) : nat -> color -> Type :=
  | B0 : buffer A lvl 0 red
  | B1 : prodN A lvl -> buffer A lvl 1 yellow
  | B2 {G Y} : prodN A lvl -> prodN A lvl -> buffer A lvl 2 (Mix G Y NoRed)
  | B3 {G Y} : prodN A lvl -> prodN A lvl -> prodN A lvl -> buffer A lvl 3 (Mix G Y NoRed)
  | B4 : prodN A lvl -> prodN A lvl -> prodN A lvl -> prodN A lvl -> buffer A lvl 4 yellow
  | B5 : prodN A lvl -> prodN A lvl -> prodN A lvl -> prodN A lvl -> prodN A lvl -> buffer A lvl 5 red.
Arguments B0 {A lvl}.
Arguments B1 {A lvl}.
Arguments B2 {A lvl G Y}.
Arguments B3 {A lvl G Y}.
Arguments B4 {A lvl}.
Arguments B5 {A lvl}.

(* A type for yellow buffers. *)

Inductive yellow_buffer (A: Type) (lvl : nat) (size : nat) : Type :=
  | Yellowish : forall {G Y},
    buffer A lvl size (Mix G Y NoRed) ->
    yellow_buffer A lvl size.
Arguments Yellowish {A lvl size G Y}.

(* A type for any buffers. *)

Inductive any_buffer (A: Type) (lvl : nat) (size : nat) : Type :=
  | Any : forall {C}, buffer A lvl size C -> any_buffer A lvl size.
Arguments Any {A lvl size C}.

(* A relation between the prefix, suffix and packet colors. *)

Inductive packet_color : color -> color -> color -> Type := 
  | PCGreen : packet_color green green green
  | PCYellow {G1 Y1 G2 Y2} : packet_color (Mix G1 Y1 NoRed) (Mix G2 Y2 NoRed) yellow 
  | PCRed {C1 C2 : color} : packet_color C1 C2 red.

(* A type for packet. As the level of the child packet is increased by one, 
   it contains elements of type [prodN A (S lvl)] that account for two elements
   of type [prodN A lvl]. Hence, the size of the child packet is counted twice
   in the size of our final packet of level [lvl]. *)

Inductive packet (A : Type) (lvl : nat) : nat -> nat -> color -> Type :=
  | Hole : packet A lvl 0 0 uncolored
  | Triple {len psize pktsize ssize : nat} {Y : yellow_hue} {C1 C2 C3 : color} :
      buffer A lvl psize C1 ->
      packet A (S lvl) len pktsize (Mix NoGreen Y NoRed) ->
      buffer A lvl ssize C2 ->
      packet_color C1 C2 C3 ->
      packet A lvl (S len) (psize + pktsize + pktsize + ssize) C3.
Arguments Hole {A lvl}.
Arguments Triple {A lvl len psize pktsize ssize Y C1 C2 C3}.

(* [power2] computes 2 to the power of a natural number. *)

Equations power2 : nat -> nat :=
power2 0 := 1;
power2 (S n) := let p := power2 n in p + p.
Transparent power2.

(* A relation between the head packet and the following deque colors. *)

Inductive cdeque_color : color -> color -> Type := 
  | CCGreen {G R} : cdeque_color green (Mix G NoYellow R)
  | CCYellow : cdeque_color yellow green 
  | CCRed : cdeque_color red green.

(* A type for sized colored deque. The same reasonning as the one for packets
   apply here. Each elements of the next colored deque accounts for [power2
   len] elements of type [prodN A lvl]. So the size of the next colored deque
   is multiplied by [power2 len] to compute the correct size for our colored
   deque. *)

Inductive cdeque (A : Type) (lvl : nat) : nat -> color -> Type :=
  | Small {size : nat} {C : color} : 
      buffer A lvl size C -> 
      cdeque A lvl size green
  | Big {len pktsize nlvl nsize size : nat} {C1 C2 : color} :
      packet A lvl len pktsize C1 -> 
      cdeque A nlvl nsize C2 ->
      nlvl = len + lvl -> 
      size = pktsize + (power2 len) * nsize ->
      cdeque_color C1 C2 ->
      cdeque A lvl size C1.
Arguments Small {A lvl size C}.
Arguments Big {A lvl len pktsize nlvl nsize size C1 C2}.

(* This function compute the size of an option. 0 if it is [None], 1 if it is
   [Some _]. *)

Equations size_option {A : Type} (o : option A) : nat :=
size_option None := 0;
size_option (Some _) := 1.
Transparent size_option.

(* The sized decompose type. *)

Inductive decompose (A : Type) (lvl : nat) : nat -> Type :=
  | Underflow : forall (o : option (prodN A lvl)), decompose A lvl (size_option o)
  | Ok {size : nat} : buffer A lvl size green -> decompose A lvl size
  | Overflow {size : nat} : 
    buffer A lvl size green -> prodN A (S lvl) -> decompose A lvl (2 + size).
Arguments Underflow {_ _}.
Arguments Ok {_ _ _}.
Arguments Overflow {_ _ _}.

(* The sized sandwich type. *)

Inductive sandwich (A : Type) (lvl : nat) : nat -> Type :=
  | Alone : forall (o : option (prodN A lvl)), sandwich A lvl (size_option o)
  | Sandwich {size C} : 
    prodN A lvl -> buffer A lvl size C -> prodN A lvl -> sandwich A lvl (2 + size).
Arguments Alone {A lvl}.
Arguments Sandwich {A lvl size C}.

(* A type for sized deque. *)

Inductive deque (A : Type) (size : nat) : Type := 
  T : forall (G : green_hue) (Y : yellow_hue), 
      cdeque A 0 size (Mix G Y NoRed) -> 
      deque A size.
Arguments T {A size G Y}.

(* Models *)

Set Equations Transparent.

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

#[local] Obligation Tactic :=
  try first [ done | cbn; hauto db:rlist ].

(* Returns the sequence contained in a product. *)

Equations prodN_seq {A} (n : nat) : prodN A n -> list A := 
prodN_seq 0 (prodZ a) := [a];
prodN_seq (S n) (prodS p1 p2) := prodN_seq n p1 ++ prodN_seq n p2.
Arguments prodN_seq {A n}.

(* Returns the sequence contained in an option. *)

Equations option_seq {A lvl} : option (prodN A lvl) -> list A :=
option_seq None := [];
option_seq (Some x) := prodN_seq x.

(* Returns the sequence contained in a buffer. *)

Equations buffer_seq {A lvl size C} : buffer A lvl size C -> list A :=
buffer_seq B0 := [];
buffer_seq (B1 a) := prodN_seq a;
buffer_seq (B2 a b) := prodN_seq a ++ prodN_seq b;
buffer_seq (B3 a b c) := prodN_seq a ++ prodN_seq b ++ prodN_seq c;
buffer_seq (B4 a b c d) := prodN_seq a ++ prodN_seq b ++ prodN_seq c ++ prodN_seq d;
buffer_seq (B5 a b c d e) := 
  prodN_seq a ++ prodN_seq b ++ prodN_seq c ++ prodN_seq d ++ prodN_seq e.

(* Returns the sequence contained in a yellow buffer. *)

Equations yellow_buffer_seq {A lvl size} : yellow_buffer A lvl size -> list A :=
yellow_buffer_seq (Yellowish buf) := buffer_seq buf.

(* Returns the sequence contained in any buffer. *)

Equations any_buffer_seq {A lvl size} : any_buffer A lvl size -> list A :=
any_buffer_seq (Any buf) := buffer_seq buf.

(* Returns the sequence of elements stored in prefix buffers along a 
   packet. *)

Equations packet_front_seq {A lvl len size C} : packet A lvl len size C -> list A :=
packet_front_seq Hole := [];
packet_front_seq (Triple buf1 p _ _) := 
  buffer_seq buf1 ++ packet_front_seq p.

(* Returns the sequence of elements stored in suffix buffers along a 
   packet. *)

Equations packet_rear_seq {A lvl len size C} : packet A lvl len size C -> list A :=
packet_rear_seq Hole := [];
packet_rear_seq (Triple _ p buf2 _) := 
  packet_rear_seq p ++ buffer_seq buf2.

(* Returns the sequence contained in a colored deque. *)

Equations cdeque_seq {A lvl size C} : cdeque A lvl size C -> list A :=
cdeque_seq (Small buf) := buffer_seq buf;
cdeque_seq (Big p cd _ _ _) := 
    packet_front_seq p ++
    cdeque_seq cd ++
    packet_rear_seq p.

(* Returns the sequence of non-excess elements of an object of type decompose. *)

Equations decompose_main_seq {A lvl size} (dec : decompose A lvl size) : list A :=
decompose_main_seq (Underflow opt) := option_seq opt;
decompose_main_seq (Ok b) := buffer_seq b;
decompose_main_seq (Overflow b _) := buffer_seq b.

(* Returns the sequence of excess elements of an object of type decompose. *)

Equations decompose_rest_seq {A lvl size} (dec : decompose A lvl size) : list A :=
decompose_rest_seq (Underflow _) := [];
decompose_rest_seq (Ok _) := [];
decompose_rest_seq (Overflow _ p) := prodN_seq p.

(* Returns the sequence of elements of an object of type sandwich. *)

Equations sandwich_seq {A lvl size} (sw : sandwich A lvl size) : list A :=
sandwich_seq (Alone opt) := option_seq opt;
sandwich_seq (Sandwich x b y) := prodN_seq x ++ buffer_seq b ++ prodN_seq y.

(* Returns the sequence contained in a deque. *)

Equations deque_seq {A size} : deque A size -> list A :=
deque_seq (T dq) := cdeque_seq dq.

(* Unset Equations Transparent. *)

(* Sequence mappings *)

Definition map_deque {T : Type -> nat -> Type} {A : Type}
  (f : forall {lvl : nat}, T A lvl -> list A) 
  {lvl q : nat}
  (d : deque (T A lvl) q) : list A := 
  let fix prodN_seq {lvlt lvlp} (p : prodN (T A lvlt) lvlp) {struct p} : list A :=
    match p with 
    | prodZ z => f z
    | prodS p1 p2 => prodN_seq p1 ++ prodN_seq p2
    end in
  let buffer_seq {lvlt lvlp size C} (b : buffer (T A lvlt) lvlp size C) : list A :=
    match b with 
    | B0 => []
    | B1 p1 => prodN_seq p1
    | B2 p1 p2 => prodN_seq p1 ++ prodN_seq p2 
    | B3 p1 p2 p3 => prodN_seq p1 ++ prodN_seq p2 ++ prodN_seq p3
    | B4 p1 p2 p3 p4 => 
      prodN_seq p1 ++ prodN_seq p2 ++ prodN_seq p3 ++ prodN_seq p4
    | B5 p1 p2 p3 p4 p5 => 
      prodN_seq p1 ++ prodN_seq p2 ++ prodN_seq p3 ++ prodN_seq p4 ++ prodN_seq p5
    end in 
  let fix packet_front_seq {lvlt lvlp len size C} 
      (pkt : packet (T A lvlt) lvlp len size C) {struct pkt} : list A :=
    match pkt with 
    | Hole => []
    | Triple p pkt _ _ => buffer_seq p ++ packet_front_seq pkt 
    end in
  let fix packet_rear_seq {lvlt lvlp len size C} 
      (pkt : packet (T A lvlt) lvlp len size C) {struct pkt} : list A :=
    match pkt with 
    | Hole => []
    | Triple _ pkt s _ => packet_rear_seq pkt ++ buffer_seq s
    end in
  let fix cdeque_seq {lvlt lvlp size C} 
      (cd : cdeque (T A lvlt) lvlp size C) {struct cd} : list A :=
    match cd with
    | Small b => buffer_seq b
    | Big pkt cd _ _ _ => 
      packet_front_seq pkt ++ 
      cdeque_seq cd ++ 
      packet_rear_seq pkt
    end in
  match d with 
  | T cd => cdeque_seq cd
  end.

(* A lemma that destructs an equality of one app into 2 subgoals. *)

Lemma div_app2 {A : Type} {l1 l1' l2 l2' : list A} : 
    l1 = l1' -> l2 = l2' -> l1 ++ l2 = l1' ++ l2'.
Proof. intros [] []; reflexivity. Defined.

(* A tactic that cleans the removes the useless hypothesis. *)

Local Ltac clear_h := 
  repeat 
  match goal with
  | H : _ |- _ => clear H
  end.

Lemma correct_mapping {T : Type -> nat -> Type} {A : Type} 
  (f : forall {lvl : nat}, T A lvl -> list A)
  {lvl q : nat}
  (d : deque (T A lvl) q) : 
  map_deque (@f) d = concat (map f (deque_seq d)).
Proof.
  (* Destruction of the deque. *)
  destruct d as [G Y cd]; cbn;
  (* Induction on the cdeque. *)
  induction cd as [lvlp size C b | lvlp len pktsize nlvl nsize size C1 C2 pkt cd IHcd elvl esize cc]; 
  (* Format for simplification. *)
  cbn; autorewrite with rlist;
  (* Handling the Big case, with packets and a following cdeque. *)
  try (repeat apply div_app2; 
  (* The following cdeque case is handled by induction. *)
  [clear_h | apply IHcd | clear_h];
  (* Induction on the packet. *)
  induction pkt as [ | lvlp ???????? p pkt IHpkt s pc];
  (* Hole cases. *)
  try reflexivity;
  (* Format for simplification. *)
  cbn; autorewrite with rlist;
  (* Separate buffer and following packet cases. *)
  apply div_app2;
  (* Following packet cases are handled by induction. *)
  [clear_h; rename p into b | apply IHpkt | apply IHpkt | clear_h; rename s into b]);
  (* Case by case on buffers. *)
  destruct b; 
  (* Format for simplification. *)
  cbn; autorewrite with rlist;
  (* Simple B0 cases are handled. *)
  try reflexivity;
  (* Separate multi-app goals into subgoals. *)
  repeat apply div_app2; clear_h;
  (* Prove the remaining by induction on the right prodN. *)
  (match goal with 
  | _ : _ |- _ = concat (map (f lvl) (prodN_seq ?p)) => induction p
  end);
  (* Finish all the cases with hauto. *)
  cbn; hauto db:rlist.
Defined.

Notation "? x" := (@exist _ _ x _) (at level 100).

(* Lemmas *)

(* Proves that for any natural number [n], [power2 n] is different from 0. *)

Lemma power2_neq0 {n : nat} : power2 n <> 0.
Proof. induction n; simpl; lia. Defined.

(* Takes a product and links its level to the length of its sequence. *)

Lemma prodN_size {A lvl} (p : prodN A lvl) :
    length (prodN_seq p) = power2 lvl.
Proof. 
  induction p.
  - reflexivity.
  - simp prodN_seq; simpl power2;
    rewrite app_length;
    rewrite IHp1; rewrite IHp2;
    reflexivity.
Defined.

(* Takes an option of products and links its level and size to the length of its 
   sequence. *)

Lemma option_size {A lvl} (o : option (prodN A lvl)) :
    length (option_seq o) = size_option o * power2 lvl.
Proof. 
  destruct o; simp option_seq; try reflexivity; 
  simp size_option; rewrite Nat.mul_1_l; apply prodN_size.
Defined.

(* Takes a buffer and links its level and size to the length of its sequence. *)

Lemma buffer_size {A lvl size C} (b : buffer A lvl size C) :
    length (buffer_seq b) = size * power2 lvl.
Proof.
  dependent elimination b;
  simp buffer_seq;
  repeat rewrite app_length;
  repeat rewrite prodN_size; 
  cbn; lia.
Defined.

(* Proves that if a buffer is empty, its size is 0. *)

Lemma empty_buffer_size {A lvl size C} (b : buffer A lvl size C) :
    buffer_seq b = [] -> size = 0.
Proof.
  intros e%(f_equal (@length _)); rewrite buffer_size in e;
  apply Nat.mul_eq_0_l in e.
  - assumption.
  - apply power2_neq0.
Defined.

(* Takes a packet and links its level and size to the length of its sequence. *)

Lemma packet_size {A lvl len size C} (pkt : packet A lvl len size C) :
    length (packet_front_seq pkt ++ packet_rear_seq pkt) = size * power2 lvl.
Proof.
  induction pkt.
  - reflexivity.
  - simp packet_front_seq packet_rear_seq;
    autorewrite with rlist;
    rewrite app_length;
    rewrite app_assoc; rewrite app_length;
    repeat rewrite buffer_size;
    do 2 rewrite Nat.mul_add_distr_r;
    rewrite IHpkt; cbn; lia.
Defined.

(* A simple lemma to better control list concatenation. *)

Lemma app_cons {A : Type} (a : A) (l : list A) :
    a :: l = [a] ++ l.
Proof. reflexivity. Defined.

(* Proves the commutation of list under the length function. *)

Lemma length_app_comm {A : Type} (l1 l2 : list A) :
    length (l1 ++ l2) = length (l2 ++ l1).
Proof.
  induction l1 as [ | a l1]; try rewrite app_cons; 
  repeat rewrite app_length; lia.
Defined.

(* Proves that 2 ^ (n + m) is indeed equal to 2 ^ n * 2 ^ m. *)

Lemma power2_add {n m : nat} : power2 (n + m) = power2 n * power2 m.
Proof.
  induction n; simpl.
  - lia.
  - rewrite IHn Nat.mul_add_distr_r; reflexivity.
Defined.

(* Takes a colored deque and links its level and size to the length of its
   sequence. *)

Lemma cdeque_size {A lvl size C} (cd : cdeque A lvl size C) : 
    length (cdeque_seq cd) = size * power2 lvl.
Proof.
  induction cd; simp cdeque_seq.
  - apply buffer_size.
  - rewrite app_assoc length_app_comm app_assoc app_length length_app_comm packet_size;
    rewrite IHcd e e0 power2_add; lia.
Defined.

(* Takes a deque and links its size to the length of its sequence. *)

Lemma deque_size {A size} (d : deque A size) : length (deque_seq d) = size.
Proof. destruct d; simp deque_seq; rewrite cdeque_size; simpl; lia. Defined.

(* Elements *)

(* The empty colored deque. *)

Equations cempty {A lvl} : { cd : cdeque A lvl 0 green | cdeque_seq cd = [] } :=
cempty := ? Small B0.

(* The empty deque. *)

Equations empty {A} : { d : deque A 0 | deque_seq d = [] } :=
empty with cempty => { | ? cd := ? T cd }.

(* Functions *)

#[local] Obligation Tactic :=
  try first [ done | cbn; hauto db:rlist ].

(* Pushing on a green buffer. *)

Equations green_push {A lvl size} 
  (x : prodN A lvl) (b : buffer A lvl size green) :
  { b' : buffer A lvl (S size) yellow | 
    buffer_seq b' = prodN_seq x ++ buffer_seq b } :=
green_push x (B2 a b) := ? B3 x a b;
green_push x (B3 a b c) := ? B4 x a b c.

(* Injecting on a green buffer. *)

Equations green_inject {A lvl size} 
  (b : buffer A lvl size green) (x : prodN A lvl) :
  { b' : buffer A lvl (S size) yellow | 
    buffer_seq b' = buffer_seq b ++ prodN_seq x } :=
green_inject (B2 a b) x := ? B3 a b x;
green_inject (B3 a b c) x := ? B4 a b c x.

(* Poping from a green buffer. *)

Equations green_pop {A lvl size} (b : buffer A lvl size green) :
  { '(x, b') : prodN A lvl * yellow_buffer A lvl (Nat.pred size) | 
    buffer_seq b = prodN_seq x ++ yellow_buffer_seq b' } :=
green_pop (B2 a b) => ? (a, (Yellowish (B1 b)));
green_pop (B3 a b c) => ? (a, (Yellowish (B2 b c))).

(* Ejecting from a green buffer. *)

Equations green_eject {A lvl size} (b : buffer A lvl size green) :
  { '(b', x) : yellow_buffer A lvl (Nat.pred size) * prodN A lvl | 
    buffer_seq b = yellow_buffer_seq b' ++ prodN_seq x } :=
green_eject (B2 a b) => ? ((Yellowish (B1 a)), b);
green_eject (B3 a b c) => ? ((Yellowish (B2 a b)), c).

(* Pushing on a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_push {A lvl size} 
  (x : prodN A lvl) (b : yellow_buffer A lvl size) :
  { b' : any_buffer A lvl (S size) | 
    any_buffer_seq b' = prodN_seq x ++ yellow_buffer_seq b } :=
yellow_push x (Yellowish buf) with buf => {
  | B1 a => ? Any (B2 x a);
  | B2 a b => ? Any (B3 x a b);
  | B3 a b c => ? Any (B4 x a b c);
  | B4 a b c d => ? Any (B5 x a b c d)
}.

(* Injecting on a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_inject {A lvl size}
  (b : yellow_buffer A lvl size) (x : prodN A lvl) :
  { b' : any_buffer A lvl (S size) | 
    any_buffer_seq b' = yellow_buffer_seq b ++ prodN_seq x } :=
yellow_inject (Yellowish buf) x with buf := {
  | B1 a => ? Any (B2 a x);
  | B2 a b => ? Any (B3 a b x);
  | B3 a b c => ? Any (B4 a b c x);
  | B4 a b c d => ? Any (B5 a b c d x)
}.

(* Poping from a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_pop {A lvl size} (b : yellow_buffer A lvl size) :
  { '(x, b') : prodN A lvl * any_buffer A lvl (Nat.pred size) | 
    yellow_buffer_seq b = prodN_seq x ++ any_buffer_seq b' } :=
yellow_pop (Yellowish buf) with buf => {
  | B1 a => ? (a, Any B0);
  | B2 a b => ? (a, Any (B1 b));
  | B3 a b c => ? (a, Any (B2 b c));
  | B4 a b c d => ? (a, Any (B3 b c d))
}.

(* Ejecting from a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_eject {A lvl size} (b : yellow_buffer A lvl size) :
  { '(b', x) : any_buffer A lvl (Nat.pred size) * prodN A lvl | 
    yellow_buffer_seq b = any_buffer_seq b' ++ prodN_seq x } :=
yellow_eject (Yellowish buf) with buf => {
  | B1 a => ? (Any B0, a);
  | B2 a b => ? (Any (B1 a), b);
  | B3 a b c => ? (Any (B2 a b), c);
  | B4 a b c d => ? (Any (B3 a b c), d)
}.

(* Pushing on a buffer. *)

Equations buffer_push {A lvl size C} (x : prodN A lvl) (b : buffer A lvl size C) :
  { cd : cdeque A lvl (S size) green | 
    cdeque_seq cd = prodN_seq x ++ buffer_seq b } :=
buffer_push x B0 := ? Small (B1 x);
buffer_push x (B1 a) := ? Small (B2 x a);
buffer_push x (B2 a b) := ? Small (B3 x a b);
buffer_push x (B3 a b c) := ? Small (B4 x a b c);
buffer_push x (B4 a b c d) := ? Small (B5 x a b c d);
buffer_push x (B5 a b c d e) := 
  ? Big (Triple (B3 x a b) Hole (B3 c d e) PCGreen) (Small B0) eq_refl _ CCGreen. 

(* Injecting on a buffer. *)

Equations buffer_inject {A lvl size C} (b : buffer A lvl size C) (x : prodN A lvl) :
  { cd : cdeque A lvl (S size) green | 
    cdeque_seq cd = buffer_seq b ++ prodN_seq x } :=
buffer_inject B0 x := ? Small (B1 x);
buffer_inject (B1 a) x := ? Small (B2 a x);
buffer_inject (B2 a b) x := ? Small (B3 a b x);
buffer_inject (B3 a b c) x := ? Small (B4 a b c x);
buffer_inject (B4 a b c d) x := ? Small (B5 a b c d x);
buffer_inject (B5 a b c d e) x := 
  ? Big (Triple (B3 a b c) Hole (B3 d e x) PCGreen) (Small B0) eq_refl _ CCGreen.

(* Poping from a buffer. *)
  
Equations buffer_pop {A lvl size C} (b : buffer A lvl size C) :
  { o : option (prodN A lvl * any_buffer A lvl (Nat.pred size)) |
    buffer_seq b =
    match o with
    | None => []
    | Some (x, b') => prodN_seq x ++ any_buffer_seq b'
    end } :=
buffer_pop B0 := ? None;
buffer_pop (B5 a b c d e) := ? Some (a, Any (B4 b c d e));
buffer_pop buf with yellow_pop (Yellowish buf) => { | ? o := ? Some o }.

(* Ejecting from a buffer. *)

Equations buffer_eject {A lvl size C} (b : buffer A lvl size C) :
  { o : option (any_buffer A lvl (Nat.pred size) * prodN A lvl) |
    buffer_seq b =
    match o with
    | None => []
    | Some (b', x) => any_buffer_seq b' ++ prodN_seq x
    end } :=
buffer_eject (B5 a b c d e) := ? Some (Any (B4 a b c d), e);
buffer_eject B0 := ? None;
buffer_eject buf with yellow_eject (Yellowish buf) => { | ? o := ? Some o }.

(* Pushes then ejects. *)

Equations prefix_rot {A lvl size C} (x : prodN A lvl) (b : buffer A lvl size C) :
  { '(b', y) : buffer A lvl size C * prodN A lvl | 
    prodN_seq x ++ buffer_seq b = buffer_seq b' ++ prodN_seq y } :=
prefix_rot x B0 := ? (B0, x);
prefix_rot x (B1 a) := ? (B1 x, a);
prefix_rot x (B2 a b) := ? (B2 x a, b);
prefix_rot x (B3 a b c) := ? (B3 x a b, c);
prefix_rot x (B4 a b c d) := ? (B4 x a b c, d);
prefix_rot x (B5 a b c d e) := ? (B5 x a b c d, e).

(* Injects then pops. *)

Equations suffix_rot {A lvl size C} (b : buffer A lvl size C) (y : prodN A lvl) :
  { '(x, b') : prodN A lvl * buffer A lvl size C | 
    buffer_seq b ++ prodN_seq y = prodN_seq x ++ buffer_seq b' } :=
suffix_rot B0 x := ? (x, B0);
suffix_rot (B1 a) x := ? (a, B1 x);
suffix_rot (B2 a b) x := ? (a, B2 b x);
suffix_rot (B3 a b c) x := ? (a, B3 b c x);
suffix_rot (B4 a b c d) x := ? (a, B4 b c d x);
suffix_rot (B5 a b c d e) x := ? (a, B5 b c d e x).

(* Create a green buffer by injecting a pair onto an option. *)

Equations prefix23 {A lvl G Y} (o : option (prodN A lvl)) (p: prodN A (S lvl)) :
  { b : buffer A lvl (2 + size_option o) (Mix G Y NoRed) |
    buffer_seq b = option_seq o ++ prodN_seq p } :=
prefix23 None (prodS b c) := ? B2 b c;
prefix23 (Some a) (prodS b c) := ? B3 a b c.

(* Create a green buffer by poping a pair onto an option. *)

Equations suffix23 {A lvl G Y} (p : prodN A (S lvl)) (o : option (prodN A lvl)) :
  { b : buffer A lvl (2 + size_option o) (Mix G Y NoRed) |
    buffer_seq b = prodN_seq p ++ option_seq o } :=
suffix23 (prodS a b) None := ? B2 a b;
suffix23 (prodS a b) (Some c) := ? B3 a b c.

(* Create a yellow (or green) buffer by pushing an element onto an option. *)

Equations suffix12 {A lvl} (x : prodN A lvl) (o : option (prodN A lvl)) :
  { b : buffer A lvl (S (size_option o)) yellow | 
    buffer_seq b = prodN_seq x ++ option_seq o } :=
suffix12 x None := ? B1 x;
suffix12 x (Some y) := ? B2 x y.

(* Returns the decomposed version of a buffer. Here, it is a prefix 
   decomposition: when the buffer is overflowed, elements at the end are 
   removed. *)

Equations prefix_decompose {A lvl size C} (b : buffer A lvl size C) :
  { dec : decompose A lvl size | 
    buffer_seq b = decompose_main_seq dec ++ decompose_rest_seq dec } :=
prefix_decompose B0 := ? Underflow None;
prefix_decompose (B1 x) := ? Underflow (Some x);
prefix_decompose (B2 a b) := ? Ok (B2 a b);
prefix_decompose (B3 a b c) := ? Ok (B3 a b c);
prefix_decompose (B4 a b c d) := ? Overflow (B2 a b) (prodS c d);
prefix_decompose (B5 a b c d e) := ? Overflow (B3 a b c) (prodS d e).

(* Returns the decomposed version of a buffer. Here, it is a suffix
   decomposition: when the buffer is overflowed, elements at the beginning are
   removed. *)

Equations suffix_decompose {A lvl size C} (b : buffer A lvl size C) :
  { dec : decompose A lvl size | 
    buffer_seq b = decompose_rest_seq dec ++ decompose_main_seq dec } :=
suffix_decompose B0 := ? Underflow None;
suffix_decompose (B1 x) := ? Underflow (Some x);
suffix_decompose (B2 a b) := ? Ok (B2 a b);
suffix_decompose (B3 a b c) := ? Ok (B3 a b c);
suffix_decompose (B4 a b c d) := ? Overflow (B2 c d) (prodS a b);
suffix_decompose (B5 a b c d e) := ? Overflow (B3 c d e) (prodS a b).

(* Returns the sandwich representation of a buffer. *)

Equations buffer_unsandwich {A lvl size C} (b : buffer A lvl size C) :
  { sw : sandwich A lvl size | buffer_seq b = sandwich_seq sw } :=
buffer_unsandwich B0 := ? Alone None;
buffer_unsandwich (B1 a) := ? Alone (Some a);
buffer_unsandwich (B2 a b) := ? Sandwich a B0 b;
buffer_unsandwich (B3 a b c) := ? Sandwich a (B1 b) c;
buffer_unsandwich (B4 a b c d) := ? Sandwich a (B2 b c) d;
buffer_unsandwich (B5 a b c d e) := ? Sandwich a (B3 b c d) e.

(* In the following, when talking about structures, we will write n-struct for
   a structure of level n. *)

(* Translates a n-buffer to a (n+1)-buffer. An additional option type is 
   returned to handle cases where the buffer contains an odd number of elements. *)

Equations buffer_halve {A lvl size C} (b : buffer A lvl size C) :
  { '(o, b') : option (prodN A lvl) * any_buffer A (S lvl) (size / 2) |
    buffer_seq b = option_seq o ++ any_buffer_seq b' } :=
buffer_halve B0 := ? (None, Any B0);
buffer_halve (B1 a) := ? (Some a, Any B0);
buffer_halve (B2 a b) := ? (None, Any (B1 (prodS a b)));
buffer_halve (B3 a b c) := ? (Some a, Any (B1 (prodS b c)));
buffer_halve (B4 a b c d) := ? (None, Any (B2 (prodS a b) (prodS c d)));
buffer_halve (B5 a b c d e) := ? (Some a, Any (B2 (prodS b c) (prodS d e))).

(* When [size1 = size2], translates a buffer of size1 to a buffer of size2. *)

Equations buffer_translate {A lvl size1 size2 C} (b : buffer A lvl size1 C) :
    size1 = size2 -> { b' : buffer A lvl size2 C | buffer_seq b' = buffer_seq b } :=
buffer_translate b eq_refl := ? b.

(* A new tactic is introduced. It destructs every option and buffer in the 
   hypothesis. It is used to prove equality on sizes, by destructing options 
   and buffers, we are left with simple equations on natural numbers. *)

Local Ltac destruct_opt_buff :=
  do 7 (try match goal with
  | o : option _ |- _ => destruct o
  | b : buffer _ _ _ green |- _ => dependent elimination b
  | b : buffer _ _ _ (Mix _ _ NoRed) |- _ => dependent elimination b
  | b : buffer _ _ _ _ |- _ => dependent elimination b
  end; cbn; try reflexivity).

#[local] Obligation Tactic :=
  try first [ done | cbn; hauto db:rlist | 
  cbn beta iota; intros; 
  repeat match goal with H : _ = _ |- _ => clear H end;
  destruct_opt_buff ].

(* Takes any n-buffer and a green (n+1)-buffer, and rearranges elements 
   contained in the two buffers to return a green n-buffer and a yellow 
   (n+1)-buffer. The order of elements is preserved. *)

Equations green_prefix_concat {A lvl size1 size2 C}
  (buf1 : buffer A lvl size1 C)
  (buf2 : buffer A (S lvl) size2 green) :
  { '(buf1', buf2') : buffer A lvl (2 + size1 mod 2) green * 
                      yellow_buffer A (S lvl) (size2 - 1 + size1 / 2) |
    buffer_seq buf1 ++ buffer_seq buf2 =
    buffer_seq buf1' ++ yellow_buffer_seq buf2' } :=
green_prefix_concat buf1 buf2 with prefix_decompose buf1 => {
  | ? Ok buf with buffer_translate buf _, buffer_translate buf2 _ => {
    | ? buf', ? buf2' := ? (buf', Yellowish buf2') };
  | ? Underflow opt with green_pop buf2 => {
    | ? (ab, Yellowish buf) with prefix23 opt ab => {
      | ? prefix with buffer_translate prefix _, buffer_translate buf _ => {
        | ? prefix', ? buf' := ? (prefix', Yellowish buf') } } };
  | ? Overflow buf ab with buffer_translate buf _, green_push ab buf2 => {
    | ? buf', ? suffix with buffer_translate suffix _ => {
      | ? suffix' := ? (buf', Yellowish suffix') } } }.
(* Next Obligation. Defined. *)

(* Takes a green (n+1)-buffer and any n-buffer, and rearranges elements 
   contained in the two buffers to return a yellow (n+1)-buffer and a green 
   n-buffer. The order of elements is preserved. *)

Equations green_suffix_concat {A lvl size1 size2 C}
  (buf1 : buffer A (S lvl) size1 green)
  (buf2 : buffer A lvl size2 C) :
  { '(buf1', buf2') : yellow_buffer A (S lvl) (size1 - 1 + size2 / 2) * 
                      buffer A lvl (2 + size2 mod 2) green |
    buffer_seq buf1 ++ buffer_seq buf2 =
    yellow_buffer_seq buf1' ++ buffer_seq buf2' } :=
green_suffix_concat buf1 buf2 with suffix_decompose buf2 => {
  | ? Ok buf with buffer_translate buf1 _, buffer_translate buf _ => {
    | ? buf1', ? buf' := ? (Yellowish buf1', buf') };
  | ? Underflow opt with green_eject buf1 => {
    | ? (Yellowish buf, ab) with suffix23 ab opt => {
      | ? suffix with buffer_translate buf _, buffer_translate suffix _ => {
      | ? buf', ? suffix' := ? (Yellowish buf', suffix') } } };
  | ? Overflow buf ab with green_inject buf1 ab, buffer_translate buf _ => {
    | ? prefix, ? buf' with buffer_translate prefix _ => {
      | ? prefix' := ? (Yellowish prefix', buf') } } }.
(* Next Obligation. Defined. *)

(* Takes any n-buffer and a yellow (n+1)-buffer, and rearranges elements 
   contained in the two buffers to return a green n-buffer and any (n+1)-buffer. 
   The order of elements is preserved. *)

Equations yellow_prefix_concat {A lvl size1 size2 C}
  (buf1 : buffer A lvl size1 C)
  (buf2 : yellow_buffer A (S lvl) size2) :
  { '(buf1', buf2') : buffer A lvl (2 + size1 mod 2) green * 
                      any_buffer A (S lvl) (size2 - 1 + size1 / 2) |
    buffer_seq buf1 ++ yellow_buffer_seq buf2 =
    buffer_seq buf1' ++ any_buffer_seq buf2' } :=
yellow_prefix_concat buf1 (Yellowish buf2) with prefix_decompose buf1 => {
  | ? Ok buf with buffer_translate buf _, buffer_translate buf2 _ => {
    | ? buf', ? buf2' := ? (buf', Any buf2') };
  | ? Underflow opt with yellow_pop (Yellowish buf2) => {
    | ? (ab, Any buf) with prefix23 opt ab => {
      | ? prefix with buffer_translate prefix _, buffer_translate buf _ => {
        | ? prefix', ? buf' := ? (prefix', Any buf') } } };
  | ? Overflow buf ab with buffer_translate buf _, yellow_push ab (Yellowish buf2) => {
    | ? buf', ? Any suffix with buffer_translate suffix _ => {
      | ? suffix' := ? (buf', Any suffix') } } }.
(* Next Obligation. *)
(* Defined. *)

(* Takes a yellow (n+1)-buffer and any n-buffer, and rearranges elements 
   contained in the two buffers to return any (n+1)-buffer and a green n-buffer. 
   The order of elements is preserved. *)

Equations yellow_suffix_concat {A lvl size1 size2 C}
  (buf1 : yellow_buffer A (S lvl) size1)
  (buf2 : buffer A lvl size2 C) :
  { '(buf1', buf2') : any_buffer A (S lvl) (size1 - 1 + size2 / 2) * 
                      buffer A lvl (2 + size2 mod 2) green |
    yellow_buffer_seq buf1 ++ buffer_seq buf2 =
    any_buffer_seq buf1' ++ buffer_seq buf2' } :=
yellow_suffix_concat (Yellowish buf1) buf2 with suffix_decompose buf2 => {
  | ? Ok buf with buffer_translate buf1 _, buffer_translate buf _ => {
    | ? buf1', ? buf' := ? (Any buf1', buf') };
  | ? Underflow opt with yellow_eject (Yellowish buf1) => {
    | ? (Any buf, ab) with suffix23 ab opt => {
      | ? suffix with buffer_translate buf _, buffer_translate suffix _ => {
        | ? buf', ? suffix' := ? (Any buf', suffix') } } };
  | ? Overflow buf ab with yellow_inject (Yellowish buf1) ab, buffer_translate buf _ => {
    | ? Any prefix, ? buf' with buffer_translate prefix _ => {
      | ? prefix' := ? (Any prefix', buf') } } }.
(* Next Obligation. Defined. *)

(* Creates a green colored deque from three options, two of level n and one of 
   level n+1. *)

Equations cdeque_of_opt3 {A lvl} 
  (o1 : option (prodN A lvl)) 
  (o2 : option (prodN A (S lvl))) 
  (o3 : option (prodN A lvl)) :
  { cd : cdeque A lvl (size_option o1 + size_option o2 + 
                       size_option o2 + size_option o3) green |
    cdeque_seq cd = option_seq o1 ++ option_seq o2 ++ option_seq o3 } :=
cdeque_of_opt3 None None None := ? Small B0;
cdeque_of_opt3 (Some a) None None := ? Small (B1 a);
cdeque_of_opt3 None None (Some a) := ? Small (B1 a);
cdeque_of_opt3 (Some a) None (Some b) := ? Small (B2 a b);
cdeque_of_opt3 None (Some (prodS a b)) None := ? Small (B2 a b);
cdeque_of_opt3 (Some a) (Some (prodS b c)) None := ? Small (B3 a b c);
cdeque_of_opt3 None (Some (prodS a b)) (Some c) := ? Small (B3 a b c);
cdeque_of_opt3 (Some a) (Some (prodS b c)) (Some d) := ? Small (B4 a b c d).

(* When [size1 = size2], translates a colored deque of size1 to a colored 
   deque of size2. *)

Equations cdeque_translate {A lvl size1 size2 C} (cd : cdeque A lvl size1 C) :
    size1 = size2 -> { cd' : cdeque A lvl size2 C | cdeque_seq cd' = cdeque_seq cd } :=
cdeque_translate cd eq_refl := ? cd.

(* A new tactic [destruct_prod] is introduced. It destructs all elements of 
   higher level into elements of lower levels. *)

Local Ltac destruct_prod :=
  repeat 
  match goal with 
  | a : prodN _ 0 |- _ => dependent elimination a
  | ab : prodN _ (S _) |- _ => dependent elimination ab
  | p : _ * _ |- _ => destruct p
  end; cbn in *.

(* A new tactic [to_size] is introduced. It converts an equality on lists to
   an equality on their sizes. *)

Local Ltac to_size H :=
  apply (f_equal (@length _)) in H; 
  repeat rewrite app_length in H;
  repeat rewrite buffer_size in H;
  repeat rewrite prodN_size in H;
  repeat rewrite option_size in H;
  repeat rewrite deque_size in H.

(* Small lemmas needed for the next tactics. *)

Lemma add_r {n m p : nat} : n + p = m + p -> n = m.
Proof. lia. Defined.

Lemma add_r_0 {m p : nat} : p = m + p -> 0 = m.
Proof. lia. Defined.

Lemma add_l_0 {n p : nat} : n + p = p -> n = 0.
Proof. lia. Defined.

(* A new tactic [absurd_power2_eq] is introduced. It aims at showing that an 
   equality of sums of powers of 2 is wrong. *)

Local Ltac absurd_power2_eq := 
  repeat
  match goal with 
  | H : 0 = power2 _ + _ |- _ => 
    exfalso; symmetry in H; 
    apply Nat.eq_add_0 in H as [H1 H2]; apply (power2_neq0 H1)
  | H : _ + power2 _ = 0 |- _ => 
    exfalso; apply Nat.eq_add_0 in H as [H1 H2]; apply (power2_neq0 H2)
  | H : _ + power2 ?n = _ + power2 ?n |- _ => apply add_r in H
  | H : power2 ?n = _ + power2 ?n |- _ => apply add_r_0 in H
  | H : _ + power2 ?n = power2 ?n |- _ => apply add_l_0 in H
  end.

#[local] Hint Rewrite Nat.add_assoc : rnat.
#[local] Hint Rewrite Nat.add_0_r : rnat.

#[local] Obligation Tactic :=
  try first [ done | cbn; destruct_prod; hauto db:rlist ];
  cbn beta iota match; intros.

(* Takes a prefix buffer, a following buffer (when the next level is composed
   of only one buffer), and a suffix buffer. It allows to rearrange all 
   elements contained in those buffers into a green cdeque. *)

Equations make_small {A lvl size1 size2 size3 C1 C2 C3}
  (b1 : buffer A lvl size1 C1)
  (b2 : buffer A (S lvl) size2 C2)
  (b3 : buffer A lvl size3 C3) :
  { cd : cdeque A lvl (size1 + size2 + size2 + size3) green |
    cdeque_seq cd = buffer_seq b1 ++ buffer_seq b2 ++ buffer_seq b3 } :=
make_small prefix1 buf suffix1 
  with prefix_decompose prefix1, suffix_decompose suffix1 => {
  | ? Underflow p1, ? Underflow s1 with buffer_unsandwich buf => {
    | ? Alone opt2 with cdeque_of_opt3 p1 opt2 s1 => { | ? cd := ? cd };
    | ? Sandwich ab rest cd with prefix23 p1 ab, suffix23 cd s1 => {
      | ? prefix, ? suffix :=
      ? Big (Triple prefix Hole suffix PCGreen) (Small rest) eq_refl _ CCGreen } };
  | ? Underflow None, ? Ok s1 with buffer_pop buf => {
    | ? None with cdeque_translate (Small s1) _ => { | ? cd := ? cd };
    | ? Some (prodS c d, Any rest) :=
      ? Big (Triple (B2 c d) Hole s1 PCGreen) (Small rest) eq_refl _ CCGreen };
  | ? Underflow (Some a), ? Ok s1 with buffer_pop buf => {
    | ? None with buffer_push a s1 => {
      | ? cd with cdeque_translate cd _ => { | ? cd' := ? cd' } };
    | ? Some (prodS c d, Any rest) :=
      ? Big (Triple (B3 a c d) Hole s1 PCGreen) (Small rest) eq_refl _ CCGreen };
  | ? Underflow opt, ? Overflow s1 ab with suffix_rot buf ab => {
    | ? (p', rest) with prefix23 opt p' => {
      | ? prefix => 
        ? Big (Triple prefix Hole s1 PCGreen) (Small rest) eq_refl _ CCGreen } };
  | ? Ok p1, ? Underflow None with buffer_eject buf => {
    | ? None with cdeque_translate (Small p1) _ => { | ? cd := ? cd };
    | ? Some (Any rest, prodS c d) :=
        ? Big (Triple p1 Hole (B2 c d) PCGreen) (Small rest) eq_refl _ CCGreen };
  | ? Ok p1, ? Underflow (Some a) with buffer_eject buf => {
  | ? None with buffer_inject p1 a => {
      | ? cd with cdeque_translate cd _ => { | ? cd' := ? cd' } };
  | ? Some (Any rest, prodS c d) :=
      ? Big (Triple p1 Hole (B3 c d a) PCGreen) (Small rest) eq_refl _ CCGreen };
  | ? Ok p1, ? Ok s1 :=
    ? Big (Triple p1 Hole s1 PCGreen) (Small buf) eq_refl _ CCGreen;
  | ? Ok p1, ? Overflow (size := size3') s1 ab with buffer_inject buf ab => {
    | ? cd := ? Big (Triple p1 Hole s1 PCGreen) cd eq_refl _ CCGreen };
  | ? Overflow p1 ab, ? Underflow opt with prefix_rot ab buf => {
    | ? (rest, p') with suffix23 p' opt => {
      | ? suffix => 
        ? Big (Triple p1 Hole suffix PCGreen) (Small rest) eq_refl _ CCGreen } };
  | ? Overflow p1 ab, ? Ok s1 with buffer_push ab buf => {
    | ? cd := ? Big (Triple p1 Hole s1 PCGreen) cd eq_refl _ CCGreen };
  | ? Overflow p1 ab, ? Overflow s1 cd with buffer_halve buf => {
    | ? (x, Any rest) with suffix12 ab x => {
      | ? prefix => ? 
        Big (Triple p1 (Triple prefix Hole (B1 cd) PCYellow) s1 PCGreen) 
            (Small rest) eq_refl _ CCGreen } } }.
Next Obligation.
  to_size e1; destruct_opt_buff; simpl in e1; rewrite Nat.add_0_r in e1;
  absurd_power2_eq.
Defined.
Next Obligation.
  apply empty_buffer_size in e1; subst; reflexivity.
Defined.
Next Obligation.
  to_size e1; destruct_opt_buff; simpl in e1; rewrite Nat.add_0_r in e1;
  absurd_power2_eq.
Defined.
Next Obligation.
  apply empty_buffer_size in e1; subst; reflexivity.
Defined.
Next Obligation.
  simp cdeque_seq packet_front_seq packet_rear_seq;
  destruct_prod; rewrite e1; aac_rewrite <-y; hauto db:rlist.
Defined.
Next Obligation.
  to_size e1; destruct_opt_buff; simpl in e1; absurd_power2_eq.
Defined.
Next Obligation.
  apply empty_buffer_size in e1; subst; lia.
Defined.
Next Obligation.
  to_size e1; destruct_opt_buff; simpl in e1; absurd_power2_eq.
Defined.
Next Obligation.
  apply empty_buffer_size in e1; subst; lia.
Defined.
Next Obligation.
  simp cdeque_seq packet_front_seq packet_rear_seq;
  destruct_prod; rewrite e1; aac_rewrite <-y; hauto db:rlist.
Defined.
Next Obligation.
  to_size y; destruct_opt_buff; simp size_option in y; 
  simpl in y; autorewrite with rnat in y; absurd_power2_eq.
Defined.

(* Takes a red cdeque and returns a green one representing the same set. *)

Equations green_of_red {A lvl size} (cd : cdeque A lvl size red) :
  { cd' : cdeque A lvl size green | cdeque_seq cd' = cdeque_seq cd } :=
green_of_red (Big (Triple p1 Hole s1 PCRed) (Small buf) eq_refl eq_refl CCRed) 
  with make_small p1 buf s1 => {
    | ? cd with cdeque_translate cd _ => { | ? cd' := ? cd' } };
green_of_red 
  (Big (Triple p1 (Triple p2 child s2 PCYellow) s1 PCRed) cd eq_refl eq_refl CCRed)
    with yellow_prefix_concat p1 (Yellowish p2), 
         yellow_suffix_concat (Yellowish s2) s1 => {
      | ? (p1', Any p2'), ? (Any s2', s1') :=
        ? Big (Triple p1' Hole s1' PCGreen) 
              (Big (Triple p2' child s2' PCRed) cd _  eq_refl CCRed) _ _ CCGreen };
green_of_red 
  (Big (Triple p1 Hole s1 PCRed) 
       (Big (Triple p2 child s2 PCGreen) 
            cd eq_refl eq_refl CCGreen) eq_refl eq_refl CCRed)
  with green_prefix_concat p1 p2, green_suffix_concat s2 s1 => {
    | ? (p1', Yellowish p2'), ? (Yellowish s2', s1') :=
    ? Big (Triple p1' (Triple p2' child s2' PCYellow) s1' PCGreen) cd _ _ CCGreen }.
Next Obligation.
  dependent elimination p1; dependent elimination s1;
  (match goal with 
  | b : buffer _ _ psize0 _ |- _ => 
    dependent elimination b end);
  dependent elimination s2; simpl; lia.
Defined.
Next Obligation.
  simp cdeque_seq packet_front_seq packet_rear_seq;
  autorewrite with rlist;
  simp yellow_buffer_seq in y, y0;
  aac_rewrite <-y; aac_normalise; 
  do 5 apply <-app_inv_head_iff;
  symmetry; assumption.
Defined.
Next Obligation. 
  dependent elimination p1; dependent elimination s1;
  (match goal with 
  | b : buffer _ _ psize0 _ |- _ => 
    dependent elimination b end);
  dependent elimination s2; simpl; lia.
Defined.
Next Obligation.
  simp cdeque_seq packet_front_seq packet_rear_seq;
  autorewrite with rlist;
  simp yellow_buffer_seq any_buffer_seq in y, y0;
  aac_rewrite <-y; aac_normalise; 
  do 5 apply <-app_inv_head_iff;
  symmetry; assumption.
Defined.

(* Takes a green or red cdeque, and returns a green one representing
   the same set. *)

Equations ensure_green {A lvl size G R} 
  (cd : cdeque A lvl size (Mix G NoYellow R)) :
  { cd' : cdeque A lvl size green | cdeque_seq cd' = cdeque_seq cd } :=
ensure_green (Small buf) := ? Small buf;
ensure_green (Big x cd eq_refl eq_refl CCGreen) := ? Big x cd _ eq_refl CCGreen;
ensure_green (Big x cd eq_refl eq_refl CCRed) := 
  green_of_red (Big x cd _ eq_refl CCRed).

(* Takes a yellow packet, as a prefix buffer, a child packet and a suffix 
   buffer, and a green or red cdeque. Returns a deque starting with this packet 
   and followed by the green version of the input colored deque. *)

Equations make_yellow {A len size1 pktsize size2 cdsize} {G1 Y1 Y2 G3 Y3 G4 R4}
  (buf1 : buffer A 0 size1 (Mix G1 Y1 NoRed))
  (p : packet A 1 len pktsize (Mix NoGreen Y2 NoRed))
  (buf2 : buffer A 0 size2 (Mix G3 Y3 NoRed))
  (cd : cdeque A (S len + 0) cdsize (Mix G4 NoYellow R4)) :
  { d : deque A (size1 + pktsize + pktsize + size2 + (power2 (S len)) * cdsize) |
    deque_seq d = buffer_seq buf1 ++
                   packet_front_seq p ++
                   cdeque_seq cd ++
                   packet_rear_seq p ++
                   buffer_seq buf2 } :=
make_yellow p1 child s1 cd with ensure_green cd => {
  | ? cd' => ? T (Big (Triple p1 child s1 PCYellow) cd' _ eq_refl CCYellow) }.

(* Takes a red packet, as a prefix buffer, a child packet and a suffix
   buffer, and a green cdeque. Returns the green version of the colored deque 
   made of the red packet followed by the green cdeque. *)

Equations make_red {A len size1 pktsize size2 cdsize} {C1 Y2 C3}
  (buf1 : buffer A 0 size1 C1)
  (p : packet A 1 len pktsize (Mix NoGreen Y2 NoRed))
  (buf2 : buffer A 0 size2 C3)
  (cd : cdeque A (S len + 0) cdsize green) :
  { d : deque A (size1 + pktsize + pktsize + size2 + (power2 (S len)) * cdsize) |
    deque_seq d = buffer_seq buf1 ++
                  packet_front_seq p ++
                  cdeque_seq cd ++
                  packet_rear_seq p ++
                  buffer_seq buf2 } :=
make_red p1 child s1 cd 
  with green_of_red (Big (Triple p1 child s1 PCRed) cd _ eq_refl CCRed) => {
    | ? cd' => ? T cd' }.

(* When [size1 = size2], translates a deque of size1 to a deque of size2. *)

Equations deque_translate {A size1 size2} (d : deque A size1) :
    size1 = size2 -> { d' : deque A size2 | deque_seq d' = deque_seq d } :=
deque_translate d eq_refl := ? d.

#[local] Obligation Tactic :=
  try first [ 
    done | 
    cbn; destruct_prod; hauto db:rlist |
    cbn; intros; destruct_opt_buff; lia ];
  cbn beta iota match; intros.

(* Pushes an element on a deque. *)

Equations push {A size} (x : A) (d : deque A size) :
  { d' : deque A (S size) | deque_seq d' = [x] ++ deque_seq d } :=
push x (T (Small buf)) with buffer_push (prodZ x) buf => {
  | ? buf' => ? T buf' };
push x (T (Big (Triple p1 child s1 PCGreen) dq eq_refl eq_refl CCGreen)) with green_push (prodZ x) p1 => {
  | ? buf' with make_yellow buf' child s1 dq => {
    | ? d' => ? d' } };
push x (T (Big (Triple p1 child s1 PCYellow) dq eq_refl eq_refl CCYellow))
  with yellow_push (prodZ x) (Yellowish p1) => {
  | ? (Any p1') with make_red p1' child s1 dq => {
    | ? d' => ? d' } }.

(* Injects an element on a deque. *)

Equations inject {A size} (d : deque A size) (x : A) :
  { d' : deque A (S size) | deque_seq d' = deque_seq d ++ [x] } :=
inject (T (Small buf)) x with buffer_inject buf (prodZ x) => {
  | ? buf' => ? T buf' };
inject (T (Big (Triple p1 child s1 PCGreen) cd eq_refl eq_refl CCGreen)) x with green_inject s1 (prodZ x) => {
  | ? buf' with make_yellow p1 child buf' cd => {
    | ? d' with deque_translate d' _ => { | ? d'' := ? d'' } } };
inject (T (Big (Triple p1 child s1 PCYellow) cd eq_refl eq_refl CCYellow)) x
  with yellow_inject (Yellowish s1) (prodZ x) => {
  | ? (Any s1') with make_red p1 child s1' cd => {
    | ? d' with deque_translate d' _ => { | ? d'' := ? d'' } } }.

(* Pops an element from a deque. *)

Equations unsafe_pop {A size} (d : deque A size) :
  { o : option (A * deque A (Nat.pred size)) |
    deque_seq d = match o with
               | None => []
               | Some (x, d') => [x] ++ deque_seq d'
               end } :=
unsafe_pop (T (Small buf)) with buffer_pop buf => {
  | ? None := ? None;
  | ? Some (prodZ x, Any buf') := ? Some (x, T (Small buf'))
};
unsafe_pop (T (Big (Triple p1 child s1 PCGreen) cd eq_refl eq_refl CCGreen)) with green_pop p1 => {
  | ? (prodZ x, Yellowish p1') with make_yellow p1' child s1 cd => {
    | ? d' with deque_translate d' _ => { | ? d'' := ? Some (x, d'') } } };
unsafe_pop (T (Big (Triple p1 child s1 PCYellow) cd eq_refl eq_refl CCYellow)) with yellow_pop (Yellowish p1) => {
  | ? (prodZ x, Any p1') with make_red p1' child s1 cd => {
    | ? d' with deque_translate d' _ => { | ? d'' := ? Some (x, d'') } } }.

Equations pop {A size} (d : deque A (S size)) : 
  { '(x, d') : A * deque A size | [x] ++ deque_seq d' = deque_seq d } :=
pop d with unsafe_pop d => { 
  | ? None := _;
  | ? Some (x, d') := ? (x, d') }.
Next Obligation.
  to_size e; apply Nat.neq_succ_0 in e; destruct e.
Defined.

(* Ejects an element from a deque. *)

Equations unsafe_eject {A size} (d : deque A size) :
  { o : option (deque A (Nat.pred size) * A) |
    deque_seq d = match o with
               | None => []
               | Some (d', x) => deque_seq d' ++ [x]
               end } :=
unsafe_eject (T (Small buf)) with buffer_eject buf => {
  | ? None := ? None;
  | ? Some (Any buf', prodZ x) := ? Some (T (Small buf'), x)
};
unsafe_eject (T (Big (Triple p1 child s1 PCGreen) cd eq_refl eq_refl CCGreen)) with green_eject s1 => {
  | ? (Yellowish s1', prodZ x) with make_yellow p1 child s1' cd => {
    | ? d' with deque_translate d' _ => { | ? d'' := ? Some (d'', x) } } };
unsafe_eject (T (Big (Triple p1 child s1 PCYellow) cd eq_refl eq_refl CCYellow)) with yellow_eject (Yellowish s1) => {
  | ? (Any s1', prodZ x) with make_red p1 child s1' cd => {
    | ? d' with deque_translate d' _ => { | ? d'' := ? Some (d'', x) } } }.

Equations eject {A size} (d : deque A (S size)) :
  { '(d', x) : deque A size * A | deque_seq d' ++ [x] = deque_seq d } :=
eject d with unsafe_eject d => {
  | ? None := _;
  | ? Some (d', x) := ? (d', x) }.
Next Obligation.
  to_size e; apply Nat.neq_succ_0 in e; destruct e.
Defined.
