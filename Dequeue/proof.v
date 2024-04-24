From Coq Require Import ssreflect.
From Coq Require Import Program List ZArith Lia.
Import ListNotations.
From Equations Require Import Equations.
Open Scope Z_scope.
From Hammer Require Import Tactics.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

(* Transforms a list of pairs into a list, preserving the order. *)

Fixpoint flattenp {A} (l: list (A * A)): list A :=
  match l with
  | [] => []
  | cons (x, y) l' => [x] ++ [y] ++ flattenp l'
  end.

(* The lemma [app_cons_one] is trivial but it is mandatory as ++ is later made
   opaque. *)

Lemma app_cons_one [A : Type] (a : A) (l : list A) : a :: l = [a] ++ l.
Proof.
  reflexivity.
Qed.

Opaque app.
Definition singleton {A : Type} (x : A) : list A := [x].
Opaque singleton.

(* A simple lemma to prove the distributivity of flattenp over concatenation 
   of lists. *)

Lemma flattenp_app A (l1: list (A * A)) l2 : flattenp (l1 ++ l2) = flattenp l1 ++ flattenp l2.
Proof. 
  induction l1 as [ | (a, b) l].
  - eauto.
  - rewrite <- app_comm_cons.
    simpl.
    rewrite IHl.
    aac_reflexivity.
Qed.

(* A list of tactics to be used when trying to resolve obligations generated by
   Equations. *)

#[export] Hint Rewrite <-app_assoc : rlist.
#[export] Hint Rewrite <-app_comm_cons : rlist.
#[export] Hint Rewrite flattenp_app : rlist.
#[export] Hint Rewrite app_nil_r : rlist.
#[export] Hint Rewrite compose_id_right : rlist.

#[local] Obligation Tactic :=
  try first [ done | hauto db:rlist ].

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

(* A type for buffers. *)

Inductive buffer : Type -> color -> Type :=
| B0 : forall {a : Type}, buffer a red
| B1 : forall {a : Type}, a -> buffer a yellow
| B2 : forall {a: Type} {G Y},
  a -> a -> buffer a (Mix G Y NoRed)
| B3 : forall {a : Type} {G Y},
  a -> a -> a -> buffer a (Mix G Y NoRed)
| B4 : forall {a : Type},
  a -> a -> a -> a -> buffer a yellow
| B5 : forall {a : Type},
  a -> a -> a -> a -> a -> buffer a red.

(* A type for yellow buffers. *)

Inductive yellow_buffer (A: Type) : Type :=
| Yellowish : forall {G Y},
  buffer A (Mix G Y NoRed) ->
  yellow_buffer A.
Arguments Yellowish {A G Y}.

(* A type for any buffers. *)

Inductive any_buffer (A: Type) : Type :=
| Any : forall {C}, buffer A C -> any_buffer A.
Arguments Any {A C}.

(* A type for packet. *)

Inductive packet : Type -> Type -> color -> Type :=
| HOLE : forall {a : Type},
  packet a a uncolored
| Yellow : forall {a b : Type} {G1 Y1 Y2 G3 Y3},
  buffer a (Mix G1 Y1 NoRed) ->
  packet (a * a) b (Mix NoGreen Y2 NoRed) ->
  buffer a (Mix G3 Y3 NoRed) ->
  packet a b yellow
| Green : forall {a b : Type} {Y},
  buffer a green ->
  packet (a * a) b (Mix NoGreen Y NoRed) ->
  buffer a green ->
  packet a b green
| Red : forall {a b : Type} {C1 Y C2},
  buffer a C1 ->
  packet (a * a) b (Mix NoGreen Y NoRed) ->
  buffer a C2 ->
  packet a b red.

(* A type for colored deque. *)

Inductive cdeque : Type -> color -> Type :=
| Small : forall {a C},
  buffer a C -> cdeque a green
| G : forall {a b G R},
  packet a b green ->
  cdeque b (Mix G NoYellow R) ->
  cdeque a green
| Y : forall {a b : Type},
  packet a b yellow ->
  cdeque b green ->
  cdeque a yellow
| R : forall {a b : Type},
  packet a b red ->
  cdeque b green ->
  cdeque a red.

(* The decompose type. *)

Inductive decompose (A : Type) : Type :=
| Underflow : option A -> decompose A
| Ok : buffer A green -> decompose A
| Overflow : buffer A green -> A * A -> decompose A.

Arguments Underflow {_}.
Arguments Ok {_}.
Arguments Overflow {_}.

(* The sandwich type. *)

Inductive sandwich (A : Type) : Type :=
| Alone : option A -> sandwich A
| Sandwich {C} : A -> buffer A C -> A -> sandwich A.
Arguments Alone {A}.
Arguments Sandwich {A C}.

(* The not_yellow trait for colors. *)

Inductive not_yellow : color -> Type :=
| Not_yellow {G R} : not_yellow (Mix G NoYellow R).

(* A type for deque. *)

Inductive deque : Type -> Type :=
| T : forall {a G Y},
  cdeque a (Mix G Y NoRed) ->
  deque a.

(* Models *)

Set Equations Transparent.

(* Get a list from a pair. *)

Equations pair_seq {A} : A * A -> list A := 
pair_seq (a, b) := [a] ++ [b].

(* Get a list from an option. *)

Equations option_seq {A} : option A -> list A :=
option_seq None := [];
option_seq (Some x) := [x].

(* Get a list from a buffer. *)

Equations buffer_seq {A C} : buffer A C -> list A :=
buffer_seq B0 := [];
buffer_seq (B1 a) := [a];
buffer_seq (B2 a b) := [a] ++ [b];
buffer_seq (B3 a b c) := [a] ++ [b] ++ [c];
buffer_seq (B4 a b c d) := [a] ++ [b] ++ [c] ++ [d];
buffer_seq (B5 a b c d e) := [a] ++ [b] ++ [c] ++ [d] ++ [e].

(* Get a list from a yellow buffer. *)

Equations yellow_buffer_seq {A} : yellow_buffer A -> list A :=
yellow_buffer_seq (Yellowish buf) := buffer_seq buf.

(* Get a list from any buffer. *)

Equations any_buffer_seq {A} : any_buffer A -> list A :=
any_buffer_seq (Any buf) := buffer_seq buf.

(* Get the list corresponding to elements stored in prefix buffers along a 
   packet. *)

Equations packet_front_seq {A B C} : packet A B C -> list A :=
packet_front_seq HOLE := [];
packet_front_seq (Yellow buf1 p _) :=
  buffer_seq buf1 ++ flattenp (packet_front_seq p);
packet_front_seq (Green buf1 p _) :=
  buffer_seq buf1 ++ flattenp (packet_front_seq p);
packet_front_seq (Red buf1 p _) :=
  buffer_seq buf1 ++ flattenp (packet_front_seq p).

(* Get the list corresponding to elements stored in suffix buffers along a 
   packet. *)

Equations packet_rear_seq {A B C} : packet A B C -> list A :=
packet_rear_seq HOLE := [];
packet_rear_seq (Yellow _ p buf2) :=
  flattenp (packet_rear_seq p) ++ buffer_seq buf2;
packet_rear_seq (Green _ p buf2) :=
  flattenp (packet_rear_seq p) ++ buffer_seq buf2;
packet_rear_seq (Red _ p buf2) :=
  flattenp (packet_rear_seq p) ++ buffer_seq buf2.

(* Constructs the function transforming a list B into a list A, given a packet
   A B _ _. It uses the induction relation of packets' Constructors to deduct 
   the right relation between A and B. *)

Equations packet_hole_flatten {A B C} : packet A B C -> list B -> list A :=
packet_hole_flatten HOLE := id;
packet_hole_flatten (Yellow _ p _) :=
  flattenp ∘ packet_hole_flatten p;
packet_hole_flatten (Green _ p _) :=
  flattenp ∘ packet_hole_flatten p;
packet_hole_flatten (Red _ p _) :=
  flattenp ∘ packet_hole_flatten p.

(* Get the list represented by a colored deque. *)

Equations cdeque_seq {A C} : cdeque A C -> list A :=
cdeque_seq (Small buf) := buffer_seq buf;
cdeque_seq (G p dq) :=
  packet_front_seq p ++
  packet_hole_flatten p (cdeque_seq dq) ++
  packet_rear_seq p;
cdeque_seq (Y p dq) :=
  packet_front_seq p ++
  packet_hole_flatten p (cdeque_seq dq) ++
  packet_rear_seq p;
cdeque_seq (R p dq) :=
  packet_front_seq p ++
  packet_hole_flatten p (cdeque_seq dq) ++
  packet_rear_seq p.

(* Get the list of non-excess elements of an object of type decompose. *)

Equations decompose_main_seq {A : Type} (dec : decompose A) : list A :=
decompose_main_seq (Underflow None) := [];
decompose_main_seq (Underflow (Some x)) := [x];
decompose_main_seq (Ok b) := buffer_seq b;
decompose_main_seq (Overflow b _) := buffer_seq b.

(* Get the list of excess elements of an object of type decompose. *)

Equations decompose_rest_seq {A : Type} (dec : decompose A) : list A :=
decompose_rest_seq (Underflow _) := [];
decompose_rest_seq (Ok _) := [];
decompose_rest_seq (Overflow b (x, y)) := [x] ++ [y].

(* Get the list of elements of an object of type sandwich. *)

Equations sandwich_seq {A : Type} (sw : sandwich A) : list A :=
sandwich_seq (Alone None) := [];
sandwich_seq (Alone (Some x)) := [x];
sandwich_seq (Sandwich x b y) := [x] ++ buffer_seq b ++ [y].

(* Get the list represented by a deque. *)

Equations deque_seq {A} : deque A -> list A :=
deque_seq (T dq) := cdeque_seq dq.

Unset Equations Transparent.

(* Functions *)

Notation "? x" := (@exist _ _ x _) (at level 100).

(* Pushing on a green buffer. *)

Equations green_push {A : Type} (x : A) (b : buffer A green) :
  { b' : buffer A yellow | buffer_seq b' = [x] ++ buffer_seq b } :=
green_push x (B2 a b) := ? B3 x a b;
green_push x (B3 a b c) := ? B4 x a b c.

(* Injecting on a green buffer. *)

Equations green_inject {A : Type} (b : buffer A green) (x : A) :
  { b' : buffer A yellow | buffer_seq b' = buffer_seq b ++ [x] } :=
green_inject (B2 a b) x := ? B3 a b x;
green_inject (B3 a b c) x := ? B4 a b c x.

(* Poping from a green buffer. *)

Equations green_pop {A : Type} (b : buffer A green) :
  { '(x, b') : A * yellow_buffer A | buffer_seq b = [x] ++ yellow_buffer_seq b' } :=
green_pop (B2 a b) => ? (a, (Yellowish (B1 b)));
green_pop (B3 a b c) => ? (a, (Yellowish (B2 b c))).

(* Ejecting from a green buffer. *)

Equations green_eject {A : Type} (b : buffer A green) :
  { '(b', x) : yellow_buffer A * A | buffer_seq b = yellow_buffer_seq b' ++ [x] } :=
green_eject (B2 a b) => ? ((Yellowish (B1 a)), b);
green_eject (B3 a b c) => ? ((Yellowish (B2 a b)), c).

(* Pushing on a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_push {A : Type} (x : A) (b : yellow_buffer A) :
  { b' : any_buffer A | any_buffer_seq b' = [x] ++ yellow_buffer_seq b } :=
yellow_push x (Yellowish buf) with buf => {
  | B1 a => ? Any (B2 x a);
  | B2 a b => ? Any (B3 x a b);
  | B3 a b c => ? Any (B4 x a b c);
  | B4 a b c d => ? Any (B5 x a b c d)
}.

(* Injecting on a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_inject {A : Type} (b : yellow_buffer A) (x : A) :
  { b' : any_buffer A | any_buffer_seq b' = yellow_buffer_seq b ++ [x] } :=
yellow_inject (Yellowish buf) x with buf := {
  | B1 a => ? Any (B2 a x);
  | B2 a b => ? Any (B3 a b x);
  | B3 a b c => ? Any (B4 a b c x);
  | B4 a b c d => ? Any (B5 a b c d x)
}.

(* Poping from a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_pop {A : Type} (b : yellow_buffer A) :
  { '(x, b') : A * any_buffer A | yellow_buffer_seq b = [x] ++ any_buffer_seq b' } :=
yellow_pop (Yellowish buf) with buf => {
  | B1 a => ? (a, Any B0);
  | B2 a b => ? (a, Any (B1 b));
  | B3 a b c => ? (a, Any (B2 b c));
  | B4 a b c d => ? (a, Any (B3 b c d))
}.

(* Ejecting from a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_eject {A : Type} (b : yellow_buffer A) :
  { '(b', x) : any_buffer A * A | yellow_buffer_seq b = any_buffer_seq b' ++ [x] } :=
yellow_eject (Yellowish buf) with buf => {
  | B1 a => ? (Any B0, a);
  | B2 a b => ? (Any (B1 a), b);
  | B3 a b c => ? (Any (B2 a b), c);
  | B4 a b c d => ? (Any (B3 a b c), d)
}.

(* Pushing on a buffer. *)

Equations buffer_push {A : Type} {C : color} (x : A) (b : buffer A C) :
  { cd : cdeque A green | cdeque_seq cd = [x] ++ buffer_seq b } :=
buffer_push x B0 := ? Small (B1 x);
buffer_push x (B1 a) := ? Small (B2 x a);
buffer_push x (B2 a b) := ? Small (B3 x a b);
buffer_push x (B3 a b c) := ? Small (B4 x a b c);
buffer_push x (B4 a b c d) := ? Small (B5 x a b c d);
buffer_push x (B5 a b c d e) := ? G (Green (B3 x a b) HOLE (B3 c d e)) (Small B0).

(* Injecting on a buffer. *)

Equations buffer_inject {A : Type} {C : color} (b : buffer A C) (x : A) :
  { cd : cdeque A green | cdeque_seq cd = buffer_seq b ++ [x] } :=
buffer_inject B0 x := ? Small (B1 x);
buffer_inject (B1 a) x := ? Small (B2 a x);
buffer_inject (B2 a b) x := ? Small (B3 a b x);
buffer_inject (B3 a b c) x := ? Small (B4 a b c x);
buffer_inject (B4 a b c d) x := ? Small (B5 a b c d x);
buffer_inject (B5 a b c d e) x := ? G (Green (B3 a b c) HOLE (B3 d e x)) (Small B0).

(* Poping from a buffer. *)
  
Equations buffer_pop {A C} (b : buffer A C) :
  { o : option (A * any_buffer A) |
    buffer_seq b =
    match o with
    | None => []
    | Some (x, b') => [x] ++ any_buffer_seq b'
    end } :=
buffer_pop B0 := ? None;
buffer_pop (B5 a b c d e) := ? Some (a, Any (B4 b c d e));
buffer_pop buf with yellow_pop (Yellowish buf) => { | ? o := ? Some o }.

(* Ejecting from a buffer. *)

Equations buffer_eject {A C} (b : buffer A C) :
  { o : option (any_buffer A * A) |
    buffer_seq b =
    match o with
    | None => []
    | Some (b', x) => any_buffer_seq b' ++ [x]
    end } :=
buffer_eject (B5 a b c d e) := ? Some (Any (B4 a b c d), e);
buffer_eject B0 := ? None;
buffer_eject buf with yellow_eject (Yellowish buf) => { | ? o := ? Some o }.

(* Pushes then ejects. *)

Equations prefix_rot {A C} (x : A) (b : buffer A C) :
  { '(b', y) : buffer A C * A | [x] ++ buffer_seq b = buffer_seq b' ++ [y] } :=
prefix_rot x B0 := ? (B0, x);
prefix_rot x (B1 a) := ? (B1 x, a);
prefix_rot x (B2 a b) := ? (B2 x a, b);
prefix_rot x (B3 a b c) := ? (B3 x a b, c);
prefix_rot x (B4 a b c d) := ? (B4 x a b c, d);
prefix_rot x (B5 a b c d e) := ? (B5 x a b c d, e).

(* Injects then pops. *)

Equations suffix_rot {A C} (b : buffer A C) (y : A) :
  { '(x, b') : A * buffer A C | buffer_seq b ++ [y] = [x] ++ buffer_seq b' } :=
suffix_rot B0 x := ? (x, B0);
suffix_rot (B1 a) x := ? (a, B1 x);
suffix_rot (B2 a b) x := ? (a, B2 b x);
suffix_rot (B3 a b c) x := ? (a, B3 b c x);
suffix_rot (B4 a b c d) x := ? (a, B4 b c d x);
suffix_rot (B5 a b c d e) x := ? (a, B5 b c d e x).

(* Create a green buffer by injecting a pair onto an option. *)

Equations prefix23 {A G Y} (o : option A) (p: A * A) :
  { b : buffer A (Mix G Y NoRed) |
    buffer_seq b = option_seq o ++ pair_seq p } :=
prefix23 None (b, c) := ? B2 b c;
prefix23 (Some a) (b, c) := ? B3 a b c.

(* Create a green buffer by poping a pair onto an option. *)

Equations suffix23 {A G Y} (p : A * A) (o : option A) :
  { b : buffer A (Mix G Y NoRed) |
    buffer_seq b = pair_seq p ++ option_seq o } :=
suffix23 (a, b) None := ? B2 a b;
suffix23 (a, b) (Some c) := ? B3 a b c.

(* Create a yellow (or green) buffer by pushing an element onto an option. *)

Equations suffix12 {A} (x : A) (o : option A) :
  { b : buffer A yellow | buffer_seq b = [x] ++ option_seq o } :=
suffix12 x None := ? B1 x;
suffix12 x (Some y) := ? B2 x y.

(* Returns the decomposed version of a buffer. Here, it is a prefix 
   decomposition: when the buffer is overflowed, elements at the end are 
   removed. *)

Equations prefix_decompose {A C} (b : buffer A C) :
  { dec : decompose A | buffer_seq b = decompose_main_seq dec ++ decompose_rest_seq dec } :=
prefix_decompose B0 := ? Underflow None;
prefix_decompose (B1 x) := ? Underflow (Some x);
prefix_decompose (B2 a b) := ? Ok (B2 a b);
prefix_decompose (B3 a b c) := ? Ok (B3 a b c);
prefix_decompose (B4 a b c d) := ? Overflow (B2 a b) (c, d);
prefix_decompose (B5 a b c d e) := ? Overflow (B3 a b c) (d, e).

(* Returns the decomposed version of a buffer. Here, it is a suffix
   decomposition: when the buffer is overflowed, elements at the beginning are
   removed. *)

Equations suffix_decompose {A C} (b : buffer A C) :
  { dec : decompose A | buffer_seq b = decompose_rest_seq dec ++ decompose_main_seq dec } :=
suffix_decompose B0 := ? Underflow None;
suffix_decompose (B1 x) := ? Underflow (Some x);
suffix_decompose (B2 a b) := ? Ok (B2 a b);
suffix_decompose (B3 a b c) := ? Ok (B3 a b c);
suffix_decompose (B4 a b c d) := ? Overflow (B2 c d) (a, b);
suffix_decompose (B5 a b c d e) := ? Overflow (B3 c d e) (a, b).

(* Returns the sandwich representation of a buffer. *)

Equations buffer_unsandwich {A C} (b : buffer A C) :
  { sw : sandwich A | buffer_seq b = sandwich_seq sw } :=
buffer_unsandwich B0 := ? Alone None;
buffer_unsandwich (B1 a) := ? Alone (Some a);
buffer_unsandwich (B2 a b) := ? Sandwich a B0 b;
buffer_unsandwich (B3 a b c) := ? Sandwich a (B1 b) c;
buffer_unsandwich (B4 a b c d) := ? Sandwich a (B2 b c) d;
buffer_unsandwich (B5 a b c d e) := ? Sandwich a (B3 b c d) e.

(* Translates a buffer to a pairs buffer. A additional option type is returned 
   to handle cases where the buffer contains an odd number of elements. *)

Equations buffer_halve {A C} (b : buffer A C) :
  { '(o, b') : option A * any_buffer (A * A) |
    buffer_seq b = option_seq o ++ flattenp (any_buffer_seq b') } :=
buffer_halve B0 := ? (None, Any B0);
buffer_halve (B1 a) := ? (Some a, Any B0);
buffer_halve (B2 a b) := ? (None, Any (B1 (a, b)));
buffer_halve (B3 a b c) := ? (Some a, Any (B1 (b, c)));
buffer_halve (B4 a b c d) := ? (None, Any (B2 (a, b) (c, d)));
buffer_halve (B5 a b c d e) := ? (Some a, Any (B2 (b, c) (d, e))).

(* Takes any buffer and a pairs green one, and rearranges elements contained in 
   the two buffers to return one green buffer and a pairs yellow buffer. The 
   order of elements is preserved. *)

Equations green_prefix_concat {A C}
  (buf1 : buffer A C)
  (buf2 : buffer (A * A) green) :
  { '(buf1', buf2') : buffer A green * yellow_buffer (A * A) |
    buffer_seq buf1 ++ flattenp (buffer_seq buf2) =
    buffer_seq buf1' ++ flattenp (yellow_buffer_seq buf2') } :=
green_prefix_concat buf1 buf2 with prefix_decompose buf1 => {
  | (? Ok buf) => ? (buf, Yellowish buf2);
  | (? Underflow opt) with green_pop buf2 => {
    | (? (ab, buf)) =>
        let '(? prefix) := prefix23 opt ab in
        ? (prefix, buf) };
  | (? Overflow buf ab) =>
    let '(? suffix) := green_push ab buf2 in
    ? (buf, Yellowish suffix)
}.

(* Takes a pairs green buffer and any one, and rearranges elements contained in 
   the two buffers to return one pairs yellow buffer and one green buffer. The 
   order of elements is preserved. *)

Equations green_suffix_concat {A C}
  (buf1 : buffer (A * A) green)
  (buf2 : buffer A C) :
  { '(buf1', buf2') : yellow_buffer (A * A) * buffer A green |
    flattenp (buffer_seq buf1) ++ buffer_seq buf2 =
    flattenp (yellow_buffer_seq buf1') ++ buffer_seq buf2' } :=
green_suffix_concat buf1 buf2 with suffix_decompose buf2 => {
  | ? Ok buf => ? (Yellowish buf1, buf);
  | ? Underflow opt with green_eject buf1 => {
    | ? (buf, ab) =>
        let '(? suffix) := suffix23 ab opt in
        ? (buf, suffix) };
  | ? Overflow buf ab =>
    let '(? prefix) := green_inject buf1 ab in
    ? (Yellowish prefix, buf)
}.

(* Takes any buffer and a pairs yellow one, and rearranges elements contained 
   in the two buffers to return one green buffer and any pairs buffer. The 
   order of elements is preserved. *)

Equations yellow_prefix_concat {A B}
  (buf1 : buffer A B)
  (buf2 : yellow_buffer (A * A)) :
  { '(buf1', buf2') : buffer A green * any_buffer (A * A) |
    buffer_seq buf1 ++ flattenp (yellow_buffer_seq buf2) =
    buffer_seq buf1' ++ flattenp (any_buffer_seq buf2') } :=
yellow_prefix_concat buf1 buf2 with prefix_decompose buf1 => {
  | ? (Ok buf) =>
    let '(Yellowish buf2) := buf2 in
    ? (buf, Any buf2);
  | ? (Underflow opt) with yellow_pop buf2 => {
    | ? (ab, buf) =>
      let '(? prefix) := prefix23 opt ab in
      ? (prefix, buf) };
  | ? (Overflow buf ab) =>
    let '(? suffix) := yellow_push ab buf2 in
    ? (buf, suffix)
}.

(* Takes a pairs yellow buffer and any one, and rearranges elements contained 
   in the two buffers to return any pairs buffer and one green buffer. The 
   order of elements is preserved. *)

Equations yellow_suffix_concat {A B}
  (buf1 : yellow_buffer (A * A))
  (buf2 : buffer A B) :
  { '(buf1', buf2') : any_buffer (A * A) * buffer A green |
    flattenp (yellow_buffer_seq buf1) ++ buffer_seq buf2 =
    flattenp (any_buffer_seq buf1') ++ buffer_seq buf2' } :=
yellow_suffix_concat buf1 buf2 with suffix_decompose buf2 => {
  | ? (Ok buf) =>
    let '(Yellowish buf1) := buf1 in
    ? (Any buf1, buf);
  | ? (Underflow opt) with yellow_eject buf1 => {
    | ? (buf, ab) =>
      let '(? suffix) := suffix23 ab opt in
      ? (buf, suffix) };
  | ? (Overflow buf ab) =>
    let '(? prefix) := yellow_inject buf1 ab in
    ? (prefix, buf)
}.

(* Creates a green colored deque from three options, one being on a pair. *)

Equations cdeque_of_opt3 {A} (o1 : option A) (o2 : option (A * A)) (o3 : option A) :
  { cd : cdeque A green |
    cdeque_seq cd = option_seq o1 ++ flattenp (option_seq o2) ++ option_seq o3 } :=
cdeque_of_opt3 None None None := ? Small B0;
cdeque_of_opt3 (Some a) None None := ? Small (B1 a);
cdeque_of_opt3 None None (Some a) := ? Small (B1 a);
cdeque_of_opt3 (Some a) None (Some b) := ? Small (B2 a b);
cdeque_of_opt3 None (Some (a, b)) None := ? Small (B2 a b);
cdeque_of_opt3 (Some a) (Some (b, c)) None := ? Small (B3 a b c);
cdeque_of_opt3 None (Some (a, b)) (Some c) := ? Small (B3 a b c);
cdeque_of_opt3 (Some a) (Some (b, c)) (Some d) := ? Small (B4 a b c d).

(* A new tactics, flattenp_lists is introduced. It is used when the context contains 
   an equality over lists of pairs. The tactic will destruct all the pairs, find 
   the hypothesis containing the equality, apply flattenp on it, simplify, and try
   to rewrite it in the goal. *)

Local Ltac flattenp_lists :=
  repeat
  match goal with 
  | ab : ?A * ?A |- _ => destruct ab; cbn in *
  end;
  match goal with 
  | H : _ ++ [(_, _)] = _ |- _ =>
    apply (f_equal flattenp) in H;
    rewrite !flattenp_app in H;
    cbn in H;
    try aac_rewrite H;
    try aac_rewrite <- H
  | H : [(_, _)] ++ _ = _ |- _ =>
    apply (f_equal flattenp) in H;
    rewrite !flattenp_app in H;
    cbn in H;
    try aac_rewrite H;
    try aac_rewrite <- H
  end.

(* Takes a prefix buffer, a following buffer (when the next level is composed
   of only one buffer), and a suffix buffer. It allows to rearrange all 
   elements contained in those buffers into a green cdeque. *)

Equations make_small {A C1 C2 C3}
  (b1 : buffer A C1)
  (b2 : buffer (A * A) C2)
  (b3 : buffer A C3) :
  { cd : cdeque A green |
    cdeque_seq cd = buffer_seq b1 ++ flattenp (buffer_seq b2) ++ buffer_seq b3 } :=
make_small prefix1 buf suffix1 with (prefix_decompose prefix1), (suffix_decompose suffix1) => {
  | (? Ok p1), (? Ok s1) :=
    ? G (Green p1 HOLE s1) (Small buf);
  | (? Ok p1), (? Underflow opt) with buffer_eject buf => {
    | ? None with opt => {
      | None := ? Small p1;
      | Some x with buffer_inject p1 x => { | ? cd := ? cd } };
    | ? Some (Any rest, cd) with suffix23 cd opt => {
      | ? suffix := ? G (Green p1 HOLE suffix) (Small rest) }
  };
  | (? Underflow opt), (? Ok s1) with buffer_pop buf => {
    | ? None with opt => {
      | None := ? Small s1;
      | Some x with buffer_push x s1 => { | ? cd := ? cd } };
    | ? Some (cd, Any rest) with prefix23 opt cd => {
      | ? prefix := ? G (Green prefix HOLE s1) (Small rest) }
  };
  | (? Underflow p1), (? Underflow s1) with buffer_unsandwich buf => {
    | ? Sandwich ab rest cd with prefix23 p1 ab, suffix23 cd s1 => {
      | ? prefix, ? suffix := ? G (Green prefix HOLE suffix) (Small rest) };
    | ? Alone opt with cdeque_of_opt3 p1 opt s1 => { | ? cd := ? cd } }
  | (? Overflow p1 ab), (? Ok s1) with buffer_push ab buf => {
    | ? rest => ? G (Green p1 HOLE s1) rest };
  | (? Ok p1), (? Overflow s1 ab) with buffer_inject buf ab => {
    | ? rest => ? G (Green p1 HOLE s1) rest };
  | (? Underflow opt), (? Overflow s1 ab) with suffix_rot buf ab => {
    | ? (cd, center) with prefix23 opt cd => {
      | ? prefix => ? G (Green prefix HOLE s1) (Small center) } };
  | (? Overflow p1 ab), (? Underflow opt) with prefix_rot ab buf => {
    | ? (center, cd) with suffix23 cd opt => {
      | ? suffix => ? G (Green p1 HOLE suffix) (Small center) } };
  | (? Overflow p1 ab), (? Overflow s1 cd) with buffer_halve buf => {
    | ? (x, Any rest) with suffix12 ab x => {
      | ? prefix => ? G (Green p1 (Yellow prefix HOLE (B1 cd)) s1) (Small rest) } }
}.
Next Obligation.
  cbn. intros * Hpref1 * Hcenter Hsuff * Hpref.
  rewrite Hpref.
  flattenp_lists.
  hauto db:rlist.
Qed.
Next Obligation.
  cbn. intros * Hpref * Hcenter * Hsuff1 * Hsuff.
  rewrite Hsuff.
  flattenp_lists.
  hauto db:rlist.
Qed.

(* Takes a red cdeque and returns a green one representing the same set. *)

Equations green_of_red {A : Type} (cd : cdeque A red) :
  { cd' : cdeque A green | cdeque_seq cd' = cdeque_seq cd } :=
green_of_red (R (Red p1 HOLE s1) (Small buf)) with make_small p1 buf s1 => {
  | ? cd' := ? cd' };
green_of_red (R (Red p1 (Yellow p2 child s2) s1) cd)
  with yellow_prefix_concat p1 (Yellowish p2), yellow_suffix_concat (Yellowish s2) s1 => {
  | ? (p1', Any p2'), ? (Any s2', s1') :=
    ? G (Green p1' HOLE s1') (R (Red p2' child s2') cd) };
green_of_red (R (Red p1 HOLE s1) (G (Green p2 child s2) cd))
  with green_prefix_concat p1 p2, green_suffix_concat s2 s1 => {
  | ? (p1', Yellowish p2'), ? (Yellowish s2', s1') :=
    ? G (Green p1' (Yellow p2' child s2') s1') cd }.
Next Obligation.
  cbn. intros * H1 * H2 *. autorewrite with rlist.
  rewrite !app_assoc H1. hauto db:rlist.
Qed.
Next Obligation.
  cbn. intros * H1 * H2 *. autorewrite with rlist.
  rewrite !app_assoc H1. hauto db:rlist.
Qed.

(* Takes a green or red cdeque, and returns a green one representing
   the same set. *)

Equations ensure_green {A C} (ny: not_yellow C) (cd : cdeque A C) :
  { cd' : cdeque A green | cdeque_seq cd' = cdeque_seq cd } :=
ensure_green Not_yellow (Small buf) := ? Small buf;
ensure_green Not_yellow (G x cd) := ? G x cd;
ensure_green Not_yellow (R x cd) := green_of_red (R x cd).

(* Takes a yellow packet, as a prefix buffer, a child packet and a suffix 
   buffer, and a green or red cdeque. Returns a deque starting with this packet 
   and followed by the green version of the input colored deque. *)

Equations make_yellow {A B: Type} {G1 Y1 Y2 G3 Y3 G4 R4}
  (buf1 : buffer A (Mix G1 Y1 NoRed))
  (p : packet (A * A) B (Mix NoGreen Y2 NoRed))
  (buf2 : buffer A (Mix G3 Y3 NoRed))
  (cd : cdeque B (Mix G4 NoYellow R4)) :
  { sq : deque A |
    deque_seq sq = buffer_seq buf1 ++
               flattenp (packet_front_seq p) ++
               flattenp (packet_hole_flatten p (cdeque_seq cd)) ++
               flattenp (packet_rear_seq p) ++
               buffer_seq buf2 }
:=
make_yellow p1 child s1 cd with ensure_green Not_yellow cd => {
  | ? cd' => ? T (Y (Yellow p1 child s1) cd') }.

(* Takes a red packet, as a prefix buffer, a child packet and a suffix
   buffer, and a green cdeque. Returns the green version of the colored deque 
   made of the red packet followed by the green cdeque. *)

Equations make_red {A B: Type} {C1 Y2 C3}
  (buf1 : buffer A C1)
  (p : packet (A * A) B (Mix NoGreen Y2 NoRed))
  (buf2 : buffer A C3)
  (cd : cdeque B green) :
  { sq : deque A |
    deque_seq sq = buffer_seq buf1 ++
               flattenp (packet_front_seq p) ++
               flattenp (packet_hole_flatten p (cdeque_seq cd)) ++
               flattenp (packet_rear_seq p) ++
               buffer_seq buf2 }
:=
make_red p1 child s1 cd with green_of_red (R (Red p1 child s1) cd) => {
  | ? cd' => ? T cd' }.

Module S.

(* Pushes an element on a deque. *)

Equations push {A: Type} (x : A) (sq : deque A) :
  { sq' : deque A | deque_seq sq' = [x] ++ deque_seq sq }
:=
push x (T (Small buf)) with buffer_push x buf => {
  | ? buf' => ? T buf' };
push x (T (G (Green p1 child s1) dq)) with green_push x p1 => {
  | ? buf' with make_yellow buf' child s1 dq => {
    | ? sq' => ? sq' } };
push x (T (Y (Yellow p1 child s1) dq))
  with yellow_push x (Yellowish p1) => {
  | ? (Any p1') with make_red p1' child s1 dq => {
    | ? sq' => ? sq' } }.

(* Injects an element on a deque. *)

Equations inject {A: Type} (sq : deque A) (x : A) :
  { sq' : deque A | deque_seq sq' = deque_seq sq ++ [x] }
:=
inject (T (Small buf)) x with buffer_inject buf x => {
  | ? buf' => ? T buf' };
inject (T (G (Green p1 child s1) cd)) x with green_inject s1 x => {
  | ? buf' with make_yellow p1 child buf' cd => {
    | ? sq' => ? sq' } };
inject (T (Y (Yellow p1 child s1) cd)) x
  with yellow_inject (Yellowish s1) x => {
  | ? (Any s1') with make_red p1 child s1' cd => {
    | ? sq' => ? sq' } }.

(* Pops an element from a deque. *)

Equations pop {A: Type} (sq : deque A) :
  { o : option (A * deque A) |
    deque_seq sq = match o with
               | None => []
               | Some (x, sq') => [x] ++ deque_seq sq'
               end } :=
pop (T (Small buf)) with buffer_pop buf => {
  pop _ (? None) := ? None;
  pop _ (? Some (x, Any buf')) := ? Some (x, T (Small buf'))
};
pop (T (G (Green p1 child s1) cd)) with green_pop p1 => {
  | ? (x, Yellowish p1') with make_yellow p1' child s1 cd => {
    | ? sq' => ? Some (x, sq') } };
pop (T (Y (Yellow p1 child s1) cd)) with yellow_pop (Yellowish p1) => {
  | ? (x, Any p1') with make_red p1' child s1 cd => {
    | ? sq' => ? Some (x, sq') } }.

(* Ejects an element from a deque. *)

Equations eject {A : Type} (sq : deque A) :
  { o : option (deque A * A) |
    deque_seq sq = match o with
               | None => []
               | Some (sq', x) => deque_seq sq' ++ [x]
               end } :=
eject (T (Small buf)) with buffer_eject buf => {
  eject _ (? None) := ? None;
  eject _ (? Some (Any buf', x)) := ? Some (T (Small buf'), x)
};
eject (T (G (Green p1 child s1) cd)) with green_eject s1 => {
  | ? (Yellowish s1', x) with make_yellow p1 child s1' cd => {
    | ? sq' => ? Some (sq', x) } };
eject (T (Y (Yellow p1 child s1) cd)) with yellow_eject (Yellowish s1) => {
  | ? (Any s1', x) with make_red p1 child s1' cd => {
    | ? sq' => ? Some (sq', x) } }.

End S.

(* Final structure wrapping everything *)

(* There might be a better setup for the definitions; currently the proofs are
   fairly tedious... *)

(* A type for this new structure that is called t. *)

Record t (A: Type) : Type := {
  seq_length : Z;
  seq : deque A;
  length_inv : Z.abs_nat seq_length = length (deque_seq seq);
}.
Arguments seq_length {A}.
Arguments seq {A}.

(* Get the list represented by a t. *)

Set Equations Transparent.
Equations t_seq {A} : t A -> list A :=
t_seq {| seq_length := len; seq := sq |} with Z_lt_le_dec len 0 => {
  | left _ => rev (deque_seq sq)
  | right _ => deque_seq sq
}.
Unset Equations Transparent.

(* Designing of a custom tactics to directly destruct a Z_lt_le_dec. *)

Local Ltac case_lt :=
  match goal with |- context [ Z_lt_le_dec ?x ?y ] =>
    destruct (Z_lt_le_dec x y); cbn
  end.

(* A simple lemma on lists. *)

Lemma rev_eq_nil A (l : list A) :
  rev l = [] -> l = [].
Proof.
  intros H%(f_equal (@length _)). cbn in H.
  rewrite rev_length in H. by apply length_zero_iff_nil.
Qed.

(* Designing of a custom tactics to directly assume a list is empty if its 
   length is null, or its reverse is the empty list. *)

Local Ltac simplist :=
  cbn in *;
  repeat match goal with
  | H : 0%nat = length ?l |- _ =>
    symmetry in H; apply length_zero_iff_nil in H; subst
  | H : rev ?l = [] |- _ =>
    apply rev_eq_nil in H; subst
  end.

(* The empty t. *)

Equations empty {A} : { sq : t A | t_seq sq = [] } :=
empty := ? {| seq_length := 0; seq := T (Small B0) |}.

(* Emptyness test for t. *)

Equations is_empty {A} (sq : t A) :
  { b : bool | b = true <-> t_seq sq = [] } :=
is_empty sq := ? (seq_length sq =? 0).
Next Obligation.
  cbn. intros *. 
  destruct sq as [x deque Hlen]. cbn. rewrite Z.eqb_eq. case_lt.
  all: split; [intros -> | intros HH]; simplist; try hauto.
  all: rewrite HH /= in Hlen; hauto.
Qed.

(* Returns the length of a t. *)

Equations length {A} (sq : t A) :
  { n : Z | n = Z.of_nat (List.length (t_seq sq)) } :=
length sq := ? Z.abs (seq_length sq).
Next Obligation.
  intros. destruct sq as [x deque Hlen]. cbn.
  case_lt; rewrite ?rev_length; lia.
Qed.

(* Reverses a t. *)

Equations rev {A} (sq : t A) : { sq' : t A | t_seq sq' = rev (t_seq sq) } :=
rev {| seq_length := n; seq := deque |} :=
  ? {| seq_length := - n; seq := deque |}.
Next Obligation.
  cbn. intros ? n deque Hlen.
  case_lt; case_lt; auto; try lia.
  1: by rewrite rev_involutive //.
  assert (n = 0) by lia; subst. simplist; hauto.
Qed.

(* Pushes an element on a t. *)

Equations push {A} (x : A) (sq : t A) :
  { sq' : t A | t_seq sq' = [x] ++ t_seq sq } :=
push x {| seq_length := n; seq := deque |} with Z_lt_le_dec n 0 => {
  | right _ with S.push x deque => {
    | ? deque' => ? {| seq_length := n + 1; seq := deque' |} };
  | left _ with S.inject deque x => {
    | ? deque' => ? {| seq_length := n - 1; seq := deque' |} }
}.
Next Obligation.
  cbn. intros * ? * -> **. rewrite app_length /=. lia.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? ? ? Hseq Hlen *. case_lt.
  { rewrite Hseq rev_unit //. }
  { assert (n = 0) by lia; subst; simplist; hauto. }
Qed.
Next Obligation.
  cbn. intros * ? * Hseq Hlen. rewrite Hseq //=. rewrite app_length /=. lia.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? ? ? Hseq Hlen *. case_lt; last hauto.
  { assert (n = 0) by lia; subst; simplist; hauto. }
Qed.

(* Injects an element on a t. *)

Equations inject {A} (sq : t A) (x : A) :
  { sq' : t A | t_seq sq' = t_seq sq ++ [x] } :=
inject {| seq_length := n; seq := deque |} x with Z_lt_le_dec n 0 => {
  | right _ with S.inject deque x => {
    | ? deque' => ? {| seq_length := n + 1; seq := deque' |} };
  | left _ with S.push x deque => {
    | ? deque' => ? {| seq_length := n - 1; seq := deque' |} }
}.
Next Obligation. cbn. intros * ? * Hlen * ->. cbn. rewrite app_length /=. lia. Qed.
Next Obligation.
  cbn. intros ? ? ? ? Hlen ? ? Hseq. case_lt; first hauto.
  assert (n = 0) by lia; subst; simplist; hauto.
Qed.
Next Obligation.
  cbn. intros * ? * Hlen * ->. rewrite app_length /=. lia.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? Hlen ? ? Hseq. case_lt; last hauto.
  assert (n = 0) by lia; subst; simplist; hauto.
Qed.

(* Pops an element from a t. *)

Equations pop {A} (sq : t A) :
  { o : option (A * t A) |
    t_seq sq = match o with
               | None => []
               | Some (x, sq') => [x] ++ t_seq sq'
               end } :=
pop {| seq_length := n; seq := deque |} with Z_lt_le_dec n 0 => {
  | right _ with S.pop deque => {
    | ? None => ? None;
    | ? Some (x, deque') => ? Some (x, {| seq_length := n-1; seq := deque' |})
  };
  | left _ with S.eject deque => {
    | ? None => ? None;
    | ? Some (deque', x) => ? Some (x, {| seq_length := n+1; seq := deque' |})
  }
}.
Next Obligation.
  cbn. intros * ? * Hseq%(f_equal (@List.length _)) Hlen.
  rewrite app_length /= in Hseq. lia.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? ? ? Hseq Hlen. case_lt.
  { rewrite Hseq rev_unit //. }
  { assert (n = -1) by lia; subst; simplist.
    rewrite Hseq rev_unit. rewrite Hseq app_length /= in Hlen.
    assert (0%nat = List.length (deque_seq deque')) by lia; simplist. hauto. }
Qed.
Next Obligation.
  cbn. intros * ? * Hseq%(f_equal (@List.length _)) Hlen.
  cbn in *. rewrite app_length /= in Hseq. lia.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? ? ? Hseq Hlen. case_lt; last hauto.
  assert (n = 0) by lia; subst; simplist. rewrite <- app_cons_one in Hseq. hauto.
Qed.

(* Ejects an element from a t. *)

Equations eject {A} (sq : t A) :
  { o : option (t A * A) |
    t_seq sq = match o with
               | None => []
               | Some (sq', x) => t_seq sq' ++ [x]
               end } :=
eject {| seq_length := n; seq := deque |} with Z_lt_le_dec n 0 => {
  | right _ with S.eject deque => {
    | ? None => ? None;
    | ? Some (deque', x) => ? Some ({| seq_length := n-1; seq := deque' |}, x)
  };
  | left _ with S.pop deque => {
    | ? None => ? None;
    | ? Some (x, deque') => ? Some ({| seq_length := n+1; seq := deque' |}, x)
  }
}.
Next Obligation.
  cbn. intros * ? * Hseq%(f_equal (@List.length _)) Hlen. rewrite app_length /= in Hseq. hauto.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? ? ? Hseq Hlen. case_lt; first hauto.
  assert (n = -1) by lia; subst; simplist.
  rewrite Hseq /=. rewrite Hseq /= in Hlen.
  rewrite app_length /= in Hlen.
  assert (0%nat = List.length (deque_seq deque')) by lia; simplist; hauto.
Qed.
Next Obligation.
  cbn. intros * ? * Hseq%(f_equal (@List.length _)) Hlen.
  rewrite app_length /= in Hseq. lia.
Qed.
Next Obligation.
  cbn. intros ? ? ? ? ? ? Hseq Hlen. case_lt; last hauto.
  assert (n = 0) by lia; subst; simplist. rewrite Hlen in Hseq |-*.
  destruct (deque_seq deque'). exact Hseq. 
  apply (f_equal (@List.length _)) in Hseq; rewrite <- app_comm_cons in Hseq; simpl in Hseq.
  apply O_S in Hseq. destruct Hseq.
Qed.

(* Tests if a t is to be read backward or not. *)

Definition is_rev {A} (sq : t A) : bool :=
  seq_length sq <? 0.