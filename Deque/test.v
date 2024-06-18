From Deque Require Import buffer deque_no_hole.

Definition test3 : deque nat :=
  let d := proj1_sig empty in
  let d := proj1_sig (push 0 d) in
  let d := proj1_sig (push 1 d) in
  let d := proj1_sig (push 2 d) in
  d.

Eval vm_compute in test3.

Definition test6 : deque nat :=
  proj1_sig (concat test3 test3).

Eval vm_compute in test6.

Definition test12 : deque nat :=
  proj1_sig (concat test6 test6).

(* Eval lazy in test12. *)

Goal exists d, test12 = d.
  eexists.
  unfold test12, test6, test3.
  (* Transparent concat. *)
  unfold concat.
  cbn.
  unfold concat_clause_1.
  cbn.
  unfold make_left_clause_2; cbn.
  unfold left_of_only_clause_1; cbn.
  unfold buffer.has5p2_clause_6; cbn.
  unfold buffer.pop5; cbn.
  unfold buffer.pop5_clause_1; cbn.
  unfold buffer.pop2; cbn.
  unfold buffer.pop2_clause_1; cbn.
  unfold buffer.pop_clause_1; cbn.
  unfold ncdeque.pop; cbn.
  unfold ncdeque.pop_clause_1; cbn.
  unfold ncdeque.unsafe_pop_clause_2_clause_1_clause_1; cbn.
  unfold ncdeque.deque_translate; cbn.
  unfold Equality.simplification_heq; cbn.
  unfold Equality.solution_right; cbn.
  unfold pop2_clause_1_clause_1; cbn.
  unfold ncdeque.unsafe_pop_clause_3_clause_1; cbn.
  unfold ncdeque.make_red; cbn.
  unfold ncdeque.make_red_clause_1; cbn.
  unfold ncdeque.green_of_red_clause_1; cbn.
  unfold ncdeque.make_small_clause_1_clause_1_clause_3_clause_1_clause_1; cbn.
  unfold ncdeque.cdeque_translate; cbn.
  unfold ncdeque.make_small_obligations_obligation_6; cbn.
  unfold eq_ind_r; cbn.
  unfold eq_ind; cbn.
  unfold eq_sym; cbn.
  Set Printing Depth 100.
  unfold ncdeque.empty_buffer_size; cbn.
  unfold eq_ind_r; cbn.
  unfold eq_ind; cbn.
  unfold eq_sym; cbn.
