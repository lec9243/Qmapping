Require Import QWIRE.Prelim.

Definition is_one_step_graph n1 n2 := length (get_path n1 n2) =? 2
Definition is_two_step_graph n1 n2 := length (get_path n1 n2) =? 3

Definition is_in_hp_graph x1 x2 y1 y2 u := (* two nodes: (x1, x2) (y1, y2) *)
 (is_one_step_path x1 y1) \/
 ((is_two_step_path x2 y2) /\ (is_elem x2 u))


 Definition get_path_hp x1 x2 y1 y2 u := (* two nodes: (x1, x2) (y1, y2) *)
 if is_in_hp_graph x1 x2 y1 y2 u then [(x1,x2), (y1,y2)]
 else if x1 < y1 then move_right_hp x1 x2 y1 y2 u 
      else move_left_hp x1 x2 y1 y2 u



(* Inductive Vi_hp_g : list nat -> list nat
                             -> (nat -> nat -> bool)
                             -> (nat -> nat -> bool)
                             -> Prop := *)

Fixpoint intersect_v (l1 : list nat) pi : (list nat) :=
match l1 with
| [] => []
| (h :: t) => if (dom_pi h pi) && (not (pi_vi h pi))
              then (h:(intersect_v t pi))
              else (intersect_v t pi)

(** dom_pi h pi == v in dom(pi) **)
pi_vi h pi :=


Definition deg_pi pi :=
