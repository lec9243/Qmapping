Require Export ConnectivityGraph.
Require Export Layouts.
Require Export MappingConstraints.
Require Import StandardGateSet.
Import StdList.

(* Alogrithm 3.1 *)

Fixpoint hierarchical_product_permuter_part1 pi permuter_g1g2 (deg_ham : nat) :=  (* line 2 *)
  match deg_ham with
  | 0 => pi
  | n =>
      let r = partial_permutation permuter_g1g2  (* line 1*)
          g' = route_v_to_k r permuter_g1g2  (* line 3,4 *)
          new_g = route_communicator_v_g1 g'  (* line 5,6 *)
      in
      hierarchical_product_permuter_part1 pi new_g (n-1)
  end.


Fixpoint hierarchical_product_permuter_part2 v1 pi permuter_g1g2 :=  (* line 7 *)
  match v1 with
  | [] => pi
  | (h :: t) =>
      let
        new_pi = route_v_Vi_to_pi h pi permuter_g1g2  (*line 8 *)
      in
      hierarchical_product_permuter_part2 t new_pi permuter_g1g2
  end,


Definition hierarchical_product_permuter pi permuter_g1g2 deg_ham := (* Algorithm 3.1 *)
let
  new_pi = hierarchical_product_permuter_part1 pi permuter_g1g2 deg_ham
  v1 = V(new_pi,1)
in
hierarchical_product_permuter_part2 v1 new_pi permuter_g1g2

(* Algorithm 3.2 *)

Fixpoint choose_distinct_sets pi sigma r rowi_V2 :=
match rowi_V2 with
| [] => sigma
| i :: tail => let v = (dom pi) - (dom sigma)
                   E = (head v, pi_v (v,1), current_v (v, i)) (* line 4 *)
                   U, V = list_n (num_of (V1 pi)) (* ni = |Vi| *) (* line 6 *)
                   G = (U, V, E) (* line 6 *)
                   V_match = v_set (find_minimum_weight G (add_u_v_e G r)) (* line 7~11 *)
                   new_sigma =  app sigma (v_list V_match) (* line 12 *)
               in
                   choose_distinct_sets pi new_sigma (r-1) t


(* Algorithm 3.3 *)

Fixpoint routing_tokens_to_destination pi :=
if (pi == id_dom pi)
then (*return seq of transpositions *)
else
  if exists_happy_swap
  then routing_tokens_to_destination (do_transposition pi)
  else
    if (exists_v (dom pi)) and (exists_u (Nu_dom_pi v))
    then routing_tokens_to_destination (no_token_swap v u)
    else routing_tokens_to_destination (unhappy_swap)
