(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Export notations.
Require Export tac_utils.
Require Export acc_utils.
Require Export list_utils. (* depends on notations + tac_utils *)
Require Export pos.        (* depends on notations + tac_utils + list_utils *)
Require Export nat_utils.  (* depends on notations + tac_utils + list_utils *)
Require Export vec.        (* depends on notations + tac_utils + list_utils + pos + nat_utils *)
Require Export finite.     (* depends on list_utils *)
Require Export tree.       (* depends on notations + acc_utils + list_utils + finite *)