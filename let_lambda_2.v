Add LoadPath ".". 
Require Import Maps.
Compute examplemap "Church".
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

(* Inductive lt_term : Type:=
   lt_var( x:nat) 
  | lt_abs ( x: nat) (e:lt_term)
  | lt_app (e1 e2 : lt_term)
  | lt_let (x:nat) (e1 e2:lt_term). *)


  (* T - (alpha- type variables) | (i - base types)| (t1->t2 function types)
  type scheme - (t - type) | (forall alpha sigma - quantified types) *)

Inductive expr:Type :=
    (* Const_int:nat -> expr *)
    | lt_var : string -> expr
    | lt_abs: string -> expr -> expr
    (* | Rec: string -> string -> expr -> expr *)
    | lt_app: expr -> expr -> expr
    | lt_letin: string -> expr -> expr -> expr.

Notation "x '-->' y " := (lt_app x y )
    (at level 101, left associativity).

Inductive tau : Type := 
    | i_base : nat -> tau 
    | var_tau : nat -> tau
    | fn_type: tau->tau->tau.


Notation "x '-a>' y " := (fn_type x y )
    (at level 101, left associativity).

Compute (i_base 1) -a> (i_base 1).


(** Type Substitution*)

Fixpoint remove_subsitution (S : list (nat*tau)) n: list (nat*tau) :=
    (** Removes a substitution (n,tau) from a list of substitutions (if it is present in the list)*)
    match S with
    | [] => []
    | h::t => if (fst h) =? n then t else h::(remove_subsitution t n)
        end.

Example S_example := [ (3,(var_tau 1)) ; (4,(var_tau 2))].

Compute (remove_subsitution S_example 2).
Compute (remove_subsitution S_example 3).
Compute (remove_subsitution S_example 4).

Fixpoint get_stubstituted_tau (S : list (nat*tau)) (n:nat) : tau :=
    (** gets that what should be replaced in place of n according to busbtitution list*)
    match S with 
    | [] => var_tau n
    | h::t => if (fst h) =? n then (snd h) else (get_stubstituted_tau t n)
    end.

Fixpoint type_subs (t : tau) (S : list (nat*tau)):tau :=
    (** apply substitutions in S to tye t*)
    match t with 
    | i_base n =>  t 
    | var_tau n => get_stubstituted_tau S n
    | fn_type t1 t2 => fn_type (type_subs t1 S ) (type_subs t2 S )
    end.

(** defining type scheme*)

Inductive type_scheme : Type:=
    | i_ts : nat -> type_scheme 
    | var_ts : nat -> type_scheme
    | gvar_ts : nat -> type_scheme
    | fn_ts: type_scheme->type_scheme->type_scheme.


Notation "x '-w>' y " := (fn_ts x y )
(at level 101, left associativity).

Fixpoint type_sc_to_type (ty : type_scheme) : tau:=
    match ty with 
    | i_ts n => i_base n 
    | var_ts v => var_tau v
    | gvar_ts _ => i_base 5000   (** error gen type cannot be converted to tau*)
    | fn_ts t1 t2 =>  fn_type (type_sc_to_type t1) (type_sc_to_type t2)
    end.

Fixpoint type_to_type_sc (ty : tau) : type_scheme:=
    match ty with 
    | i_base n  => i_ts n 
    | var_tau v =>  var_ts v
    | fn_type t1 t2 =>  fn_ts (type_to_type_sc t1) (type_to_type_sc t2)
    end.

(** type instance*)
Fixpoint type_instance (sig : type_scheme) (S : list (nat*tau)):type_scheme :=
    match sig with
    | i_ts n => sig
    | var_ts v => (type_to_type_sc  (get_stubstituted_tau S  v) )
    | gvar_ts g => sig
    | fn_ts t1 t2 => fn_ts (type_instance t1 S) (type_instance t2 S)
end.    

(** Generic instance*)


Fixpoint get_stubstituted_ts (S : list (nat*type_scheme)) (n:nat) : type_scheme :=
    (** gets that what should be replaced in place of n according to busbtitution list*)
    match S with 
    | [] => var_ts n
    | h::t => if (fst h) =? n then (snd h) else (get_stubstituted_ts t n)
    end.
    
Fixpoint GenericInstance (sig : type_scheme) (S : list (nat*type_scheme)) :type_scheme :=
    (** Here S is mapping generic variable to some type scheme. it is not mapping any variables to tau like in type instance*)
    match sig with
    | i_ts n => sig
    | var_ts v => sig
    | gvar_ts g => get_stubstituted_ts S g
    | fn_ts t1 t2 => fn_ts (GenericInstance t1 S) (GenericInstance t2 S) 
    end.

(* Fixpoint inlist (n:nat) (l: list nat):bool:=
    match l with 
    | [] => false
    | h::t => if h=?n then true else (inlist n t)
    end. *)

Example example_type :=((var_tau 1) -a> ((var_tau 2) -a> (var_tau 3))).
Example S_example2 := [ (1,(var_tau 2)) ; (2,(var_tau 3))].
Example S_example3 := [ (1,(i_base 2)) ; (2,(var_tau 3))].

Compute example_type.
Compute type_subs example_type S_example2.
Compute type_subs example_type S_example3.

(* type_instance (sig : type_scheme) (S : list (nat*tau)):type_scheme  *)

Example example_ts := ((var_ts 1) -w> ((var_ts 2) -w> (var_ts 3))).

Example example2_ts := ((var_ts 1) -w> ((var_ts 2) -w> (gvar_ts 3))).

Compute type_instance ( example_ts) S_example2.
Compute type_instance ( example2_ts) S_example2.

Compute GenericInstance example2_ts ([(3, example2_ts )]).

(**
    Type inference rules
*)

(* 
Inductive one_beta : lc_term -> lc_term -> Prop := 
  | one_beta_red : forall e1 e2 : lc_term , 
        one_beta ((lc_abs e1) --> e2) (substitution_under_lambda e1 e2)
  | op_red : forall e1 e2 e1': lc_term , 
      one_beta e1 e1' -> one_beta (e1 --> e2) (e1' --> e2) 
  | arg_red : forall e1 e2 e2': lc_term , 
      one_beta e2 e2' -> one_beta (e1 --> e2) (e1 --> e2') 
  | abs_red : forall e1 e1': lc_term , 
      one_beta e1 e1' -> one_beta (lc_abs e1) (lc_abs e1'). *)

Fixpoint fetchTypeSchemeString (gamma : (list ( string * type_scheme ))) ( x : string): (option type_scheme) :=
    match gamma with 
    | [] => None
    | h::t => if (string_dec (fst h) x) 
                then Some (snd h)
                else (fetchTypeSchemeString t x)
    end.

Fixpoint eq_type_sc (t1 t2 : type_scheme):bool:= 
    match t1 with
    | var_ts v1 => match t2 with 
        | var_ts v2 => v1 =? v2
        | _ => false
        end
    | i_ts n1 => match t2 with 
        | i_ts n2 => n1 =? n2
        | _ => false
        end
    | gvar_ts g1 => match t2 with 
        | gvar_ts g1=> g1 =? g1
        | _ => false
        end
    | fn_ts t11 t12 => match t2 with 
        | fn_ts t21 t22 => (andb (eq_type_sc t11 t21) (eq_type_sc t12 t22))
        | _ => false
        end
    end.

Compute eq_type_sc (fn_ts (var_ts 1) (var_ts 2)) (fn_ts (var_ts 1) (var_ts 2)).
Compute eq_type_sc (fn_ts (var_ts 1) (gvar_ts 2)) (fn_ts (var_ts 1) (gvar_ts 2)).

Fixpoint ingamma (gamma : (list ( string * type_scheme ))) ( x : string) (sig1 :type_scheme):bool :=
    match (fetchTypeSchemeString gamma x)  with 
    | None => false
    | Some sig => (eq_type_sc sig sig1)
    end.



Fixpoint updateGamma (gamma : (list ( string * type_scheme ))) ( x_ts : string*type_scheme) : (list ( string * type_scheme )) :=
    match gamma with 
    |[] => [x_ts]
    | h::t => if  (string_dec (fst h) (fst x_ts)) 
            then x_ts::t 
            else h::(updateGamma t x_ts)
    end.

Notation "x ** y " := (updateGamma x y )
    (at level 101, left associativity).

(* Fixpoint incr (x:nat):nat:=
    match x with
    | f => f+1
    end.

Compute incr 3. *)

Definition getMaxNat (x1 x2:nat) := if (x1 <? x2) then x2 else x1.


Fixpoint getMaxGenVar (sig:type_scheme) : nat := 
    match sig with
        | i_ts n => 0
        | var_ts v => 0
        | gvar_ts g => g
        | fn_ts t1 t2 => (getMaxNat (getMaxGenVar t1) (getMaxGenVar t2) )
        end.


Fixpoint generalize_var_helper (sig: type_scheme) (x g1:nat) : type_scheme:=
    match sig with
    | i_ts n => sig
    | var_ts v => if v=?x then gvar_ts g1 else sig
    | gvar_ts g => sig
    | fn_ts t1 t2 => (fn_ts (generalize_var_helper t1 x g1) (generalize_var_helper t2 x g1) )
    end.

Fixpoint generalize_var (sig: type_scheme) (x:nat): type_scheme:=
    generalize_var_helper sig x ((getMaxGenVar sig)+1)
    .

Compute example_ts.
Compute (generalize_var (generalize_var example_ts 2) 3).
Compute (generalize_var (generalize_var example_ts 0) 3).

Inductive type_of : (list ( string * type_scheme )) -> expr -> type_scheme -> Prop :=
    | taut_rule : forall (gamma : (list ( string * type_scheme ))) (x:string) (sig: type_scheme) ,
        ( ingamma gamma x sig)=true  ->  (type_of gamma (lt_var x) sig)
    |  app_rule : forall (gamma : (list ( string * type_scheme ))) (e1 e2:expr) (t2 t1:tau),
        (type_of gamma e1 (  type_to_type_sc (t1 -a> t2) )) -> 
        (type_of gamma e2 (type_to_type_sc t1)) -> 
        (type_of gamma (e1 --> e2) (type_to_type_sc t2))
    | abs_rule: forall (gamma : (list ( string * type_scheme ))) (x:string) (e :expr) (t2 t1:tau),
        (type_of ( gamma ** (x,(type_to_type_sc t1))) e (type_to_type_sc t2)) -> 
        type_of gamma (lt_abs x e) (type_to_type_sc (t1 -a> t2) )  
    | let_rule: forall (gamma : (list ( string * type_scheme ))) (x:string) (e1 e2 :expr) (sig :type_scheme) (t:tau),
        (type_of gamma e1 sig) -> (type_of (gamma ** (x,sig)) e2 ( type_to_type_sc t)) -> type_of gamma (lt_letin x e1 e2) (type_to_type_sc t)
    | inst_rule: forall (gamma : (list ( string * type_scheme ))) (sig sig_dash : type_scheme) (S : list (nat*type_scheme)) (e:expr),
        (eq_type_sc (GenericInstance sig S) sig_dash) = true -> (type_of gamma e sig ) -> (type_of gamma e sig_dash)
    | gen_rule:  forall (gamma : (list ( string * type_scheme ))) (sig : type_scheme) (e:expr) (n:nat),
     (type_of gamma e sig) -> (type_of gamma e (generalize_var  sig n) )
    . 
