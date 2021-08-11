Add LoadPath ".". 
Require Import Maps.
Compute examplemap "Church".
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

(* Compute Maps.examplemap "Church".
Compute Maps.examplepmap "Church".

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).


Notation "x '|->' v ';' m" := (Maps.update m x v)
  (at level 100, v at next level, right associativity).

(** We can also hide the last case when it is empty. *)
Notation "x '|->' v" := (Maps.update Maps.empty x v)
  (at level 100). *)

Example Example_SIG := 
 ("0"|->0 ; "1" |-> 0 ; "+" |-> 2 ; "*" |-> 2).

 Check Example_SIG.


(* Example Example_sig_small := ("x" |-> "y" )%string.
 Compute Example_sig_small "x". *)
(* Check list nat 3. *)

Inductive preT : Type:=
| Constant_t (c : string)
| Variable_t (x:string)
| Compound_t (f: string) (l :list preT ) .

Compute Constant_t "1".
Check Compound_t "*" [(Constant_t "0") ; (Constant_t "1")].

Example examplePret_1plus0starX := Compound_t "+" [ 
                                            (Constant_t "1") ; 
                                            ( Compound_t "*" [
                                                    (Constant_t "0") ;
                                                    (Variable_t "x")
                                                ]) 
                                                ].

Example examplePret_1plus0star_invalidterm := Compound_t "+" [ 
                                            (Constant_t "1") ; 
                                            ( Compound_t "*" [
                                                    (Constant_t "0") 
                                                ]) 
                                                ].                                                

Fixpoint flatten_list {A:Type} (l: list (list A) ):list A:=
  match l with 
    | [] => []
    | h::t =>  h ++ (flatten_list t)
  end.

Compute flatten_list [[1] ; [2;3;4] ; [2]; [1]].

Fixpoint getVars (t : preT) : list string:=
  match t with
  | Constant_t c => []
  | Variable_t x => [x]
  | Compound_t f l => flatten_list ( map getVars l ) 
  end.

Compute getVars examplePret_1plus0starX.  
(* if (SIG c) =? Some 1 then true else false *)
(* Fixpoint size (p : lc_term) : nat :=
  match p with
  | lc_var x => 1
  | lc_abs e => 1 + size e
  | lc_app e1 e2 => (size e1) + (size e2)
  end. *)

Check ( "x" !-> true ; _     !-> false ).

Example example_X := ( "x" !-> true ;  "y" !-> true ; _     !-> false ).

Compute (example_X "x").

Compute (example_X "y").

Example example_1_plus := ( "x" !-> true ;  "y" !-> true ; _     !-> false ).

(* Compute (example_X2 "1"). *)

Compute (Example_SIG "1").

(* Definition  remove_some := . *)
Compute [1 ; 2 ; 3].

Compute 1<?3.

(** applies function to list eleents one by one and returns false if result of any computation is false*)
Fixpoint check_all_true {A:Type} (f: A -> bool) (l:list A) : bool := 
    match l with 
    | [ ] => true
    | h::t => if (f h) then (check_all_true f t) else false
    end.

Locate even.
Compute check_all_true Nat.even [ 22 ; 2 ;  4 ; 3].

Compute map Nat.even [1;2;3;4].

(** function to check all elements of list are true*)
Fixpoint and_list (l:list bool): bool :=
    match l with
    | [ ] => true
    | h::t => if h then (and_list t) else false
    end.

Compute and_list [ true ; true; false; true].

Fixpoint isValidTerm (SIG : string->option nat) (X_map: string -> bool) (tm : preT) : bool := 
    match  tm with 
        | Constant_t c => match (SIG c) with 
                            | (Some 0) => true 
                            | _ =>  false
                            end
        | Variable_t x => (X_map x)
        | Compound_t f l => match SIG f with
                            | Some k =>  if (k =? 0) then false
                                else if ((length l)=?k)  
                                    then and_list( map (isValidTerm SIG X_map) l)
                                    else false 
                            | _ => false
                            end
        end.


Compute isValidTerm Example_SIG example_X (Constant_t "1")= true.
Compute isValidTerm Example_SIG example_X (Constant_t "x")= false.
Compute isValidTerm Example_SIG example_X ( Variable_t "x") = true.
Compute isValidTerm Example_SIG example_X ( Variable_t "y") = true.
Compute isValidTerm Example_SIG example_X ( Variable_t "1") = false.

Compute (isValidTerm Example_SIG example_X examplePret_1plus0starX) = true.
Compute (isValidTerm Example_SIG example_X examplePret_1plus0star_invalidterm) = false.



(* Open Scope string_scope. *)
Example Example_sig_small := ( "x" , (Variable_t "y") )%string.
Compute fst Example_sig_small.

Fixpoint subsitute_t (sig_small: string * preT) (tm1:preT) :preT :=
    match tm1 with 
        | Constant_t _ => tm1
        | Variable_t x1 => if (string_dec x1 (fst sig_small)) then (snd sig_small) else tm1 
        | Compound_t f l => Compound_t f (map (subsitute_t sig_small) l)
        end.

Compute subsitute_t  ("x" , (Variable_t "y") )%string examplePret_1plus0starX .
Compute subsitute_t  ("x" , (Constant_t "0") )%string examplePret_1plus0starX.
Compute subsitute_t  ("x" , examplePret_1plus0starX  )%string examplePret_1plus0starX.

Fixpoint subsitute_t_sig_list (sig_small_list: list (string * preT)) (tm1:preT) :preT :=
    match sig_small_list with 
        | [] => tm1
        | h_sig::t_sig_list => subsitute_t_sig_list t_sig_list (subsitute_t h_sig tm1)
    end.

Compute subsitute_t_sig_list  [("x" , (Variable_t "y") )]%string examplePret_1plus0starX .

Example examplePret_1plusYstarX := Compound_t "+" [ 
                                            (Constant_t "1") ; 
                                            ( Compound_t "*" [
                                                    (Variable_t "y") ;
                                                    (Variable_t "x")
                                                ]) 
                                                ].

Compute subsitute_t_sig_list  [("x" , (Variable_t "y") )]%string examplePret_1plusYstarX .

Compute subsitute_t_sig_list  [("x" , (Variable_t "y") ); ("y" , (Constant_t "0") )]%string examplePret_1plusYstarX .


(** Unification *)

(* Inductive kleisli : Type:=
| nil
| kl (kle_tl:kleisli) (sig_new: ). *)

(* We maintain kleisli as a list *)

Compute [1;2;3] ++ [] ++ [1].
Check Example_sig_small.
(* Definition list_append {A:Type} (l:list A) (x:A) : list A :=
  l++[x].
Compute list_append [1;2;3]  1. *)

Fixpoint in_list_string (x:string) (l:list string):bool :=
  match l with 
  | [] => false
  | h::t => if (string_dec h x) then true else (in_list_string x t)  
  end.

  (* Fixpoint in_list_string2 (x:string) (l:list string):bool :=
  match l with 
  | [] => false
  | h::t => match h with
    | x => true
    | _ => false
    end  
  end. *)

Compute in_list_string "x" ["x";"r";"h"] %string.

Compute ("3","1")%string.

(* Inductive Kleisli:Type :=
  | id
  | kl (t Kleisli). *)
  
(*   
(* this argument may not be needed(kl : option list (string*string) ) *)
Fixpoint mgu (t1:preT) (t2: preT) : option (list (string*string)).

(** helper function to apply mgu in 2 lists*)
Fixpoint subst_lists (l1 l2 : preT) : option (list (string*string)) :=
  match l1 with 
    | [] => match l2 with
      | [] => Some []
      | _ => None
    end
    | h1::t1 => match l2 with 
      | [] => None
      | h2::t2 => match (mgu h1 h2) with
        | None => None
        | Some l_subs => Some []
      end
    end
  end. *)


Fixpoint zip_lists {A:Type} (l1 l2: list A){struct l1} : list (A * A) :=
  (** here we are assuming that lists are
   of same length since this function is always called for 
   valid lists*)
  match l1 with 
    | [] => []
    | h1::t1 => match l2 with 
      | [] => [] (** this case will never happen*)
      | h2::t2 => (h1,h2) :: (zip_lists t1 t2)
    end
  end. 

(* Not in use because used let fix in place of this
Fixpoint mgu_list_helper (f_mgu: preT -> preT -> option (list (string*preT)) ) ( sig_list_op : option (list (string*preT))) (zl: list (preT*preT)) {struct zl}: option (list (string*preT)) :=
  match sig_list_op with 
    |None => None
    | Some sig_list => match zl with
      | [] => Some []
      | h::t => match h with
        | (u1, u2) => match (f_mgu u1 u2) with 
          | None => None
          | Some l_subs =>  match (mgu_list_helper f_mgu (Some (sig_list ++ l_subs)) t) with
            | None => None
            | Some l_subs_ret => Some (l_subs ++ l_subs_ret)
          end
        end   
      end
    end
  end. *)

Check string_dec.

Fixpoint max_nat (l:list nat) : (option nat) :=
  match l with 
  | [] => None
  | h::t => match (max_nat t) with
    | None => Some h
    | Some m => if h<?m then Some m else Some h
    end
    end.

Compute max_nat [1;2;0;1].
Fixpoint height_t (t1:preT):nat :=
  match t1 with 
    | Variable_t x1 => 0
    | Constant_t a2 => 0
    | Compound_t f2 l2 => match (max_nat (map height_t l2)) with 
      | None => 1
      | Some m => 1 + m
      end
      end. 

Definition Example_htx := (Compound_t "*" [(Constant_t "1") ; (Variable_t "x")]).
Definition Example_htx2 := (Compound_t "*" [Example_htx ;(Constant_t "1") ]).
Definition Example_htx3 := (Compound_t "*" [Example_htx2 ;(Constant_t "1") ]).
Definition Example_htx4 := (Compound_t "*" [Example_htx2 ;Example_htx2 ]).
Compute height_t Example_htx.
Compute height_t Example_htx2.
Compute height_t Example_htx3.
Compute height_t Example_htx4.
Require Import Coq.Program.Wf. 
Program Fixpoint mgu (t1:preT) (t2: preT) {measure (height_t t1)}: option (list (string*preT)) :=
  match t1 with 
    | Variable_t x1 => match t2 with 
      | Variable_t x2 => if (string_dec x2 x1) then (Some []) else (Some [ (x1 , t2) ])
      | Constant_t a2 => Some [ (x1 , t2) ]
      | Compound_t f2 l2 => if (in_list_string x1 (getVars t2)) then None else Some [ ( x1 , t2 ) ]
    end
    | Constant_t a1 => match t2 with
      | Constant_t a2 => if (string_dec a1 a2) then Some [] else None 
      | Variable_t x2 => Some ([ (x2 , t1) ])
      | Compound_t _ _=> None
    end
    | Compound_t f1 l1 => match t2 with
      | Constant_t _ => None
      | Variable_t x2 => if (in_list_string x2 (getVars t1)) then None else Some [ ( x2 , t1 ) ]
      | Compound_t f2 l2 => if (string_dec f1 f2) 
        then 
        let fix mgu_list_helper ( sig_list_op : option (list (string*preT))) (l1 l2: list (preT)) : option (list (string*preT)) :=
              match sig_list_op with 
                |None => None
                | Some sig_list => match l1 with
                  | [] => Some []
                  | h1::t1 => match l2 with
                    | [] => None
                    | h2::t2 => match (mgu (subsitute_t_sig_list sig_list h1) (subsitute_t_sig_list sig_list h2)) with 
                      | None => None
                      | Some l_subs =>  match (mgu_list_helper (Some (sig_list ++ l_subs)) t1 t2) with
                        | None => None
                        | Some l_subs_ret => Some (l_subs ++ l_subs_ret)
                      end
                    end   
                  end
                end
              end 
              in mgu_list_helper  (Some []) l1 l2  
        (* then Some [] *)
        else None 
        
    end
  end.

(* Next Obligation.
Proof. 
  destruct (subsitute_t_sig_list sig_list h1).
  - simpl. destruct ( max_nat (map height_t l3)).
  destruct (zerop (S n)); try discriminate; try trivial. 
  destruct (zerop(1)) ;try discriminate; try trivial.
  - simpl. destruct ( max_nat (map height_t l3)). 
  --  destruct (zerop (S n)); try discriminate; try trivial.
  --  destruct (zerop(1)) ;try discriminate; try trivial.
  - f_equal. simpl.
  --  unfold lt. reflexivity.
  -- unfold lt.       
  unfold subsitute_t_sig_list. 
Qed. 

(* Check mgu. *)

Compute mgu (Variable_t "x") (Variable_t "x"). (** id *)
Compute mgu (Variable_t "x") (Variable_t "y"). (** id *)
Compute mgu (Variable_t "x") (Constant_t "0"). (** x-> ta*)
Compute mgu (Variable_t "x") (Compound_t "+" [(Constant_t "1") ; (Variable_t "y")] ). (** x -> t2*)
Compute mgu (Variable_t "x") (Compound_t "+" [(Constant_t "1") ; (Variable_t "x")] ). (** FAIL*)


Compute mgu (Constant_t "0") (Constant_t "0"). (** id*)
Compute mgu (Constant_t "0") (Variable_t "x"). (** x-> a*)
Compute mgu (Constant_t "0") (Constant_t "1"). (** FAIL *)

Compute mgu (Compound_t "*" [(Constant_t "1") ; (Variable_t "x")] ) (Constant_t "1") . (** FAIL*)
Compute mgu (Compound_t "*" [(Constant_t "1") ; (Variable_t "x")] ) (Compound_t "+" [(Constant_t "1") ; (Variable_t "x")] ). (** FAIL f1 != f2*)
Compute mgu (Compound_t "+" [(Constant_t "1") ; (Variable_t "x")] ) (Compound_t "+" [(Variable_t "y") ; (Constant_t "2")] ). (** y-> 1 x->2 *)

Example test_1 := Compound_t "*" [(Constant_t "1") ; (Variable_t "x")].
Example test_2 := Compound_t "+" [(Variable_t "y") ; (Constant_t "2")].
Compute mgu test_2 test_1 . (** fail *)

Example test_3 := Compound_t "*" [(Variable_t "y") ; (Constant_t "2")].
Compute mgu test_3 test_1 . (** y-> 1 x->2 *)

Example test_4 := Compound_t "*" [
    Compound_t "+" [(Variable_t "x");(Variable_t "y")] ; 
    Compound_t "+" [
        (Constant_t "4");
        (Compound_t "*" [
            (Compound_t "+" [(Constant_t "1"); (Variable_t "y")]);
            (Constant_t "4")
            ] ) 
        ] 
    ].

Example test_5 := Compound_t "*" [
        Compound_t "+" [(Variable_t "x");(Variable_t "y")] ; 
        Compound_t "+" [
            (Variable_t "x");
            (Compound_t "*" [
                (Compound_t "+" [ (Variable_t "y"); (Constant_t "1")]);
                (Variable_t "y")
                ] ) 
            ] 
        ].

Compute mgu test_4 test_5  . * y-> 1 x->2 *)
