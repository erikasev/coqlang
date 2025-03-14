Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

Open Scope char_scope.
Open Scope char_scope.

Import ListNotations.

Import ListNotations.

Require Import Turing.Util. 
Require Import Turing.Lang.
Require Import List. 


(* Definition of a word and a language *)
Definition word (* String *) := list ascii.
Definition language := word -> Prop.
(* membership *)
Definition In w (L:language) := L w.  
(* word is in language, if you can prove L of w, the word is in the language  *)


(* w is In L => In w L *)

(* Common string operations. *)


(* Length *) (* String which is a list c a r*)
Goal length ["c"; "a"; "r"] = 3.
Proof. reflexivity. Qed. 







(* how do i define a language that only accepts a certain word *)
(* language := word -> Prop *)

(* 1. Define a language L1 that only accepts word ["c"; "a"; "r" ] *)
(* 2. Show that L1 accepts word ' ' *)
(* knowing that the language accepts the word and returns a Prop. (a function) *)
(* Proposition says the word given by input has to be exactly c a r *)

(* 'L1' name, takes an input as an parameter 'w' (word/string) 'w =' has to be exactly  *)
Definition L1 w := w = ["c"; "a"; "r"].
(* Can also write it L1 (w:word) := w = *)

Print L1. (* list ascii -> Prop *)


(* Prove L1 accepts the string *)
Goal 
    In ["c"; "a"; "r"] L1.
Proof. 
    unfold In. 
    reflexivity.
Qed.

(* proof that some other word is not in L1 empty string *)
Goal 
    ~ In [] L1.
Proof. (*Neg proofs always harder, because you have to show for all strings, its not there. *)
    unfold In, L1. (* empty string has to be different than L1. *)
    (* different is not equal, assume that they are the same => contradiction => inversion  *)
    intros N.
    inversion N.
Qed.

(* we know that all strings in that language have to be car  *)
Lemma l1_inv: forall w, (* for any word, if that word is in l1 then that word has to be *)
In w L1 -> 
w = ["c"; "a"; "r"].
Proof. 
    unfold In, L1.
    intros.
    assumption.
Qed.

(* implement, the string, has to be a single vowel. *)
(* Definition L2 w := *)

(* Prove that if a list has non-zero length, then there exits an element in it*)
Definition Char (c:ascii) (w: word) := w = [c].

(* Definition L2 w := w = ["a"] \/ w = ["e"] \/ w = ["i"]. *)

Definition L2 w := Char "a" w
    \/ Char "e" w
    \/ Char "i" w
    \/ Char "o" w
    \/ Char "u" w.

(* show that a  *)
Goal In ["i"] L2.
    Proof.
        unfold In, L2.
        unfold Char.
        right.
        right.
        left.
        reflexivity.
    Qed.
(* pro tip whenever u have a not, then intros N*)

Lemma aa_not_in_vowel: ~ In ["a"; "a"] L2.
    unfold In, L2.
    intros N. (* assume you have it, reach false / proof by contradiction *)
    destruct N.
    -inversion H.
    -destruct H as [N|[N|[N|N]]]; inversion N.
Qed.


(* how would you write Nil language? *)
Print Nil.

(* show that the empty string is in Nil*)
Goal In [] Nil.
Proof. reflexivity. Qed.

(* If a word is accepted by Nil then it must be the empty string *)

(* Print Turing.Lang to see the library *)

(* Union of two languages*)
Print Union.

Import LangNotations.
Infix "U" := Union. 
Goal In ["a"] ("a" U "b").

Goal (* for any word, if the word is in l1 then it has to be in l1 U l2*)
    forall (w:word),
    In w L1 ->
    In w (L1 U L2).
Proof.
    unfold In.
    intros.
    unfold Union.
    left.
    assumption.
Qed.


    
Definition App L1 L2 w := 
    exists w1 w2, 
    In w1 L1 /\
    In w2 L2 /\
    w = w1 ++ w2.



(* l1 >> l2  is concatenation *)
Definition L1' := App(Char "c" )
                    (App (Char"a") 
                            (Char "r")).

Print pow_cons.

Lemma a_in_a:
    Char "a" ["a"].
Proof.
    unfold Char.
    reflexivity.
Qed.

  

(* Power function *)
Goal 
    (* a, a, a, is a to the power of 3 *)
    In ["a"; "a"; "a"] (Pow "a" 3).
Proof. 
    unfold In.
    (* { a } *) (* there is some string in the character a and w2 in Ln*)
    apply pow_cons with (w1 :=["a"]) (w2:=["a"; "a"]). (* now applying this constructor we have to prove 3 things. *)
    
    (* first goal, has a power of 2 prove it 2["a"] ["a"]*)
    -apply pow_cons with (w1:=["a"]) (w2:=["a"]).
        + (* power of one prove l^1 = L * e *) apply pow_cons with (w1:=["a"]) (w2:=[]). 
            * (* Pow "a" 0 [] *) apply pow_nil.
            * (* "a" ["a"]*) apply a_in_a.
            * (* reflexive *) reflexivity.
        + apply a_in_a.
        + reflexivity.
    - apply a_in_a.
    -reflexivity. 
Qed.

(* ^^ why do we have to prove 3 things? 
because pow_cons has 3 conditions 

forall n w1 w2 w3, 

In w2 (Pow L n) -> (1) (goal 1)
In w1 L ->  (2) goal 2
w3 = w1 ++ w2 -> (3) goal 3

Pow L (S n ) w3

*)

Lemma pow_char_in_inv:
    forall c n w,
    In w (Pow(Char c) n) ->
    w = Util.pow1 c n.
Proof.
     unfold In in *. (* * unfolds everywhere *)
    (* in you H you have an inductive prop, 'Pow (char c) n w ' and in the goal you have a function 'w = pow1 c n' *)

    (* pow of 1, prove that the power of char of n is the same as the goal *)
    induction n; intros. {  (* why n ? because its what varies here *)
        (* Pow in goal? simpl *) 
        simpl.
        (* now, an inductive prop in the assumption -> make it smaller *) 
        inversion H; subst; clear H. (*  rewrites all the equations in the assumptions, makes them go away*)
        auto.
    }
    simpl.
    (* simplify an induction prop *)
    inversion H; subst; clear H. 
    (* can i use IHn? *)
    apply IHn in H1.
    rewrite H1 in *.
    subst.
    clear IHn. (* already used *)
    (* now use H2 *)
    unfold Char in *.
    subst.
    reflexivity.

Qed. 

(* important 
(* now, an inductive prop in the assumption -> make it smaller *) 
        inversion H; subst; clear H. (*  rewrites all the equations in the assumptions, makes them go away*)

*)