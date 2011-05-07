Add LoadPath "../UnivalentFoundations".

Require Import Homotopy.
Require Import Menagerie.
Require Import Pi0.  (* included for lemmas about hlevels etc. *)


Axiom pi0' : forall (A : Type), Type.

Axiom pi0'_cpnt : forall {A : Type}, A -> pi0' A.

Axiom pi0'_axiomK : forall {A : Type} (x : pi0' A) (l : x ~~> x), l ~~> idpath x.

Axiom pi0'_rect : forall {A : Type} {P : pi0' A -> Type}
 (dcpnt : forall (x : A), P (pi0'_cpnt x))
 (daxiomK : forall (x : pi0' A) (l : x ~~> x) (z : P x) (dl :
transport l z ~~> z),
   dl ~~> map (fun p: x ~~> x => transport p z) (pi0'_axiomK x l)),
 forall (x : pi0' A), P x.

Axiom pi0'_compute_cpnt : forall {A : Type} {P : pi0' A -> Type}
 (dcpnt : forall (x : A), P (pi0'_cpnt x))
 (daxiomK : forall (x : pi0' A) (l : x ~~> x) (z : P x) (dl :
transport l z ~~> z),
   dl ~~> map (fun p: x ~~> x => transport p z) (pi0'_axiomK x l))
 (a : A),
 pi0'_rect dcpnt daxiomK (pi0'_cpnt a) ~~> dcpnt a.

Definition map_dep {A} {P} f {x y} p := @dependent_map_on_paths A P f x y p.

Definition map2_dep {X : Type} {P : X -> Type} {x y : X} {p q : x ~~> y}
 (f : forall x, P x) (s : p ~~> q) :
 map_dep f p ~~> map (fun p : x ~~> y => transport p (f x)) s @ map_dep f q.
Proof.
 path_induction.
Defined.

Definition map2_dep_loop {X : Type} {P : X -> Type} {x : X} {l : x ~~> x}
 (f : forall x, P x) (s : l ~~> idpath x) :
 map_dep f l ~~> map (fun p : x ~~> x => transport p (f x)) s.
Proof.
(* intros X P x l f s. *)
 match goal with |- _ ~~> ?t => path_via (t @ map_dep f (idpath x)) end.
 apply map2_dep.
(* not needed by Mike; different computational behaviour of his map_dep, perhaps? *)
 simpl.  path_tricks.
Defined.

(* In principle the following should be an axiom — but in fact it’s derivable; and by h-level considerations, it’s a proposition (easy to prove this given extensionality); so the axiom is redundant. *)
Lemma pi0'_compute_axiomK : 
  forall {A : Type} {P : pi0' A -> Type}
         (dcpnt : forall (x : A), P (pi0'_cpnt x))
         (daxiomK : forall (x : pi0' A) (l : x ~~> x) (z : P x)
                           (dl : transport l z ~~> z),
                    dl ~~> map (fun p: x ~~> x => transport p z) (pi0'_axiomK x l))
         (x : pi0' A) (l : x ~~> x),
    map2_dep_loop (pi0'_rect dcpnt daxiomK) (pi0'_axiomK x l)
  ~~>
    daxiomK x l (pi0'_rect dcpnt daxiomK x) (map_dep (pi0'_rect dcpnt daxiomK) l).
Proof.
  intros A P dcpnt daxiomk.
  assert (forall (x : pi0' A), isSet (P x)) as fibres_are_sets.
    intros x.
    apply if_loops_contract_then_is_set.
    apply (fibred_K_implies_loops_contract_in_fibres (axiomK := pi0'_axiomK)).
    assumption.
  assert (forall (x : pi0' A) (z z' : P x), isSet (z ~~> z')) as fibres_are_hlevel_3.
    intros x.
    apply set_implies_hlevel_3.
    apply fibres_are_sets.
  intros x l.  apply fibres_are_hlevel_3.
Defined.



(* Deriving my statements of the axioms from Mike’s: *)

Lemma pi0'_contr : forall {X} (l : Circle -> (pi0' X)), (map_on_paths l loop) ~~> (idpath (l base)).
Proof.
  intros X l.  apply pi0'_axiomK.
Defined.

