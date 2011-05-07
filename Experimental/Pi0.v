Add LoadPath "../UnivalentFoundations".

Require Import Homotopy.
Require Import Menagerie.


(* First some definitions/lemmas which should really be moved to other files *)

Definition isProp (X:Type) := forall {x y : X}, x ~~> y.
Definition isSet (X:Type) := forall {x y : X}, isProp (x ~~> y). 

Lemma prop_implies_set : forall {X:Type}, isProp X -> isSet X.
Admitted.

Lemma set_implies_hlevel_3 : forall {X:Type}, isSet X -> forall {x y : X}, isSet (x ~~> y).
Proof.
  intros X XisSet x y.  apply prop_implies_set.  apply XisSet.
Defined.

Lemma transp_along_map_on_paths : forall {Y X : Type} {P : X -> Type}
                                         {f : Y -> X}
                                         {y y':Y} {u:y~~>y'}
                                         {z : P (f y)},
                                    (transport (P := (fun y => P (f y))) u z)
                                  ~~>
                                    (transport (map_on_paths f u) z).
Proof.
  intros.  induction u.  simpl.  exact (idpath z).
Qed.


Definition Circle_nondep_rect {X} {x:X} (p : x ~~> x) : Circle -> X.
  exact (@Circle_rect (fun _ => X) x ((transport_in_trivial_fibration loop x) @ p)).
Defined.

Definition Circle_nondep_comp_base {X} {x:X} (p : x ~~> x) :
                                   (Circle_nondep_rect p base ~~> x).
  unfold Circle_nondep_rect.  apply (Circle_comp_base (P := fun _ => X)).
Defined.

Definition Circle_nondep_comp_loop {X} {x:X} (p : x ~~> x) :
                     ! (Circle_nondep_comp_base p)
                     @ (map_on_paths (Circle_nondep_rect p) loop)
                     @ (Circle_nondep_comp_base p)
                   ~~> p.
Proof.
  (* a bunch of messing around with naturality and transport_in_trivial_fibration *)
Admitted.




(*
Inductive pi0 (X:Type) : Type :=
    | pi0_cmpt : X -> pi0 X
    | pi0_contr : forall (l : Circle -> pi0 X), paths (idpath (l base)) (cong l loop)
*)

Axiom pi0 : Type -> Type.

Axiom pi0_cmpt : forall {X} (x:X), (pi0 X).

Axiom pi0_contr : forall {X} (l : Circle -> (pi0 X)), (map_on_paths l loop) ~~> (idpath (l base)).



Axiom pi0_rect : forall {X} {P : (pi0 X -> Type)}
                    (d_cmpt : forall x:X, P (pi0_cmpt x))
                    (d_contr : forall (l : Circle -> (pi0 X))  (k : forall a:Circle, P (l a)),
                      let id_coerced_along_contr :=
                         ( transp_along_map_on_paths
                         @ (map_on_paths (fun u : l base ~~> l base => transport u (k base)) (pi0_contr l)) )
                      in
                         (id_coerced_along_contr) ~~> (dependent_map_on_paths k loop)),
                 forall (z : pi0 X), P z.

Axiom pi0_comp_cmpt : forall {X} {P} {d_cmpt} {d_contr} (x:X),
                             (@pi0_rect X P d_cmpt d_contr (pi0_cmpt x)) ~~> (d_cmpt x). 

(* Axiom pi0_comp_contr *)
(* Horrible to type… but actually should be redundant for homotopical reasons anyway, I think, so hopefully leaving it out will not hurt us. *)

Lemma pi0_nondep_rect {X} {Y} (s : isSet Y) (f : X -> Y)
                      : pi0 X -> Y.
Proof.
  apply (@pi0_rect X (fun _ => Y) f); intros.  apply s.
Defined.

Lemma pi0_nondep_comp_base : forall {X} {Y} {s} {f} (x:X), (@pi0_nondep_rect X Y s f (pi0_cmpt x) ~~> (f x)).
Proof.
  intros; unfold pi0_nondep_rect.  exact (pi0_comp_cmpt (P := fun _ => Y) x).
Defined.  (* maybe could/should leave opaque, since is a path in a set? *)

(* Again, pi0_nondep_comp_loop is unnecessary, since we can get its result equivalently and more directly from the fact that Y is a set. *)

Lemma if_circles_contract_then_loops_contract {X : Type} :
        (forall (l : Circle -> X), (map_on_paths l loop) ~~> (idpath (l base)))
        -> forall (x:X) (p : x ~~> x), (p ~~> idpath x).
Proof.
  intros contr x p.
  set (p_as_circle := Circle_nondep_rect p). 
  set (almost_goal := contr p_as_circle).
(* plan:
    p
 ~~>    [by ! Circle_nondep_comp_loop]
    (! Circle_nondep_comp_base p) @ (map_on_paths p_as_circle loop) @ (Circle_nondep_comp_base p)
 ~~>    [by almost_goal]
    (! Circle_nondep_comp_base p) @ (idpath (p_as_circle base)) @ (Circle_nondep_comp_base p)
 ~~>    [by unitarity of composition]]
    (! Circle_nondep_comp_base p) @ (Circle_nondep_comp_base p)
 ~~>    [by inverseness of !]
    idpath x
*)
  path_via ((! Circle_nondep_comp_base p) @ (map_on_paths p_as_circle loop) @ (Circle_nondep_comp_base p)).
    exact (! Circle_nondep_comp_loop p). 
  path_via ((! Circle_nondep_comp_base p) @ (idpath (p_as_circle base)) @ (Circle_nondep_comp_base p)).
    (* almost_goal gets used automagically for first subgoal *)
  path_via ( (! Circle_nondep_comp_base p) @ (Circle_nondep_comp_base p)).
    (* units/inverses dealt with automagically in both subgoals *)
Defined.

Lemma if_loops_contract_then_is_set {X : Type} :
        (forall (x:X) (p : x ~~> x), (p ~~> idpath x)) 
        -> isSet X.
Proof.
  intros contr x y u v.
  path_via (u @ !v @ v).  path_via (u @ (!v @ v)).
(* now have 3 subgoals: 
  u ~~> u @ (!v @ v)
        u @ (!v @ v) ~~> (u @ !v) @ v
                         (u @ !v) @ v ~~> v
solved in the following 3 lines respectively: *)
  path_via (u @ idpath _).  (* both subgoals auto (by: unitarity ; inverse)  *)
  apply opposite; apply concat_associativity.
  path_via (idpath _ @ v).  (* both subgoals auto (by: contr ; unitarity) *)
Defined.

Lemma if_is_set_then_circles_contract : forall {X : Type}, isSet X -> 
           (forall (l : Circle -> X), (map_on_paths l loop) ~~> (idpath (l base))).
Proof.
  intros X isSetX l.  apply isSetX.
Defined.

Lemma pi0_is_set : forall {X:Type}, isSet (pi0 X).
Proof.
  intros X.
  apply if_loops_contract_then_is_set.
  apply if_circles_contract_then_loops_contract.
  exact pi0_contr.
Defined.





(* Deriving Mike’s statements of the axioms from mine: *)

Definition map_dep {A} {P} f {x y} p := @dependent_map_on_paths A P f x y p.

(* Definition pi0 {X:Type} — already defined. *)

Definition pi0_cpnt {X} := @pi0_cmpt X.

Lemma pi0_axiomK : forall {A : Type} (x : pi0 A) (l : x ~~> x), l ~~> idpath x.
Proof.
  intros A.  apply if_circles_contract_then_loops_contract.  exact pi0_contr.
Defined.    

(* what Mike’s calling “axiom K” is what I’ve been calling “loops contract” *)

Lemma fibred_K_implies_loops_contract_in_fibres :
  forall {X : Type} {axiomK : forall (x : X) (l : x ~~> x), l ~~> idpath x}
         {P : X -> Type}
         (fibred_K : forall (x : X) (l : x ~~> x) (z : P x)
                            (dl : transport l z ~~> z),
                    dl ~~> map (fun p: x ~~> x => transport p z) (axiomK x l)),
  forall (x : X) (z : P x) (p : z ~~> z), p ~~> idpath z.
Proof.
  intros X axiomK P fibred_K x z p.
  exact ((fibred_K x (idpath x) z p) @ ! (fibred_K x (idpath x) z (idpath z))). 
Defined.

Lemma pi0_rect' :
  forall {A : Type} {P : pi0 A -> Type}
         (dcpnt : forall (x : A), P (pi0_cpnt x))
         (daxiomK : forall (x : pi0 A) (l : x ~~> x) (z : P x)
                           (dl : transport l z ~~> z),
                    dl ~~> map (fun p: x ~~> x => transport p z) (pi0_axiomK x l)),
  forall (x : pi0 A), P x.
Proof.
  intros A P dcpnt daxiomK.  apply (@pi0_rect A P dcpnt).
(* The only non-trivial hypothesis for pi0_rect is ‘d_contr’. *)
(* For this, we need a lemma: *)
  assert (forall (x : pi0 A), isSet (P x)) as fibres_are_sets.
    intros x.
    apply if_loops_contract_then_is_set.
    apply (fibred_K_implies_loops_contract_in_fibres (axiomK := pi0_axiomK)).  
    assumption.
(* Now we can easily construct ‘d_contr’:*)
  intros l k; apply fibres_are_sets.
Defined.

Lemma pi0'_compute_cpnt :
  forall {A : Type} {P : pi0 A -> Type}
         (dcpnt : forall (x : A), P (pi0_cpnt x))
         (daxiomK : forall (x : pi0 A) (l : x ~~> x) (z : P x)
                           (dl : transport l z ~~> z),
                    dl ~~> map (fun p: x ~~> x => transport p z) (pi0_axiomK x l))
         (a : A),
  pi0_rect' dcpnt daxiomK (pi0_cpnt a) ~~> dcpnt a.
Proof.
  intros A P dpnt daxiomK a.
  apply pi0_comp_cmpt.
Defined.
 
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
(* not needed by Mike: *)
 simpl.  path_tricks.
Defined.

Lemma pi0_compute_axiomK : 
  forall {A : Type} {P : pi0 A -> Type}
         (dcpnt : forall (x : A), P (pi0_cpnt x))
         (daxiomK : forall (x : pi0 A) (l : x ~~> x) (z : P x)
                           (dl : transport l z ~~> z),
                    dl ~~> map (fun p: x ~~> x => transport p z) (pi0_axiomK x l))
         (x : pi0 A) (l : x ~~> x),
    map2_dep_loop (pi0_rect' dcpnt daxiomK) (pi0_axiomK x l)
  ~~>
    daxiomK x l (pi0_rect' dcpnt daxiomK x) (map_dep (pi0_rect' dcpnt daxiomK) l).
Proof.
  intros A P dcpnt daxiomk.
  assert (forall (x : pi0 A), isSet (P x)) as fibres_are_sets.
    intros x.
    apply if_loops_contract_then_is_set.
    apply (fibred_K_implies_loops_contract_in_fibres (axiomK := pi0_axiomK)).
    assumption.
  assert (forall (x : pi0 A) (z z' : P x), isSet (z ~~> z')) as fibres_are_hlevel_3.
    intros x.
    apply set_implies_hlevel_3.
    apply fibres_are_sets.
  intros x l.  apply fibres_are_hlevel_3.
Defined.
(* This proof can be shortened a bit, β-reducing the first assertion within the second; but I think this separation is a little more perspicuous. *)




