Add LoadPath "../UnivalentFoundations".

Require Import Homotopy.
Require Import Menagerie.


Definition isProp (X:Type) := forall {x y : X}, x ~~> y.
Definition isSet (X:Type) := forall {x y : X}, isProp (x ~~> y). 

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


(*
Inductive pi0 (X:Type) : Type :=
    | incl : X -> pi0 X
    | contr : forall (l : Circle -> pi0 X), paths (idpath (l base)) (cong l loop)
*)

Axiom pi0 : Type -> Type.

Axiom cmpt : forall {X} (x:X), (pi0 X).

Axiom contr : forall {X} (l : Circle -> (pi0 X)), (map_on_paths l loop) ~~> (idpath (l base)).



Axiom pi0_rect : forall {X} {P : (pi0 X -> Type)}
                    (d_cmpt : forall x:X, P (cmpt x))
                    (d_contr : forall (l : Circle -> (pi0 X))  (k : forall a:Circle, P (l a)),
                      let id_coerced_along_contr :=
                         ( transp_along_map_on_paths
                         @ (map_on_paths (fun u : l base ~~> l base => transport u (k base)) (contr l)) )
                      in
                         (id_coerced_along_contr) ~~> (dependent_map_on_paths k loop)),
                 forall (z : pi0 X), P z.

Axiom pi0_comp_cmpt : forall {X} {P} {d_cmpt} {d_contr} (x:X),
                             (@pi0_rect X P d_cmpt d_contr (cmpt x)) ~~> (d_cmpt x). 

(* Axiom pi0_comp_contr *)
(* Horrible to type… but actually should be redundant for homotopical reasons anyway, I think, so hopefully leaving it out will not hurt us. *)

Lemma pi0_nondep_rect {X} {Y} (s : isSet Y) (f : X -> Y)
                      : pi0 X -> Y.
Proof.
  apply (@pi0_rect X (fun _ => Y) f); intros.  apply s.
Defined.

Lemma pi0_nondep_comp : forall {X} {Y} {s} {f} (x:X), (@pi0_nondep_rect X Y s f (cmpt x) ~~> (f x)).
Proof.
  intros; unfold pi0_nondep_rect.  exact (pi0_comp_cmpt (P := fun _ => Y) x).
Defined.  (* maybe could/should leave opaque, since is a path in a set? *)

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
  (* a bunch of messing around with naturality and transport_in_trivial_fibration *)
Admitted.


Lemma if_circles_contract_then_loops_contract {X : Type} :
        (forall (l : Circle -> X), (map_on_paths l loop) ~~> (idpath (l base)))
        -> forall (x:X) (p : x ~~> x), (p ~~> idpath x).
Proof.
  intros contr x p.
  set (p_as_circle := Circle_nondep_rect p). 
  set (almost_goal := contr p_as_circle).
(* roughly:
    p
 ~~>    [by !Circle_nondep_comp_loop and some messing around]
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
    (* units/inverses are folded away automagically in both subgoals *)
Defined.

Lemma if_loops_contract_then_isset {X : Type} :
        forall (x:X) (p : x ~~> x), (p ~~> idpath x) 
        -> isSet X.
Proof.
  intros contr x y u v.
