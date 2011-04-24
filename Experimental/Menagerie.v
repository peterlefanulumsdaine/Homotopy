Add LoadPath "../UnivalentFoundations".

Require Import Homotopy.

(** Some general constructions which we will use: *)

Definition map_on_paths {A B} {x x'} := @map A B x x'.  (* Just an alias. *)

Definition dependent_map_on_paths {A} {P : A -> Type} (f : forall x : A, P x) 
              {x y : A} (p : x ~~> y) :
              transport p (f x) ~~> f y.
Proof.
  path_induction.
Defined.

Lemma self_transport_path {A} {x y : A} (p : x ~~> y)
            : transport (P := fun z => z ~~> y) p p ~~> idpath y.
Proof.
  path_induction.
Defined.

Lemma transport_in_trivial_fibration {A B} {x y : A} (p : x ~~> y) (u : B)
            : transport (P := fun _ => B) p u ~~> u.
Proof.
  path_induction.
Defined.

Lemma strong_ctrn_from_wk {A} 
            : contractible A -> forall x y : A, x ~~> y.
Proof.
  intros [c p] x y.
  path_via c.
Defined.


(*
Inductive Interval : Type :=
    | left : Interval
    | right : Interval
    | segment : Paths left right.
*)

Axiom Interval : Type.

Axiom left : Interval.
Axiom right : Interval.
Axiom segment : left ~~> right.

Axiom Interval_rect :
         forall {P : (Interval -> Type)}
                (d_left : P left)
                (d_right : P right)
                (d_segment : (transport segment d_left) ~~> d_right),
         forall x : Interval, P x.

Axiom Interval_comp_left :
         forall {P} {d_left} {d_right} {d_segment},
         (@Interval_rect P d_left d_right d_segment) left ~~> d_left.

Axiom Interval_comp_right :
         forall {P} {d_left} {d_right} {d_segment},
         (@Interval_rect P d_left d_right d_segment) right ~~> d_right.

Axiom Interval_comp_segment :
         forall {P} {d_left} {d_right} {d_segment},
             ( (map_on_paths (transport (P := fun x => P x) segment) (! Interval_comp_left))
             @ (dependent_map_on_paths (@Interval_rect P d_left d_right d_segment) segment) 
             @ Interval_comp_right)
           ~~>
             d_segment.

(*
Inductive Circle : Type :=
    | base : Circle
    | loop : Paths base base.
*)

Axiom Circle : Type.

Axiom base : Circle.
Axiom loop : base ~~> base.

Axiom Circle_rect :
         forall {P : (Circle -> Type)}
                (d_base : P base)
                (d_loop : (transport loop d_base) ~~> d_base),
         forall x : Circle, P x.

Axiom Circle_comp_base :
         forall {P} {d_base} {d_loop},
         (@Circle_rect P d_base d_loop) base ~~> d_base.

Axiom Circle_comp_loop :
         forall {P} {d_base} {d_loop},
             ( (map_on_paths (transport (P := fun x => P x) loop) (! Circle_comp_base))
             @ (dependent_map_on_paths (@Circle_rect P d_base d_loop) loop) 
             @ Circle_comp_base)
           ~~>
             d_loop.
 
(*
Inductive Circle' : Type :=
    | east : Circle
    | west : Circle'
    | upper : Paths left right
    | lower : Paths right left.
*)

Axiom Circle' : Type.

Axiom east : Circle'.
Axiom west : Circle'.
Axiom upper : east ~~> west.
Axiom lower : west ~~> east.

Axiom Circle'_rect :
         forall {P : (Circle' -> Type)}
                (d_east : P east) (d_west : P west)
                (d_upper : (transport upper d_east) ~~> d_west)
                (d_lower : (transport lower d_west) ~~> d_east),
         forall x : Circle', P x.

Axiom Circle'_comp_east :
         forall {P} {d_east} {d_west} {d_upper} {d_lower},
         (@Circle'_rect P d_east d_west d_upper d_lower) east ~~> d_east.

Axiom Circle'_comp_west :
         forall {P} {d_east} {d_west} {d_upper} {d_lower},
         (@Circle'_rect P d_east d_west d_upper d_lower) west ~~> d_west.

Axiom Circle'_comp_upper :
         forall {P} {d_east} {d_west} {d_upper} {d_lower},
             ( (map_on_paths (transport (P := fun x => P x) upper) (! Circle'_comp_east))
             @ (dependent_map_on_paths (@Circle'_rect P d_east d_west d_upper d_lower) upper) 
             @ Circle'_comp_west)
           ~~>
             d_upper.

Axiom Circle'_comp_lower :
         forall {P} {d_east} {d_west} {d_upper} {d_lower},
             ( (map_on_paths (transport (P := fun x => P x) lower) (! Circle'_comp_west))
             @ (dependent_map_on_paths (@Circle'_rect P d_east d_west d_upper d_lower) lower) 
             @ Circle'_comp_east)
           ~~>
             d_lower.

(* Inductive Cell2 : Type :=
    | src0 : Cell2
    | tgt0 : Cell2
    | src1 : src0 ~~> tgt0
    | tgt1 : src0 ~~> tgt0
    | cell2 : src1 ~~> Tgt1
*)

Axiom Cell2 : Type.

Axiom src0 : Cell2.  Axiom tgt0 : Cell2.
Axiom src1 : src0 ~~> tgt0.  Axiom tgt1 : src0 ~~> tgt0.
Axiom cell2 : src1 ~~> tgt1.


Axiom Cell2_rect :
         forall {P : (Cell2 -> Type)}
                (d_src0 : P src0) (d_tgt0 : P tgt0)
                (d_src1 : (transport src1 d_src0) ~~> d_tgt0)
                (d_tgt1 : (transport tgt1 d_src0) ~~> d_tgt0)
                (d_cell2 : (transport (P := fun (p : src0 ~~> tgt0) => ((transport p d_src0) ~~> d_tgt0))
                            cell2 d_src1)
                            ~~> d_tgt1),
         forall x : Cell2, P x.

Axiom Cell2_comp_src0 :
         forall {P} {d_src0} {d_tgt0} {d_src1} {d_tgt1} {d_cell2},
         (@Cell2_rect P d_src0 d_tgt0 d_src1 d_tgt1 d_cell2) src0 ~~> d_src0.

Axiom Cell2_comp_tgt0 :
         forall {P} {d_src0} {d_tgt0} {d_src1} {d_tgt1} {d_cell2},
         (@Cell2_rect P d_src0 d_tgt0 d_src1 d_tgt1 d_cell2) tgt0 ~~> d_tgt0.

Axiom Cell2_comp_src1 :
         forall {P} {d_src0} {d_tgt0} {d_src1} {d_tgt1} {d_cell2},
             ( (map_on_paths (transport (P := fun x => P x) src1) (! Cell2_comp_src0))
             @ (dependent_map_on_paths (@Cell2_rect P d_src0 d_tgt0 d_src1 d_tgt1 d_cell2) src1) 
             @ Cell2_comp_tgt0)
           ~~>
             d_src1.

Axiom Cell2_comp_tgt1 :
         forall {P} {d_src0} {d_tgt0} {d_src1} {d_tgt1} {d_cell2},
             ( (map_on_paths (transport (P := fun x => P x) tgt1) (! Cell2_comp_src0))
             @ (dependent_map_on_paths (@Cell2_rect P d_src0 d_tgt0 d_src1 d_tgt1 d_cell2) tgt1) 
             @ Cell2_comp_tgt0)
           ~~>
             d_tgt1.

(*
Axiom Cell2_comp_cell2 : the type of this is horrendous.  Can be simplified with “higher John Major path types” perhaps?
*)

(*
Inductive Sphere2 : Type :=
    | base2 : Sphere
    | surf2 : Paths (@refl base2) (@refl base2).
*)


Axiom Sphere2 : Type.

Axiom base2 : Sphere2.
Axiom surf2 : (idpath base2) ~~> (idpath base2).

Axiom Sphere2_rect :
         forall {P : (Sphere2 -> Type)}
                (d_base2 : P base2)
                (d_surf2 : (transport (P := fun (p : base2 ~~> base2) => ((transport p d_base2) ~~> d_base2))
                            surf2 (idpath d_base2))
                            ~~> (idpath d_base2)),
         forall x : Sphere2, P x.

Axiom Sphere2_comp_base2 :
         forall {P} {d_base2} {d_surf2},
         (@Sphere2_rect P d_base2 d_surf2) base2 ~~> d_base2.

(* Axiom Sphere2_comp_surf2 : again omitted for now due to horrendous type *)

(*
Inductive Susp (X : Type) : Type :=
    | north : Susp X
    | south : Susp X
    | merid : X -> Paths north south.
*)

Axiom Susp : forall X : Type, Type.

Axiom north : forall {X : Type}, Susp X.
Axiom south : forall {X : Type}, Susp X.
Axiom merid : forall {X : Type}, X -> (@north X) ~~> (@south X).


Axiom Susp_rect :
         forall {X : Type} {P : (Susp X) -> Type}
                (d_north : P north)
                (d_south : P south)
                (d_merid : forall x : X, (transport (merid x) d_north) ~~> d_south),
         forall x : Susp X, P x.

Axiom Susp_comp_north :
         forall {X} {P} {d_north} {d_south} {d_merid},
         (@Susp_rect X P d_north d_south d_merid) north ~~> d_north.

Axiom Susp_comp_south :
         forall {X} {P} {d_north} {d_south} {d_merid},
         (@Susp_rect X P d_north d_south d_merid) south ~~> d_south.

Axiom Susp_comp_merid :
         forall {X} {P} {d_north} {d_south} {d_merid},
         forall (x:X),
             ( (map_on_paths (transport (P := fun z => P z) (merid x)) (! Susp_comp_north))
             @ (dependent_map_on_paths (@Susp_rect X P d_north d_south d_merid) (merid x)) 
             @ Susp_comp_south)
           ~~>
             d_merid x.

(*
Inductive Cyl {X Y : Type} (f : X -> Y) : Y -> Type :=
    | cyl_base : forall y:Y, Cyl f y
    | cyl_top : forall x:X, Cyl f (f x)
    | cyl_seg : forall x:X, Paths (intop x) (inbase (f x)).
*)

Axiom Cyl : forall {X Y : Type} (f : X -> Y), Y -> Type.

Axiom cyl_base : forall {X Y} {f:X->Y}, forall (y:Y), Cyl f y.
Axiom cyl_top : forall {X Y} {f:X->Y}, forall (x:X), Cyl f (f x).
Axiom cyl_seg : forall {X Y} {f:X->Y}, forall (x:X), (cyl_top x) ~~> (cyl_base (f x)).
(* is it more convenient to make `f` implicit or explicit in these constructors? *) 

Axiom Cyl_rect : forall {X Y} {f:X->Y} {P : forall y, Cyl f y -> Type},
                 forall (d_base : forall y:Y, P y (cyl_base y))
                        (d_top : forall x:X, P (f x) (cyl_top x))
                        (d_seg : forall x:X, (transport (cyl_seg x) (d_top x)) ~~> (d_base (f x))),
                 forall (y : Y) (z : Cyl f y), P y z.

Axiom Cyl_comp_base : 
                 forall {X Y} {f} {P} {d_base} {d_top} {d_seg},
                 forall y:Y, (@Cyl_rect X Y f P d_base d_top d_seg) y (cyl_base y) ~~> d_base y.

Axiom Cyl_comp_top :
                 forall {X Y} {f} {P} {d_base} {d_top} {d_seg},
                 forall x:X, (@Cyl_rect X Y f P d_base d_top d_seg) (f x) (cyl_top x) ~~> d_top x.

Axiom Cyl_comp_seg :
                 forall {X Y} {f:X->Y} {P:forall (y:Y) (z:Cyl f y), Type} {d_base} {d_top} {d_seg},
                 forall x:X, 
             ( (map_on_paths (transport (P := fun z => P (f x) z) (cyl_seg x)) (! (Cyl_comp_top x)))
             @ (dependent_map_on_paths (@Cyl_rect X Y f P d_base d_top d_seg (f x)) (cyl_seg x)) 
             @ Cyl_comp_base (f x))
           ~~>
             (d_seg x).


(*
Inductive isInhab (X:Type) : Type :=
    | proj : X -> isInhab X
    | contr : forall (y y' : isInhab X), Paths y y'.
*)

Axiom isInhab : forall (X:Type), Type.

Axiom proj : forall {X}, X -> isInhab X.
Axiom contr : forall {X}, forall (z z' : isInhab X), z ~~> z'.

Axiom isInhab_rect : forall {X:Type},
         forall {P : isInhab X -> Type}
                (d_proj : forall x:X, P (proj x))
                (d_contr : forall (z z' : isInhab X) (w : P z) (w' : P z'), (transport (contr z z') w) ~~> w'),
         forall z : isInhab X, P z.

Axiom isInhab_comp_proj :
         forall {X} {P} {d_proj} {d_contr},
         forall (x : X), (@isInhab_rect X P d_proj d_contr) (proj x) ~~> (d_proj x).

Axiom isInhab_comp_contr :
         forall {X} {P} {d_proj} {d_contr},
         forall {z z' : isInhab X},
             (dependent_map_on_paths (@isInhab_rect X P d_proj d_contr) (contr z z')) 
           ~~>
             d_contr z z' (@isInhab_rect X P d_proj d_contr z) (@isInhab_rect X P d_proj d_contr z').

(*
Inductive tr0 (X:Type) : Type :=
    | incl : X -> tr0 X
    | contr : forall (l : S1 -> X), Paths (refl (l base)) (cong l loop)
*)

