(** * Finitary endofunctors preserve epis

(compiles with UniMath 9e1009089faa45c7cfbae3520df8bb7c5927d4ed and Coq 8.9)

A finitary endofunctor (on hSet) is a an endofunctor F on sets such that the
canonical morphism

<<<
colim (FinSet / X --> Set -- F --> Set) ---> F X
>>>

is an isomorphism (see [isFinitary]).


The main theorem [FinitaryPreserveEpis] states that any finitary endofunctor
preserves surjections: if f : X → Y is surjective, then # F f also is.

The proof is done without using excluded middle.

The idea is to restrict to finite sets using finitary sets for which some axiom
 of choice holds constructively.

The key lemma is [FinColim_mor_preserves_epi], stating that for any functor F and
any surjective map f : X → Y, the induced map

>>>
colim (FinSet / X -> Set -- F --> Set) -> colim (FinSet / Y --> Set -- F --> Set)
<<<

is surjective.



*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Subcategory.Limits.

Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.categories.FinSet.
Require Import UniMath.CategoryTheory.UnderCategories.
Require Import UniMath.CategoryTheory.CommaCategories.
Require Import UniMath.CategoryTheory.elems_slice_equiv.
Require Import UniMath.Combinatorics.FiniteSets.



  

Open Scope cat.




Local Notation "'SET' / X" := (slice_precat SET X has_homsets_HSET) (at level 3).

Definition is_finite_slice (X : hSet) (fX : SET / X) : hProp :=
  finite_subtype (pr1 fX).


Definition FinSetSlice_precategory (X : hSet) : precategory :=
  full_sub_precategory (C := SET / X) (is_finite_slice X).


Local Notation "'FINSET' / X" := (FinSetSlice_precategory X) (at level 3).

(**
From a slice object u : U --> X on X, we get a slice object f ∘ u : U --> Y on Y.
(this is actually functorial of course)
 *)
Definition FinSetSlice_Mor_ob  {X Y : hSet} (f : X -> Y) :
  (FINSET / X) -> (FINSET / Y).
Proof.
  intro v.
  use make_carrier.
  + eapply tpair.
    refine ( (f ∘ (pr2 (pr1 v)))).
  + exact (pr2 v).
Defined.

Local Notation "'FINSET' #/ f" := (FinSetSlice_Mor_ob f) (at level 3).

Definition FinSetSlice_Mor_mor {X Y : hSet} (f : X -> Y) 
           {v1 v2}(u : FINSET / X ⟦ v1, v2 ⟧) :
  FINSET / Y ⟦ FINSET #/ f v1, FINSET #/ f v2 ⟧.
Proof.
    use make_carrier.
    + unshelve eapply tpair.
      * refine ((pr1 (pr1 u))).
      * cbn -[compose].
        etrans; revgoals.
        { apply pathsinv0,  (assoc (C := SET)). }
        apply (cancel_postcomposition  (C := SET)).
        exact (pr2 (pr1 (u))).
    + exact (pr2 u).
Defined.

Local Notation "'FINSET' ##/ f" := (FinSetSlice_Mor_mor f) (at level 3).


(** The forgetful functor FinSet / X -> Set mapping u : U → X to U *)
Definition forget_FinSetSlice (X : hSet) : FINSET / X ⟶ HSET :=
  (sub_precategory_inclusion _ _ ∙ slicecat_to_cat _ _).

(** as a diagram *)
Definition J (X : hSet) :=
  (diagram_from_functor (FINSET / X) HSET (forget_FinSetSlice X)).

Local Infix "▤" := mapdiagram (at level 20).

(* Definition colimFJ (F : HSET ⟶ HSET)(X : hSet) := coSet (F (J X)). *)


(* Colimits in Set *)
Local Notation coSET d := (ColimsHSET_of_shape _ d).


(** Canonical morphism
colim (FinSet / X --> Set -- F --> Set) ---> F X
*)
Definition canonical_finitary_mor (F : HSET ⟶ HSET) (X : hSet) :
  SET ⟦  colim (coSET (F ▤ J X)) , F X⟧.
Proof.
  use colimArrow.
  use make_cocone.
  - intro v.
    exact (# F (pr21 v)).
  - intros u v e.
    cbn -[compose].
    etrans.
    {
      apply pathsinv0, (functor_comp F).
    }
    apply maponpaths.
    apply pathsinv0.
    exact (pr21 e).
Defined.

Definition isFinitary (F : HSET ⟶ HSET) :=
  ∏ (X : hSet), isweq (canonical_finitary_mor F X).


(**
Any map f : X → Y induces a map between colimits
colim (FinSet / X --> Set)  → colim (FinSet / Y --> Set)
*)
Definition FinColim_mor (F : HSET ⟶ HSET) {X Y : hSet} (f : X -> Y) :
  (colim (coSET ( F ▤ (J X))) : hSet) ->
  (colim (coSET ( F ▤ (J Y))) : hSet).
Proof.
  set (cY := (coSET ( F ▤ (J Y)))).
  use (colimArrow (C := SET)).
  use make_cocone.
  - intro v.
    set (v' := FINSET #/ f v).
    exact (colimIn (C := SET) cY v').
  - intros u v e.
    set (e' := (FINSET ##/ f e)).
    change  ( dmor ( F ▤ (J X)) e) 
            with 
              ( dmor ( F ▤ (J Y)) e').
    apply (colimInCommutes (C := SET) cY _ _ e').
Defined.


(**
if [f : X -> Y] is surjective, then, for  each slice object u : n → Y on Y,
there is a slice object w : n → X on X s.t.
<<<
   w
n ---> X
 \     |
  \    |  f
 u \   V
    \> Y
     
>>>
This works because n is finite (thus we can use some axiome of choice)
 *)
Definition lift_slice_epi  {X Y : hSet} (f : X -> Y) (surjf : issurjective f)
  (v : FINSET / Y) 
  (** n : the underlying finite set of the slice v *)
  (n := (pr1 (pr1 v)) : hSet) 
  (** u : the morphism *)
  (u := (pr2 (pr1 v)) : n -> Y)  :
  ∥ ∑ (w : SET ⟦ n, X ⟧) , f ∘ w = u  ∥.
Proof.
  assert (h : ishinh (∏ (p : n), ∑ (x : X), f x =  u p)).
  {
    use ischoicebasefiniteset.
    + exact (pr2 v).
    + intro p.
      apply surjf.
    }
  revert h.
  use hinhfun.
  intro P.
  refine ((fun p => pr1 (P p)),, _).
  apply funextfun.
  intro p.
  exact (pr2 (P p)).
Defined.


(**
If f is surjective, then the canonical map
<<<
colim (FinSet / X --> Set)  → colim (FinSet / Y --> Set)
>>>
also is
 *)
Lemma FinColim_mor_preserves_epi (F : HSET ⟶ HSET) {X Y : hSet} (f : X -> Y) (epif : issurjective f) :
   issurjective (FinColim_mor F f).
Proof.
  red.
  use setquotunivprop.
  intros [v x].
  cbn in x.
  set (cX := coSET( F ▤ (J X))).
  set (cY := coSET( F ▤ (J Y))).
  change (setquotpr _ _) with (colimIn (C := SET) cY v x).
  assert (v' := lift_slice_epi f epif v).
  revert v'.
  eapply hinhfun.
  intros [w we].
  red.
  transparent assert (vX :   ( FINSET / X)).
  {
     use make_carrier.
      + exact (pr11 v ,, w).
      + exact (pr2 v).
 }
  use tpair.
  {
    use (colimIn (C := SET)).
    - exact vX.
    - exact x.
  }
  cbn beta.
  unfold FinColim_mor.
  set (cc := make_cocone _ _).
  etrans.
  {
    assert (h := colimArrowCommutes (C := SET) cX _ cc vX).
    apply (maponpaths (fun z => z x)) in h.
    exact h.
  }
  unfold cc.
  cbn -[colimIn].
  change v with ((pr11 v ,, pr21 v),, pr2 v).
  rewrite <- we.
  apply idpath.
Qed.

(**
Finitary endofunctors preserve epimorphisms.
The idea is that the following diagram commutes:

<<<
colim (F J_X) ----> colim (F J_Y)
      |                      |
      |                      |
      |                      |
      V                      V
     F X -----------------> F Y
>>>
where the right morphism is an isomorphisms (and thus surjective) by
finitarity, and the top morphism is surjective by [FinColim_mor_preserves_epi].
By composition of the top right surjections, the bottom left composition is also
a surjection, and so the bottom morphism is surjective.
 *)

(** Commutation of the square:

<<<
colim (F J_X) ----> colim (F J_Y)
      |                      |
      |                      |
      |                      |
      V                      V
     F X -----------------> F Y
>>>
*)
Lemma FinitaryPreserveEpis_aux_eq {F : HSET ⟶ HSET}  {X Y : hSet}
      (f : X -> Y) : (FinColim_mor F f : SET ⟦ _, _ ⟧) · canonical_finitary_mor F Y =
                    canonical_finitary_mor F X · # F f.
Proof.
  set (cX := coSET (F ▤ J X)).
  etrans.
  {
    apply postcompWithColimArrow.
  }
  etrans;[|apply pathsinv0,postcompWithColimArrow].
  apply colimArrowUnique.
  intro u.
  etrans;[apply colimArrowCommutes|].
  change (# F (pr21 u · f) = # F (pr21 u) · #F f).
  apply functor_comp.
Qed.



Lemma FinitaryPreserveEpis {F : HSET ⟶ HSET} (finF : isFinitary F) {X Y : hSet}
      (f : X -> Y)(epif : issurjective f) : issurjective (# F f).
Proof.
  eapply issurjtwooutof3b.
  eapply (transportf issurjective).
  - use FinitaryPreserveEpis_aux_eq.
  - use issurjcomp.
    + apply FinColim_mor_preserves_epi.
      exact epif.
    + apply issurjectiveweq.
      apply finF.
Qed.
