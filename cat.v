Require Import Program.

Set Implicit Arguments.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section variables.
  Variable tvar : Type.

  Inductive type :=
  | TVar (x : tvar)
  | Arrow (t1 t2 : type).

  Section var.
    Variable var : type -> Type.

    Inductive term : type -> Type :=
    | Var : forall t,
      var t -> term t
    | Abs : forall dom ran,
      (var dom -> term ran) -> term (Arrow dom ran)
    | App : forall dom ran,
      term (Arrow dom ran) -> term dom -> term ran.
  End var.

  Definition Term t := forall var, term var t.

  Section tvars.
    Variable tvarD : tvar -> Type.

    Fixpoint typeD (t : type) : Type :=
      match t with
        | Arrow t1 t2 => typeD t1 -> typeD t2
        | TVar a => tvarD a
      end.

    Fixpoint termD t (e : term typeD t) : typeD t :=
      match e with
        | Var _ x => x
        | Abs _ _ e1 => fun x => termD (e1 x)
        | App _ _ e1 e2 => (termD e1) (termD e2)
      end.

    Definition TermD t (E : Term t) : typeD t :=
      termD (E _).
  End tvars.
End variables.

Section finVariables.
  Inductive finType : Type -> Type :=
  | fTVar : finType unit
  | fArrow : forall n m : Type,
               finType n -> finType m -> finType (n + m).

  Fixpoint type_of_finType n tvar (t : finType n)
  : (n -> tvar) -> type tvar
    := match t in finType n return (n -> _) -> _ with
         | fTVar => fun tvars => TVar (tvars tt)
         | fArrow tn tm t1 t2 =>
           fun tvars =>
             Arrow
               (@type_of_finType _ _ t1 (fun x => tvars (inl x)))
               (@type_of_finType _ _ t2 (fun x => tvars (inr x)))
       end.

  Section var.
    Variable tvar : Type.
    Variable var : finType tvar -> Type.

    Inductive finTerm : finType tvar -> Type :=
    | fVar : forall t,
      var t -> term t
    | Abs : forall dom ran,
      (var dom -> term ran) -> term (Arrow dom ran)
    | App : forall dom ran,
      term (Arrow dom ran) -> term dom -> term ran.
  End var.

  Definition Term t := forall var, term var t.

  Section tvars.
    Variable tvarD : tvar -> Type.

    Fixpoint typeD (t : type) : Type :=
      match t with
        | Arrow t1 t2 => typeD t1 -> typeD t2
        | TVar a => tvarD a
      end.

    Fixpoint termD t (e : term typeD t) : typeD t :=
      match e with
        | Var _ x => x
        | Abs _ _ e1 => fun x => termD (e1 x)
        | App _ _ e1 e2 => (termD e1) (termD e2)
      end.

    Definition TermD t (E : Term t) : typeD t :=
      termD (E _).
  End tvars.
End variables.


(*
Section finVariables.
  Variable tvar : Type.
  Variable count_occ : type tvar -> nat.

  Check @term tvar (fun t => Fin (count_occ t)).
  Section var.
    Inductive finTerm n : finType n -> Type :=
    | fVar : forall f : Fin n, finTerm (TVar f)
    | fAbs : forall dom ran,
               (var dom -> term ran) -> term (Arrow dom ran)
    | App : forall dom ran,
      term (Arrow dom ran) -> term dom -> term ran.
  End var.

  Definition Term t := forall var, term var t.

  Section tvars.
    Variable tvarD : tvar -> Type.

    Fixpoint typeD (t : type) : Type :=
      match t with
        | Arrow t1 t2 => typeD t1 -> typeD t2
        | TVar a => tvarD a
      end.

    Fixpoint termD t (e : term typeD t) : typeD t :=
      match e with
        | Var _ x => x
        | Abs _ _ e1 => fun x => termD (e1 x)
        | App _ _ e1 e2 => (termD e1) (termD e2)
      end.

    Definition TermD t (E : Term t) : typeD t :=
      termD (E _).
  End tvars.
End variables.
*)
Record category := {
  Object :> Type;
  Morphism : Object -> Object -> Type;

  Identity : forall o, Morphism o o
}.

Definition op : category -> category :=
  fun C => {| Object := Object C;
              Morphism x y := Morphism C y x;
              Identity x := Identity C x |}.

Record indexedFunctor idx (Cs : idx -> category) (D : category) := {
  ObjectOf :> (forall i, Cs i) -> D;
  MorphismOf : forall (Xs Ys : forall i, Cs i),
                 (forall i, Morphism (Cs i) (Xs i) (Ys i))
                 -> Morphism D (ObjectOf Xs) (ObjectOf Ys)
}.

Definition cat : category :=
  {| Object := category;
     Morphism C D := indexedFunctor (fun _ : unit => C) D;
     Identity C := {| ObjectOf f := f tt;
                      MorphismOf x y m := m tt |}
  |}.

Definition naturalTransformation idx Cs D (F G : @indexedFunctor idx Cs D) :=
  forall (Xs : forall i, Cs i), Morphism D (F Xs) (G Xs).

Definition indexedFunctorCategory idx (Cs : idx -> category) (D : category) :=
  {|
    Object := indexedFunctor Cs D;
    Morphism := @naturalTransformation idx Cs D;
    Identity := fun f x => Identity D (f x)
  |}.

Definition compose_functors_1 idx Cs D D'
        (F : @indexedFunctor unit (fun _ => D) D')
        (G : @indexedFunctor idx Cs D)
: @indexedFunctor idx Cs D'
  := {| ObjectOf x := ObjectOf F (fun _ => ObjectOf G x);
        MorphismOf x y m := MorphismOf F _ _ (fun _ => MorphismOf G _ _ m) |}.

Definition compose_functors idx idx'
           (Cs : idx -> category) (Ds : idx' -> category) D'
           (F : @indexedFunctor idx' Ds D')
           (G : forall i, @indexedFunctor idx Cs (Ds i))
: @indexedFunctor idx Cs D'
  := {| ObjectOf x := ObjectOf F (fun i => ObjectOf (G i) x);
        MorphismOf x y m := MorphismOf F _ _ (fun i => MorphismOf (G i) _ _ m) |}.

Definition indexedFunctorCategory_last_helper C D
           idx (Cs : idx -> category)
           (m : indexedFunctor (fun _ : unit => D) C)
: indexedFunctor (fun _ : unit => indexedFunctorCategory Cs D)
                 (indexedFunctorCategory Cs C).
Proof.
  let Cs := match goal with |- indexedFunctor ?Cs ?D => constr:(Cs) end in
  let D := match goal with |- indexedFunctor ?Cs ?D => constr:(D) end in
  refine (Build_indexedFunctor
            Cs
            D
            (compose_functors m)
            (fun Xs Ys T => fun Xs0 => MorphismOf m _ _ (fun i => T i Xs0))).
Defined.

Definition indexedFunctor_rest_helper
           idx (Cs C's : idx -> category)
           (D : category)
           (F : forall i, indexedFunctor (fun _ : unit => C's i) (Cs i))
           (G : indexedFunctor Cs D)
:  indexedFunctor C's D
  := Build_indexedFunctor
       C's D
       (fun X' =>
          G (fun i => (F i) (fun _ => X' i)))
       (fun Xs Ys Ms =>
          MorphismOf G _ _ (fun i =>
                              MorphismOf (F i) _ _ (fun _ => Ms i))).

Definition indexedFunctorCategory_rest_helper
           idx (Cs C's : idx -> category)
           (D : category)
           (F : forall i, indexedFunctor (fun _ : unit => C's i)
                                         (Cs i))
  := Build_indexedFunctor
       (fun _ : unit =>
          indexedFunctorCategory Cs D)
       (indexedFunctorCategory C's D)
       (fun X => indexedFunctor_rest_helper _ F (X tt))
       (fun Xs Ys Ms _ => Ms tt _).

Definition indexedFunctorCategoryFunctor idx
: indexedFunctor (fun i : option idx => match i with None => cat | Some _ => op cat end) cat
  := Build_indexedFunctor (fun i : option idx => match i with
                                                   | None => cat
                                                   | Some _ => op cat
                                                 end)
                          cat
                          (fun f => @indexedFunctorCategory idx (fun i => f (Some i)) (f None))
                          (fun Xs Ys Ms =>
                             compose_functors
                               (indexedFunctorCategory_last_helper _ (Ms None))
                               (fun ttt =>
                                  indexedFunctorCategory_rest_helper
                                    (fun i => Xs (Some i))
                                    (fun i => Ys (Some i))
                                    (Xs None)
                                    (fun i => Ms (Some i)))).

Section typeCat.
  Variable tvar : Type.
  Variable tvars : tvar -> category.

  Fixpoint typeCat (t : type tvar) : category
    := match t with
         | TVar a => tvars a
         | Arrow t1 t2 => indexedFunctorCategory
                            (fun _ : unit => typeCat t1)
                            (typeCat t2)
       end.

  Definition selection_functor (a : tvar) : indexedFunctor tvars cat
    := Build_indexedFunctor tvars cat
                            (fun x => tvars a)
                            (fun xs ys ms => Identity _ _).

  Program Fixpoint termCat t (e : term typeCat t)
  : indexedFunctor tvars (typeCat t) :=
    match e in term _ t return indexedFunctor tvars (typeCat t) with
      | App _ _ e1 e2 => (termCat e1) (termCat e2)
      | Var _ x => selection_functor _
      | Abs _ _ e1 => e1
    end.

  Next Obligation.
    simpl; fold typeCat; intros.
    Check (fun P H0 H1 H2 x => term_rect P H0 H1 H2 (e1 x)).


  Fixpoint typeCat (t : type tvar) : indexedFunctor tvars cat.
  refine match t with
           | TVar a => selection_functor a
           | Arrow t1 t2 => _
         end.
  assert ((forall i, tvars i) -> cat).
  Set Printing Coercions.
indexedFunctorCategoryFunctor _
(fun _ : unit => typeCat t1) (typeCat t2)

  Axiom cheat : forall T, T.

  Program Fixpoint termCat t (e : term typeCat t) : typeCat t :=
    match e in term _ t return typeCat t with
      | App _ _ e1 e2 => (termCat e1) (termCat e2)
      | Var _ x => x
      | Abs _ _ e1 => {| ObjectOf := fun x => termCat (e1 x);
        MorphismOf := _ |}
    end.

  Next Obligation.
    simpl; fold typeCat; intros.
    Check (fun P H0 H1 H2 x => term_rect P H0 H1 H2 (e1 x)).

Theorem identity_something :.
