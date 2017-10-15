Section Ejercicio1.

(*Variable a a0 b c d p q x: Prop.*)


(*
Theorem e11 : a -> forall a:Set, forall b:Set, a.
Proof.
  intro.
  intro.
  intro.
  assumption.
*)

(*
Theorem e: forall x:Set, x -> forall y:Set, a.
Proof.
  intro.
  intro.
  intro.
*)

(*
Theorem e: (forall foralls:Set, foralls) -> a -> b.
Proof.
  intro.
  apply X.
Qed.

Print e.
*)

(*
Theorem e:(forall H:Set, H) -> (forall W:Set, W).
Proof.
  intro.
  assumption.
Qed.
*)

(*
Theorem e:a -> a -> a -> a.
Proof.
  intros.
  assumption.
Qed.

Print e.
*)

(*Theorem e:(forall H:Set, H->forall H:Set, H->forall H0:Set, H0) -> forall H:Set, a->H.*)

(*Theorem e:a->a0->forall a:Set, a->forall a1:Set, a1->a.*)

(*Theorem q:a->exists a:Prop, a -> forall y:Prop, y -> p.*)
(*
Theorem tt: (forall x:Prop, forall y:Prop, forall z:Prop, x -> z) -> (forall x:Prop, forall z:Prop, x -> z).
Proof.
  intro.
  intro.
  intro.
  intro.
Qed.
*)

(*
Theorem ee:forall a:Prop, a -> a.
Proof.
  intros; assumption.
Qed.

Theorem ee2: a -> a.
Proof.
  exact (ee a).
Qed.

Print ee2.

Theorem qq:(forall a:Prop, a -> a) -> (exists q:Prop, q->q).
Proof.
  intro.
  exists a0.
  intro;assumption.
Qed.

Print ex_intro.

Print qq.

End Ejercicio1.

Print qq.
*)

(*Theorem w:forall b9:Prop, b9 -> exists p:Prop, (a->forall a:Prop, forall b9:Prop, b9 /\ a/\p) -> (forall a:Prop, a/\p).*)

(*
Theorem qq : forall zz:Prop, zz -> (exists t:Prop, t).
Proof.
  intros.
  exists (forall zz:Prop, zz).
  intro.
Qed.
*)

(*
Theorem h:exists q:Prop, forall g:Prop, g -> q.
Proof.
  exists (forall g:Prop, g).
Qed.
*)
(*
Theorem tt : forall A, ~(A <-> ~A).
Proof.
  intros.
  unfold not.
  intros.

Qed.
*)

(* Casos para chequear la precedencia. *)
Variables p q r t
 g w: Prop.

Theorem k: p -> q -> 
p /\ q /\ p /\ p -> q.

Theorem k2: ~ (p /\ ~(q  -> ~p -> p /\ ~r -> q)) /\ r.

Theorem k3: p /\ q /\ p \/ r.

Theorem k4: p \/ q -> p.

Theorem k5: w -> g \/ p \/ q /\ r \/ w.


Definition asd x y 
:= forall w:Prop, 
forall v:Prop, 
x /\ y.

Print and.

Notation "A -- B" := (asd A B) (at level 75).

Theorem k6: p -- q /\ r -- w.

Theorem k7: p -> q <-> p -> q.
Proof.
unfold iff.
split.
intro.
assumption.
intro.
assumption.
Qed.

Print All. 

Theorem k8: forall x:Prop, x  -> p <-> forall y:Prop,y.
unfold iff.

Definition asd2 x := forall q:Prop, x -> q.
intro.

Print All.

Print k7.

Axiom k81 : forall x:Prop, x -> x.

Print k81.

Print All.

Theorem k82 : forall x:Prop, x -> x.
Proof.
  exact k81.
Qed.

Print k82.

intros.
auto.

Theorem k9: r /\ ~ asd p q -> w.
intro.

Theorem k10: ~(~~asd (asd2 p) (~w)).

Theorem k11: p -> q <-> p -> q.
exact k7.

Definition funn (w:Prop) := forall x: Prop, w -> x -> w.

Theorem k12: ~p \/ funn (~ ~ exists p: Prop, p -> p).
Proof.
  right.
  unfold funn.
  intros.
  assumption.
Qed.

Print k12.


Check (or_intror (~p) (((fun (x : Prop) (H : p) (_ : x) => H)):(funn p)) ).

Check (fun (aa : Prop) (H : aa) => fun (aa:Prop) => H).

Definition k14 := fun (aa : Prop) (H : aa) => fun (aa:Prop) (H2 : aa )=> H.

Print k14.


Theorem k15 : forall bb:Prop, forall aa : Prop, aa -> forall aa0 : Prop, aa0 -> aa.
Proof.
  intro.
  exact (fun (aa : Prop) (H : aa) => fun (aa:Prop) (H2 : aa )=> H).
Qed.

Print k15.

Theorem k166: forall x:Prop, x -> x.
Proof.
  auto.
Qed.

Theorem k16: (forall w:Prop, w) -> (forall k:Prop, k).
Proof.
  apply (k166 (forall w:Prop, w)).
Qed.

Print k16.

Check (fun H : forall w : Prop, w => H:(forall k:Prop, k)).

Theorem t21: p -> (forall p:Prop, p) /\ forall w:Prop, ~ forall p:Prop, w /\ p.


Definition x x y := forall w:Prop, forall v:Prop, x /\ y.

Print x.
Check x.

Print All.

Print t.


Theorem tt22 : forall w, (x w) (w -> w).

Theorem t22: forall c:Prop, c -> c.  Proof.  intros.  assumption.  Qed.

Definition tt22 := fun (c : Prop) (H : c) => H.

Print t22.

Definition tt2220 := fun (c : forall q:Prop, q -> q) (y : forall q:Prop, q -> q) => c.

Print tt2220.

Definition tt222 := fun (c : forall q:Prop, q -> q) (c0 : Prop) => c c0.

Print tt222.

Definition t23 := tt22 p.  Definition ttt := p.


Print t23.

Definition All := p.

Print All.

(*Variables xx:Prop.

Print xx.*)


Theorem xx: forall ttt:Prop, ttt -> ttt.
Proof.
  intros.
  assumption.
Qed.

Variables xx:Prop.

Theorem t25: forall q:Prop, (forall k:Prop, forall h:Prop, k->k) -> (q -> q).
Proof.
  intro.
  intro.
  apply H.
  exact (xx).
Qed.


Definition xxx := fun (w : Prop) (H : w) => H.

Definition yyy := fun (w : Prop) (xxx : w) => xxx.

Print yyy.

Definition xx2 := forall w, w.

Theorem t255:xx2->forall xx2:Prop,xx2->xx2.
Proof.
  auto.
Qed.

Print t255.

Check (fun (H0 : xx2) (xx2 : Prop) (H : xx2) => H0).

Theorem H: forall w:Prop, w -> w.
Proof.
  intros.
  assumption.
Qed.

Theorem H0: forall w:Prop, w -> w.
Proof.
  intros.
  exact(H w0 H0).
Qed.

Print H0.

Theorem t2555: (forall a:Prop, a) -> (forall a:Prop, a) -> (forall H1:Prop, H1 -> H1).
Proof.
intro.
intro.
intro.
auto.
Qed.

Print t2555.

Theorem t26: forall w:Prop, w -> w -> w.
Proof.
  intro.
  intro.
  cut (w0 -> w0).
  intro.
  exact (H w0).
  intros.
  assumption.
Qed.

Print t26.

Definition cut := forall w, w -> w.

Variables asd:Prop.

Definition Variables := forall w, w.


Theorem t27: forall theorem:Prop, forall intros:Prop, intros -> intros (* hola*).
Proof.
  intro.
  cut cut.
  intro.
  Definition intros := forall w, w.
  Variables qqq:Prop.
  Check asd.
  unfold intros.
  auto.
  unfold cut.
  auto.
Qed.


Print All. 

(*Theorem t27: forall w, w -> w -> w.
Proof.
  intro.
  exact (fun (H10 : w0) (H10: w0 -> w0) => H10).
Qed.

Print t27.*)



(*
Theorem pp:forall g, forall w, (forall x, x -> x) -> (x g w).
Proof.
  intros.
  unfold x.
Qed.
*)


Definition abc (p:Prop) (p:Prop) := p -> p.

Theorem prueba: forall w:Prop, forall v:Prop, abc w v.
Proof.
  intros.
  unfold not.
  intros.
  assumption.
Qed.

Print abc.

Definition ea x y := forall w, (w /\ x) /\ y -> w.

Print ea.

Theorem tt: forall w:Prop, forall p:Prop, w -> p -> ea (forall p:Prop, p /\ w \/ w) (forall w:Prop, forall p:Prop, w /\ p).
Proof.
  intros.
  unfold ea.
  intros.
  elim H1.
  intros.
  elim H2.
  intros.
  assumption.
Qed.

Definition x x y := forall w:Prop, x /\ y.

Theorem tt2 : forall x:Prop, forall y:Prop, x /\ y -> x /\ y.
Proof.
  intros.
  assumption.
Qed.

Theorem tt3 : forall w:Prop, forall y:Prop, x w y -> x w y.
Proof.
  intros.
  unfold x.
  auto.
Qed.

Print conj.
Print not.

Definition op1 := forall p:Prop, p -> p.
Definition op2 := forall q:Prop, q -> op1.
Definition op3 := fun (p : Prop) (p : Prop) => p -> op1.

Print op2.
Print op3.

Check (op3 p /\ p).

Theorem aa:p /\ p -> (op3 p).
Proof.
  intro.
  unfold op3.
  unfold op1.
  intros.
  assumption.
Qed.

Definition CBool := forall x:Set, x -> x -> x.

Definition tru : CBool := fun (x : Set) => fun (t:x) => fun (f:x) => t.

Print tru.

Theorem tru2 : CBool.
Proof.
  unfold CBool.
  intros.
  exact (H0).
Qed.

Print tru2.


Notation "A -- B" := (forall w:Prop, (A -> B -> w) -> w)  (at level 0).

Check p -- q.

Theorem kk: p -> q -> (forall w:Prop, (p -> q -> w) -> w).
Proof.
  intros.
  apply H1.
  assumption.
  assumption.
Qed.

Check kk.

Print conj.

Theorem t4 : p -> q -> (p -> (q -> c)) -> c.
Proof.
  intros.
  cut (q -> c).
  intro.
  apply H2.
  assumption.
  apply H1.
  assumption.
Qed.

Theorem gg2 : (forall x:Prop, forall y:Prop, a -> b) -> (a->b).
Proof.
  intro.
  apply H.
  exact (a0).
  exact (x).
Qed.

Print gg2.

(* El apply NO se da cuenta de la unificación. *)
Theorem gg3 : (forall x:Prop, forall y:Prop, y -> y) -> ((forall z:Prop, z -> z) -> (forall z:Prop, z -> z)).
Proof.
  intro.
  apply H.
  exact c.
  exact (H a (forall z : Prop, z -> z)).
Qed.

Print gg3.

(* El apply NO se da cuenta que NO unfica. *)
(*Theorem gg4 : (forall x:Prop, forall y:Prop, y -> y) -> (forall z:Prop, z -> z -> z).
Proof.
  intro.
  apply H.
Qed.
*)


(*Theorem gg5 : (forall x:Prop, forall y:Prop, forall z: Prop, x -> y -> y) -> (forall w:Prop, forall e:Prop, w -> e -> e).
Proof.
  intro.
  apply H.
Qed.
*)

Theorem algo : exists p: Prop, x -> p.
Proof.
  exists x.
  intros.
  assumption.
Qed.

Print algo.
Print ex_intro.
Print and.

Theorem t2 : p -> (exists x:Prop, p -> x) -> (exists y:Prop, y).
Proof.
  intros.
  elim H0.
  intros.
  exists x0.
  apply H1.
  assumption.
Qed.

Print t2.
Print ex_ind.

Definition e := ex_intro (fun p : Prop => x -> p) x (fun H : x => H).

Print e.


(* El caso donde apply es igual a assumption. *)
Theorem kk:(forall w:Prop, forall l:Prop, w) -> (forall l:Prop, forall r:Prop, l).
Proof.
  intro.
  apply H.
Qed.

Print kk.

Theorem ll:(forall w:Prop, w -> w) -> ((exists l:Prop, l -> a) ->  (exists m:Prop, m -> a)).
Proof.
  intro.
  exact (H (exists x:Prop, x -> a)).
Qed.

Print ll.


Theorem ww:a->(forall x:Prop, x) -> (exists q:Prop, a->q).
Proof.
  intros.
  exists (forall x:Prop, x).
  intro.
  apply H0.
Qed.

(*Theorem rr:(exists y:Prop, y->(forall y:Prop, y/\y)) -> x.
Proof.
  intros.
  elim H.
Qed.
*)

Theorem qq: p->(forall p:Prop, forall p:Prop, p) -> forall p:Prop, p /\ p.
Proof.
  intros; split; apply H0; assumption.
Qed.

Theorem eee:a->a\/b.
Proof.
Print or_introl.
intro.
exact (or_introl b H).
Qed.

Print eee.
Print or_introl.

Theorem eeee: a -> a\/b.
Proof.
  intro.
  apply eee.
  assumption.
Qed.

Print eeee.

Theorem e2: a /\ b -> a.
Proof.
intro.
elim H.
intros.
assumption.
Qed.


Theorem e3: a -> b -> (a /\ b) /\ (a /\ a).
Proof.
intro.
intro.
split.
split.
assumption.
assumption.
split.
assumption.
assumption.
Qed.


Theorem e4: a /\ b -> c /\ d -> d.
intro.

Theorem e5: a -> b -> (a /\ a) /\ (b->b).
Proof.
  intros.
  split.
  split.
  Focus 2.
  assumption.
  assumption.
  intro;assumption.
Qed.

Theorem e6: (a->c) /\ a-> c.
Proof.
  intro.
  elim H.
  intros.
  apply H0; assumption.
Qed.



Theorem e7:forall c:Set, (forall a:Set,a) -> forall c:Set, c->c.
Proof.
  intro.
  intro.
  intro.
  intro; assumption.
Qed.


(* RETOMANDO *)

Theorem rss : forall p:Prop, forall p:Prop, p -> p.
Proof.
  intros.
  assumption.
Qed.

Print rss.

Definition rss2 := fun (p p : Prop) (H : p) => H.

Print rss2.


Theorem retomo1 : p -> forall p:Prop, p -> p.
Proof.
  intros.
  assumption.
Qed.

Print retomo1.


Definition retomo11 := fun (H : p) (p : Prop) (H0 : p) => H0.

Print retomo11.

Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.

Theorem e11 : (forall x:U, A(x)) -> forall y:U, A(y).
Proof.
  intro.
  assumption.
Qed.

Theorem e12 : (forall x y:U, (R x y)) -> forall x y:U, (R y x).
Proof.
  intros H a b.
  exact (H b a).
Qed.


Theorem e13 : (forall x: U, ((A x)->(B x)))
                        -> (forall y:U, (A y))
                          -> (forall z:U, (B z)).
Proof.
  intros H H' a.
  exact (H a (H' a)).
Qed.


End Ejercicio1.


Section Ejercicio2.

Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.


Theorem e21 : (forall x:U, ((A x)-> ~(forall x:U, ~ (A x)))).
Proof.
  unfold not in *.
  intros a H H'.
  exact (H' a H).
Qed.

Theorem e22 : (forall x y:U, ((R x y)))-> (forall x:U, (R x x)).
Proof.
  intros H a.
  apply H.
Qed.

Theorem e23 : (forall x:U, ((P -> (A x))))
                        -> (P -> (forall x: U, (A x))).
Proof.
  intros H H' a.
  exact (H a H').
Qed.


Theorem e24 : (forall x:U, ((A x) /\ (B x)))
                        -> (forall x:U, (A x))
                          -> (forall x:U, (B x)).
Proof.
  intros H H' a.
  exact (proj2 (H a)).
Qed.

End Ejercicio2.



Section Ejercicio3.

(*Por qué se definen tantas variables? no son necesarias*)

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Hypothesis H1: forall x:U, (R x x).
Hypothesis H2: forall x y z:U, (R x y) /\ (R x z) -> (R y z).

Theorem e3 : (forall x:U, (R x x)) /\ (forall x y:U, (R x y) -> (R y x)) /\ (forall x y z:U, (R x y) /\ (R y z) -> (R x z)).
Proof.
  split; [assumption | idtac].
  split.
    intros a b H.
    exact (H2 a b a (conj H (H1 a))).

    intros a b c H.
    elim H; intros H' H''; clear H.
    assert (R b a).
      exact (H2 a b a (conj H' (H1 a))).

      exact (H2 b a c (conj H H'')).
Qed.


End Ejercicio3.



Section Ejercicio4.

(*Por qué cuando se hace: exists t, t debe estar en el contexto? t debe poder
construirse del contexto*)

Variable U : Set.
(*Variable F : Set -> Prop. (sería como F : P(U) -> Prop? si)*)
Variable A : U->Prop.
Variable R : U->U->Prop.

Theorem e41: (exists x:U, exists y:U, (R x y)) -> exists y:U, exists x:U, (R x y).
Proof.
  intro H.
  elim H.
  intros a H'.
  elim H'.
  intros b H''.
  exists b; exists a; assumption.
Qed.


Theorem e42: (forall x:U, A(x)) -> ~ exists x:U, ~ A(x).
Proof.
  unfold not in *.
  intros H H'.
  elim H'.
  intros a H''.
  exact (H'' (H a)).
Qed.

Theorem e43: (exists x:U, ~(A x)) -> ~(forall x:U, (A x)).
Proof.
  unfold not in *.
  intros H H'.
  elim H.
  intros a H''.
  exact (H'' (H' a)).
Qed.

End Ejercicio4.


Section Ejercicio5.

Variable nat      : Set.
Variable S        : nat -> nat.
Variable a b c    : nat.
Variable odd even : nat -> Prop.
Variable P Q      : nat -> Prop.
Variable f        : nat -> nat.

Theorem e51: forall x:nat, exists y:nat, (P(x)->P(y)).
Proof.
  intro a1.
  exists a1.
  intro; assumption.
Qed.

Theorem e52: exists x:nat, (P x)
                            -> (forall y:nat, (P y)->(Q y))
                               -> (exists z:nat, (Q z)).
Proof.
  exists a.
  intros H H'.
  exists a.
  exact (H' a H).
Qed.


Theorem e53: even(a) -> (forall x:nat, (even(x)->odd (S(x)))) -> exists y: nat, odd(y).
Proof.
  intros H H'.
  exists (S a).
  exact (H' a H).
Qed.


Theorem e54: (forall x:nat, P(x) /\ odd(x) ->even(f(x)))
                            -> (forall x:nat, even(x)->odd(S(x)))
                            -> even(a)
                            -> P(S(a))
                            -> exists z:nat, even(f(z)).
Proof.
  intros H H' H'' H'''.
  assert (odd (S a)); [exact (H' a H'') | idtac].
  exists (S a).
  exact (H (S a) (conj H''' H0)).
Qed.

End Ejercicio5.



Section Ejercicio6.

Variable nat : Set.
Variable S   : nat -> nat.
Variable le  : nat -> nat -> Prop.
Variable f   : nat -> nat.
Variable P   : nat -> Prop.

Axiom le_n: forall n:nat, (le n n).
Axiom le_S: forall n m:nat, (le n m) -> (le n (S m)).
Axiom monoticity: forall n m:nat, (le n m) -> (le (f n) (f m)).


Lemma le_x_Sx: forall x:nat, (le x (S x)).
Proof.
  intro a.
  exact ((le_S a a) (le_n a)).
Qed.

Lemma le_x_SSx: forall x:nat, (le x (S (S x))).
Proof.
  intro a.
  exact((le_S a (S a)) ((le_S a a) (le_n a))).
Qed.

Theorem T1_e2_1: forall a:nat, exists b:nat, (le (f a) b).
Proof.
  intro a.
  exists (f a).
  exact (monoticity a a (le_n a)).
Qed.

Theorem T1_e2_2: forall a:nat, exists b:nat, (le (f a) b).
Proof.
  intro a.
  exists (f(S a)).
  exact (monoticity a (S a) (le_S a a (le_n a))).
Qed.

Theorem T1_e2_3: forall a:nat, exists b:nat, (le (f a) b).
Proof.
  intro a.
  exists (f(S (S a))).
  exact (monoticity a (S (S a)) (le_S a (S a) (le_S a a (le_n a)))).
Qed.

(*Se puede usar repeat adentro de un exact? No, solo pueden ir términos*)

Theorem T1_e2a: forall a:nat, exists b:nat, (le (f a) b).
Proof.
  intro a.
  exists ((S (S (S (S (S (f a))))))).
  repeat (apply le_S).
  exact (monoticity a a (le_n a)).
Qed.

Theorem T1_e2b: forall a:nat, exists b:nat, (le (f a) b).
Proof.
  intro a.
  exists ((S (S (S (S (S (f a))))))).
  do 5 (apply le_S).
  exact (monoticity a a (le_n a)).
Qed.

End Ejercicio6.



Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

Theorem e71: (forall x:U, ((A x) /\ (B x)))
                       -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
  intro H; split; intro a; [exact (proj1 (H a)) | exact (proj2 (H a))].
Qed.

Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof.
  intro H; elim H; intros a H'; elim H'; intro H''; [left | right]; exists a; assumption.
Qed.

End Ejercicio7.


Section Ejercicio8.

Variable U : Set.
Variable R : U -> U -> Prop.
Variable T V : U -> Prop.

Theorem e81: (exists y:U, forall x:U, R x y) -> (forall x:U, exists y:U, R x y).
Proof.
  intros H a.
  elim H.
  intros b H'.
  exists b.
  exact (H' a).
Qed.

Theorem T282: (exists y:U, True) /\ (forall x:U, (T x) \/ (V x)) -> 
              (exists z:U, (T z)) \/ (exists w:U, (V w)).
Proof.
  intros H.
  elim H; intros H' H''; clear H.
  elim H'.
  intros a H'''.
  elim (H'' a); intros; [left | right]; exists a; assumption.
Qed.

(*La condición (exists y:U, True) es necesaria, pues para probar la disyunción
de existenciales es necesario dar un testigo, un elemento de U, y solo puede
obtenerse mediante (exists y:U, True)*)

End Ejercicio8.


Section Ejercicio9.
Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

Lemma not_ex_not_forall: (~exists x :U, ~A x) -> (forall x:U, A x).
Proof.
  unfold not in *.
  intros H a.
  assert (((A a) -> False) -> False).
    intro H'.
    apply H.
    exists a.
    assumption.

    apply (NNPP (A a)); assumption.
Qed.

Lemma not_forall_ex_not: (~forall x :U, A x) -> (exists x:U,  ~A x).
Proof.
  unfold not in *.
  intro H.
  elim (classic (exists x : U, A x -> False)); intro H'; [assumption | idtac].
  assert (forall x:U, A x); [apply (not_ex_not_forall) | absurd (forall x:U, A x)]; assumption.
Qed.

End Ejercicio9.



Section Sec_Peano.

Variable nat : Set. (*Pisa el nat de COQ*)
Variable  O  : nat.
Variable  S  : nat -> nat.

Axiom disc   : forall n:nat, ~O=(S n).
Axiom inj    : forall n m:nat, (S n)=(S m) -> n=m.

Variable sum prod : nat->nat->nat.
Axiom sum0   : forall n :nat, (sum n O)=n.
Axiom sumS   : forall n m :nat, (sum n (S m))=(S (sum n m)).
Axiom prod0  : forall n :nat, (prod n O)=O.
Axiom prodS  : forall n m :nat, (prod n (S m))=(sum n (prod n m)).


Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
  assert (sum (S O) (S O)= S (sum (S O) O)); [exact (sumS (S O) O) | idtac].
  assert (sum (S O) O = S O); [exact (sum0 (S O)) | idtac].
  rewrite -> H0 in H; assumption.
Qed.

Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
  unfold not in *.
  intros a H.
  elim H; intros H' H''; clear H.
  elim H''; intros b H'''; rewrite <- H' in H'''.
  absurd (O = S b); [exact (disc b) | assumption].
Qed.

Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
  intro a.
  assert ((prod a (S O))=(sum a (prod a O))); [exact (prodS a O) | idtac].
  assert ((prod a O)=O); [exact (prod0 a) | idtac].
  rewrite -> H0 in H.
  assert((sum a O)=a) ; [exact (sum0 a) | idtac].
  rewrite -> H1 in H.
  assumption.
Qed.

(*Lema auxiliar, para probar "diff"*)
Lemma L1: forall n m:nat, n<>m -> m<>n.
Proof.
  unfold not in *.
  intros a b H H'.
  apply H.
  rewrite -> H'; reflexivity.
Qed.

(*Check not_eq_sym. no lo puedo usar?*)

Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
  unfold not in *.
  intros a H.
  assert (S a = O); [apply (inj (S a) O); assumption | idtac].
  absurd (S a = O); [apply (L1 O (S a)); exact (disc a) | assumption].
Qed.

(*Que diferencia hay entre lema y teorema? ninguna*)

(*No se puede demostrar el princio de inducción? No*)

Axiom inducción: forall P:nat->Prop, (P(O) /\ (forall n:nat, P(n) -> P(S n))) -> forall n:nat, P(n).


(*Ejercicio 2.11*)
Variable le : nat->nat->Prop.
Axiom leinv: forall n m:nat, (le n m) -> n=O \/
      (exists p:nat, (exists q:nat, n=(S p)/\ m=(S q) /\ (le p q))).

Lemma notle_s_o: forall n:nat, ~(le (S n) O).
Proof.
  unfold not in *.
  intros a H.
  assert ((S a) = O \/ (exists p:nat, (exists q:nat, S a =(S p)/\ O=(S q) /\ (le p q)))); [apply (leinv (S a) O); assumption | idtac].
  elim H0; intro H'; [apply(disc a); symmetry; assumption | idtac]; clear H0.
  elim H'; intros b H''; elim H''; intros c H'''; clear H' H''.
  elim H'''; intros H1 H2; elim H2; intros H3 H4; clear H''' H2.
  apply(disc c); assumption.
Qed.

End Sec_Peano.

(*Si hacemos las secciones "Ejercicio10" y "Ejercicio11", que traía originalmente la plantilla,
se puede probar el ejercicio 11 con los naturales de Coq, usando los teoremas de los naturales
que trae Coq*)