Require Import Coq.Reals.Reals.

From Coq Require Import Vector.
Require Import Coq.Vectors.Vector.
Definition vector := Vector.t. 

Import VectorNotations.

Record TriDiagSys := {
  n : nat;
  c : vector R n;
  b : vector R (S n);
  a : vector R n;
  f : vector R (S n);
}.

Definition x_2 (SLE : TriDiagSys) : R :=
  let n := n SLE in
  let b := b SLE in
  let t := fun n => vector R (S n) in
  let T := sigT t in
  match (existT t n b): T
  with  
  | existT _ 0 b => hd b (*Длина b = (S n), => там есть хотя бы 1 элемент*)
  | existT _ (S k) b =>
    let b_1 := hd b in
    let tlb := tl b in (*n := S k => длина b - S(S k) то есть хотя бы 2 и tl b != nil*)
    let b_2 := hd tlb in
    b_2
             (* Error:
                In environment
                SLE : TriDiagSys
                n := n SLE : nat
                b := b SLE : vector R (S (demo.n SLE))
                k : nat
                b_1 := hd b : R
                tlb := tl b : t R (demo.n SLE)
                The term "tlb" has type "t R (demo.n SLE)" while it is expected to have type
                "t R (S ?n)". *)
  end.
