Require Import Coq.Reals.Reals.
Require Import List.

From Coq Require Import Vector.
Require Import Coq.Vectors.Vector.
Definition vector := Vector.t. 

Import ListNotations.

(* тип совместной СЛАУ из трехдиагональной матрицы, ее (размера-1) и правой части*)
(* n - число на 1 меньшее размера матрицы *)
(* c - наддиагональные элементы матрицы *)
(* b - диагональные элементы матрицы *)
(* a - поддиагональные элементы матрицы *)
(* f - правая часть уравнения *)



(* TODO научиться считать ранг матрицы *)
Definition rank (n : nat) : nat := S n.


Record TriDiagSys := {
  n : nat;
  c : vector R n;
  b : vector R (S n);
  a : vector R n;
  f : vector R (S n);

  is_consistent :=
    rank n = rank n /\ rank n = n; (* TODO сформулировать критерий Кронекера-Капелли*)

  proof_of_consistency : is_consistent
}.


Definition get_n (sys : TriDiagSys) : nat :=
  n sys.

Definition get_c (sys : TriDiagSys) : vector R (n sys) :=
  c sys.

Definition get_b (sys : TriDiagSys) : vector R (S (n sys)) :=
  b sys.

Definition get_a (sys : TriDiagSys) : vector R (n sys) :=
  a sys.

Definition get_f (sys : TriDiagSys) : vector R (S (n sys)) :=
  f sys.



Definition toVec (l : list R) : vector R (length l) :=
  Vector.of_list l.

Fixpoint toList {A : Type} {n : nat} (v : Vector.t A n) : list A :=
match v with
| nil _ => []
| cons _ h _ t => h :: toList t
end.

Fixpoint reverse_list (l : list R) : list R :=
  match l with
  | [] => []
  | h :: t => reverse_list t ++ h :: []
  end.

Section v.
Import VectorNotations.

Fixpoint mkVector (n : nat) (value : R) : Vector.t R n :=
  match n with
    | O => Vector.nil R
    | S p => value :: (mkVector p value)
  end.

End v.



(* Operations on elements of type R *)
Definition sub (a b : R) : R := Rminus a b. (* Subtraction *)
Definition mul (a b : R) : R := Rmult a b.  (* Multiplication *)
Definition div (a b : R) : R := Rdiv a b.    (* Division *)
Definition one : R := R1.                    (* Identity element for multiplication *)
Definition zero : R := R0.                   (* Identity element for addition *)
Definition add (a b : R) : R := Rplus a b.    (* Addition *)

(* Функция для вычисления denominator *)
(* denominator = b[i] + a[i]*alpha[i]; *)
Definition denominator (a alpha b : R) : R :=
  add (mul a alpha) b.

(* Функция для вычисления a_i *)
(* alpha[i+1] = -c[i]  / denominator; i>=0 *)
Definition alpha_i (c a alpha b : R) : R :=
  div (sub zero c) (denominator a alpha b).

(* Функция для вычисления a_1 *)
(* alpha[0] = -c[0] / b[0]; *)
Definition alpha_1 (c b : R) : R :=
  div (sub zero c) b.
  
(* Функция для вычисления b_i *)
(* beta[i+1] = (f[i] - a[i]*beta[i]) / denominator; i>=0*)
Definition beta_i (a b f alpha beta : R) : R :=
  div (sub f (mul a beta)) (denominator a alpha b).

(* Функция для вычисления b_1 *)
(* beta[0] = f[0]  / b[0]; *)
Definition beta_1 (f b : R) : R :=
  div f b.

(* Функция для вычисления x_j, j<n*)
(*  *)
Definition x_j (x alpha beta : R) : R :=
  add (mul alpha x) beta.

(* Функция для вычисления x_n*)
(*  *)
Definition x_n (a b f alpha beta  : R) : R :=
  div (sub f (mul a beta)) (add b (mul a alpha)).


Fixpoint matrix_mul' (n : nat) (a b c x : list R) (x' : R) : list R := 
  match n with
  | 0 => 
    match a, b, x with
    | [], [], [] => []
    | [], _, _ => []
    | _, [], _ => []
    | _, _, [] => []
    | hda::tla, hdb::tlb, hdx::tlx =>
      let f_1 := mul hda x' in
      let f_2 := mul hdx hdb in
      [(add f_1 f_2)]
    end
  | S k =>
    match a, b, c, x with
    | [],[],[], [] =>  []
    | [], _, _, _ => []
    | _, [], _, _ => []
    | _, _, [], _ => []
    | _, _, _, [] => []
    | hda::tla, hdb::tlb, hdc::tlc, hdx::tlx =>
      let f_1 := mul hda x' in
      let f_2 := mul hdx hdb in
      match tlx with
      | [] => []
      | hdx'::tlx' =>
        let f_3 := mul hdc hdx' in
        let f_i := add f_1 (add f_2 f_3) in
        (f_i) :: matrix_mul' k tla tlb tlc tlx f_i
      end
    end

    end.
    


Definition matrix_mul (SLE : TriDiagSys) (x : list R) : list R :=
  let n := get_n SLE in
  let a := toList (get_a SLE) in
  let b := toList (get_b SLE) in
  let c := toList (get_c SLE) in
 
  match n with
  | 0 => (* матрица 1 на 1 *)
    match b, x with
    | [],[] => []
    | [], _ => []
    | _,[] => []
    | hdb::tlb, hdx::tlx =>
      let f_1 := mul hdb hdx in
      [f_1]
    end
  | S k =>
    match a, b, c, x with
    | [],[],[], [] =>  [] 
    | [], _, _, _ => []
    | _, [], _, _ => []
    | _, _, [], _ => []
    | _, _, _, [] => []
    | hda::tla, hdb::tlb, hdc::tlc, hdx::tlx =>
      match x with
      | [] => []
      | hdx'::tlx' =>
        let x_1 := (add (mul hdb hdx) (mul hdc hdx')) in
        x_1 :: (matrix_mul' k a tlb tlc tlx x_1)
      end
    end
  end.



Fixpoint find_alpha' (b c a : list R) (alpha : R) : list R :=
  match b, c, a with
  | [],[],[] =>  []
  | [], _, _ => []
  | _, [], _ => []
  | _, _, [] => []
  | hdb::tlb, hdc::tlc, hda::tla =>
    let alpha_i := alpha_i hdc hda alpha hdb in
    alpha_i :: (find_alpha' tlb tlc tla alpha_i)
  end.


Definition find_alpha (SLE : TriDiagSys) : (list R) :=
  let n := get_n SLE in
  let a := toList (get_a SLE) in
  let b := toList (get_b SLE) in
  let c := toList (get_c SLE) in
  let f := toList (get_f SLE) in

  match c, b with
    | [], [] => [] 
    | _, [] => [] 
    | [], _ => []
    | hdc::tlc, hdb::tlb =>
      let alpha_1 := alpha_1 (hdc) (hdb) in
      alpha_1 :: (find_alpha' b c a alpha_1)
    end.






Fixpoint find_beta' (a b f alpha : list R) (beta : R) : list R :=
  match a, b, f, alpha with
  | [],[],[], [] =>  [] 
  | [], _, _, _ => [] 
  | _, [], _, _ => [] 
  | _, _, [], _ => [] 
  | _, _, _, [] => [] 
  | hda::tla, hdb::tlb, hdf::tlf, hd_alpha::tl_alpha =>
    let beta_i := beta_i hda hdb hdf hd_alpha beta in
    beta_i :: (find_beta' tla tlb tlf tl_alpha beta_i)
  end.


Definition find_beta (SLE : TriDiagSys) (alpha : list R) : (list R) :=
  let n := get_n SLE in
  let a := toList (get_a SLE) in
  let b := toList (get_b SLE) in
  let c := toList (get_c SLE) in
  let f := toList (get_f SLE) in

  match b, f with
    | [], [] => [] 
    | _, [] => [] 
    | [], _ => [] 
    | hdb::tlb, hdf::tlf =>
      let beta_1 := beta_1 hdf hdb in
      beta_1 :: (find_beta' a b f alpha beta_1)
    end.




Fixpoint find_x' (alpha beta : list R) (x : R) : list R :=
  match alpha, beta with
  | [], [] => []
  | [], _ => []
  | _, [] => []
  | hd_alpha::tl_alpha, hd_beta::tl_beta => 
    let x_j := x_j x hd_alpha hd_beta in 
    x_j :: (find_x' tl_alpha tl_beta x_j)
  end.


Definition find_x (SLE : TriDiagSys) (alpha beta : list R): (list R) :=
  let n := get_n SLE in
  let a := toList (get_a SLE) in
  let b := toList (get_b SLE) in
  let c := toList (get_c SLE) in
  let f := toList (get_f SLE) in

  match a, b, f, alpha, beta with
  | [],[],[],[],[] => []
  | [], _, _, _, _ => [] 
  | _, [], _, _, _ => [] 
  | _, _, [], _, _ => [] 
  | _, _, _, [], _ => [] 
  | _, _, _, _, [] => [] 
  | hda::tla, hdb::tlb, hdf::tlf, hd_alpha::tl_alpha, hd_beta::tl_beta =>
    let x_n := x_n hda hdb hdf hd_alpha hd_beta in
    x_n :: (find_x' alpha beta x_n)
  end.  



Definition solution (SLE : TriDiagSys) : (list R) :=
  match (S (get_n SLE)) with
  | 0 => []
  | S 0 =>
    let b := toList (get_b SLE)  in
    let f := toList (get_f SLE) in
    match b, f with
    | [], _ => []
    | _, [] => []
    | hdb::tlb, hdf::tlf =>
      let f_0 := div hdf hdb in
      [f_0]
    end
  | S _ => 
    let alpha := find_alpha SLE in
    let beta := find_beta SLE alpha in
    reverse_list(find_x SLE alpha beta)
  end.






Theorem correct : forall (A : TriDiagSys),
  matrix_mul A (solution A) = toList(b A).
Proof.
  (* Здесь должна быть реализация доказательства *)
Admitted.