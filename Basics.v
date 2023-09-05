(* 定义Type类型 *)
Inductive day : Type := 
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* 定义函数 *)
Definition next_weekday (d:day) : day :=
  match d with 
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday 
    | friday => saturday 
    | saturday => sunday 
    | sunday => monday 
    end.

(* Compute 指令来计算 *)
Compute (next_weekday friday). 

Compute (next_weekday (next_weekday saturday)).

(* 定义断言 *)
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = monday.

(* 验证断言 *)
Proof. simpl. reflexivity. Qed.

(* 定义数据类型 *)
(* Inductive bool : Type :=  
  | true
  | false.
 *)
(* 定义函数,函数的作用为bool变量取反 *)
Definition negb (b:bool) : bool :=
  match b with 
    | true => false
    | false => true
  end.

(* 定义函数，函数的作用为对两个bool变量进行与操作 *)
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with 
    | true => b2
    | false => false
  end.

(* 定义函数，函数的作用为对两个bool变量进行或操作 *)
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with 
    | true => true
    | false => b2
  end.

(* 真值表 *)
Example test_orb1: (orb  true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb  false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(* 引入Notation指令，引入中缀符号 *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* coq的条件表达式 *)
Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Definition andb' (b1:bool) (b2:bool) : bool := 
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool := 
  if b1 then true
  else b2.


(* Exercise 1 *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  if (andb b1 b2) then false
  else true.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise 2 *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) :=
  if (b1 && b2 && b3) then true
  else false.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.


(* Checkout检查表达式类型 *)
Check true.

Check true : bool.
Check (negb true) : bool.

(* 检查函数类型 *)

Check negb : bool -> bool.
Check negb.

Check andb.

Inductive rgb : Type :=
  | red 
  | green
  | blue.

Inductive color : Type := 
  | black
  | white
  | primary (p : rgb).
(* red、green、blue、black、white以及primary(还有true、false、monday等)这样的原子标识符叫做“构造子” *)

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.



Module Playground.
  Definition b : rgb := blue.
End Playground.
Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.


(* 定义模块,模块的开始 *)
Module tuple.

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3:bit).

(* 检查类型 *)
Check (bits B1 B0 B1 B0).

Definition all_zero (nb : nybble) : bool :=
  match nb with 
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).

Compute (all_zero (bits B0 B0 B0 B0)).

End tuple. 
(* 模块的结束 *)

(* 使用模块进行计算 *)
Compute (tuple.all_zero (tuple.bits tuple.B0 tuple.B0 tuple.B0 tuple.B0)).


(* Module NatPlayground. *) 


Check (S (S (S (S 0)))).


Definition minustwo (n : nat) : nat := 
  match n with 
    | 0 => 0
    | S 0 => 0
    | S (S n') => n'
  end.

Compute (minustwo 4).

(* 数字是偶数还是奇数 *)
(* 注释快捷键 ctrl+D *)
Fixpoint evenb (n:nat) : bool :=
  match n with 
    | 0 => true
    | S 0 => false
    | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool :=
  negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed. 
Example test_oddb2:oddb 4 = false.
Proof. simpl. reflexivity. Qed.
(* 单步运行发现simpl未起到作用，后续分析原因 *)

(* 大写的S表示构造子“后继” *)

(* End NatPlayground. *)


(* Module NatPlayground2. *)

Fixpoint plus (n : nat) (m : nat) : nat :=
 match n with 
  | 0 => m
  | S n' => S (plus n' m)
 end.

Compute (oddb 1).
Compute (plus 3 2).

(* plus 3 2 执行过程
i.e plus 3 2
=> plus (S (S (S 0))) (S (S 0)) 自然数的表示方式
=> S ((plus S (S 0)) (S (S 0))) 根据第二个match子句
=> S (S (plus (S 0) (S (S 0)))) 根据第二个match子句
=> S (S (S (plus 0 (S (S 0))))) 根据第二个match子句
=> S (S (S (S (S 0)))) 根据第一个match子句
=> 5
*)

Fixpoint mult (n m : nat) : nat :=
  match n with 
    | 0 => 0
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed. 

Fixpoint minus (n m:nat) : nat :=
  match n, m with 
    | 0, _ => 0
    | S _, 0 => n
    | S n', S m' => minus n' m'
  end.

Compute(minus 9 7).

Compute(minus 6 7).

(* base^power *)
Fixpoint exp (base power : nat) : nat :=
  match power with 
    | 0 => S 0
    | S p => mult base (exp base p)
  end.

(* 计算2的3次方 *)
Compute (exp 2 3).

(* Exercise n的介乘 *)
Fixpoint factorial (n:nat) :=
  match n with  
    |0 => 1
    | S p => mult n (factorial(p))
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: factorial 5 = (mult 10 12).
Proof. simpl. reflexivity. Qed.

(* Notation "x + y" := (plus x y). *)

(* Notation "x - y" := (minus x y). *)

(* Notation " x * y" := (mult x y). *)

Check ((0 + 1) + 1).

(* End NatPlayground2. *)

Fixpoint eqb (n m : nat) : bool := 
  match n with 
    | 0 => match m with 
            | 0 => true
            | S m' => false
           end
    | S n' => match m with 
                | 0 => false 
                | S m' => eqb n' m'
              end
  end.

Fixpoint leb (n m : nat) : bool := 
  match n with 
    | 0 => true
    | S n' => 
            match m with 
              | 0 => false
              | S m' => leb n' m'
            end
   end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise ltb *)
Definition ltb (n m : nat) : bool :=
  if (m <=? n) then false
  else true.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.


(* 基于化简的证明 *)
Theorem plus_0_n: forall n: nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.


Theorem plus_0_n': forall n: nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity. Qed.

(* 基于改写的证明 *)

Theorem plus_id_example: forall n m: nat, 
  n = m -> 
  n + n = m + m.

(* Proof.
  intros n m. simpl. reflexivity. Qed. *)

Proof. 
  (* 将两个量词移动到上下文中： *)
  intros n m.
  (* 将前提移到上下文中： *)
  intros H.
  (* 用前提改写目标：
  -> 把前提等式H的左边替换成右边 *)
  rewrite -> H.
  reflexivity. Qed.

(* Proof. 
  (* 将两个量词移动到上下文中： *)
  intros n m.
  (* 将前提移到上下文中： *)
  intros H.
  (* 用前提改写目标：
  <- 把前提等式H的右边替换成左边 *)
  rewrite <- H.
  reflexivity. Qed. *)


Theorem plus_id_exercise : forall n m o : nat, 
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H0.
  intros H1.
  rewrite -> H0.
  rewrite -> H1.
  simpl. reflexivity. Qed.

(* intros H0:将前提条件n=m移到上下文中 
intros H1:将前提条件m=o移到上下文中
rewrite -> H0将等式n + m = m + o.中n换成m，即m + m = m + o
rewrite -> H1将等式m + m = m + o.中m换成o，即o + o = o + o 
-> : 表示将等式中的全部符号，使用前提条件左边替换为右边的规则。
<- : 表示将等式中的全部符号，使用前提条件
*)

Check mult_n_O.

Check mult_n_Sm.


Theorem mult_n_0_m_0 : forall n m : nat,
  (n * 0) + (m * 0) = 0.
Proof.
  intros n m.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem mult_n_1 : forall n : nat,
  n * 1 = n.
Proof.
  intros n.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  simpl. reflexivity. Qed.



(* 利用分类讨论来证明 *)
Theorem plus_neq_0 : forall n : nat, 
  (n + 1) =? 0 = false.
Proof. 
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.
(* destruct策略会生成两个子目标，as [| n'] 这种标注被称为“引入模式”。 *)

Theorem negb_involutive : forall b : bool, 
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof. 
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.
(* 首先将b分成两个子目标（true和false）；然后再将c分为两个子目标true和false。每一对reflexivity调用和紧邻其上的destruct执行后生成
的子目标对应 *)
Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof. 
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.
 
Theorem andb3_exchange : forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.  
      - reflexivity.
      - reflexivity. }
Qed.


Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'' : forall b c, andb b c = andb c b.
Proof. 
  intros [] [].
  - reflexivity.
  - reflexivity. 
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn:B.
    - destruct c eqn:C.
      + simpl.
        reflexivity.
      + simpl.
        intros H.
        rewrite -> H.
        reflexivity. 
    - destruct c eqn:C.
      + simpl. 
      reflexivity.
      + simpl. intros H.
      rewrite -> H.
      reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat, 
  0 =? (n+1) = false.
 Proof. 
    intros [|n].
    - reflexivity.
    - reflexivity.
  Qed.


(* 符号优先级和结合性 *)
(* Notation "x + y" := (plus x y) 
                      (at level 50, left associativity)
                      : nat_scope. *)
(* Notation "x * y" := (mult x y) 
                      (at level 40, left associativity)
                      : nat_scope. *)
(* Coq使用0到100的优先级，同时支持“左结合”、“右结合”和“不结合”三种结合性。 *)










