/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe08_Metaprogramming_Demo
import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe 演示 10：霍尔逻辑

我们回顾第二种指定编程语言语义的方法：霍尔逻辑。如果操作语义对应于一个理想化的解释器，那么**霍尔逻辑**（也称为**公理语义**）则对应于一个验证器。霍尔逻辑特别适用于对具体程序进行推理。 -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace LoVe


/- ## Hoare 三元组

Hoare 逻辑的基本判断通常称为 **Hoare 三元组**。它们的形式为：

    `{P} S {Q}`

其中 `S` 是一个语句，`P` 和 `Q`（称为 **前置条件** 和 **后置条件**）是关于状态变量的逻辑公式。

**预期含义**：

    如果在执行 `S` 之前 `P` 成立，并且执行正常终止，那么在终止时 `Q` 成立。

这是一个 **部分正确性** 的陈述：如果程序正常终止（即没有运行时错误、没有无限循环或发散），则程序是正确的。

以下所有 Hoare 三元组都是有效的（符合预期含义）：

    `{True} b := 4 {b = 4}`
    `{a = 2} b := 2 * a {a = 2 ∧ b = 4}`
    `{b ≥ 5} b := b + 1 {b ≥ 6}`
    `{False} skip {b = 100}`
    `{True} while i ≠ 100 do i := i + 1 {i = 100}`

## Hoare 规则

以下是用于推理 WHILE 程序的完整规则集：

    ———————————— Skip
    {P} skip {P}

    ——————————————————— Assign
    {Q[a/x]} x := a {Q}

    {P} S {R}   {R} S' {Q}
    —————————————————————— Seq
    {P} S; S' {Q}

    {P ∧ B} S {Q}   {P ∧ ¬B} S' {Q}
    ——————————————————————————————— If
    {P} if B then S else S' {Q}

    {P ∧ B} S {P}
    ————————————————————————— While
    {P} while B do S {P ∧ ¬B}

    P' → P   {P} S {Q}   Q → Q'
    ——————————————————————————— Conseq
    {P'} S {Q'}

`Q[a/x]` 表示将 `Q` 中的 `x` 替换为 `a`。

在 `While` 规则中，`P` 被称为 **不变式**。

除了 `Conseq` 之外，这些规则都是语法驱动的：通过查看程序，我们可以立即知道应该应用哪条规则。

**示例推导**：

    —————————————————————— Assign   —————————————————————— Assign
    {a = 2} b := a {b = 2}          {b = 2} c := b {c = 2}
    —————————————————————————————————————————————————————— Seq
    {a = 2} b := a; c := b {c = 2}


                     —————————————————————— Assign
    x > 10 → x > 5   {x > 5} y := x {y > 5}   y > 5 → y > 0
    ——————————————————————————————————————————————————————— Conseq
    {x > 10} y := x {y > 0}

可以通过标准规则证明各种 **派生规则** 的正确性。例如，我们可以为 `skip`、`:=` 和 `while` 推导出双向规则：

    P → Q
    ———————————— Skip'
    {P} skip {Q}

    P → Q[a/x]
    —————————————— Assign'
    {P} x := a {Q}

    {P ∧ B} S {P}   P ∧ ¬B → Q
    —————————————————————————— While'
    {P} while B do S {Q}

## Hoare 逻辑的语义方法

我们可以在 Lean 中 **语义地** 定义 Hoare 三元组。

我们将使用状态上的谓词（`State → Prop`）来表示前置条件和后置条件，遵循浅嵌入风格。 -/

def PartialHoare (P : State → Prop) (S : Stmt)
    (Q : State → Prop) : Prop :=
  ∀s t, P s → (S, s) ⟹ t → Q t

macro "{*" P:term " *} " "(" S:term ")" " {* " Q:term " *}" : term =>
  `(PartialHoare $P $S $Q)

namespace PartialHoare

theorem skip_intro {P} :
    {* P *} (Stmt.skip) {* P *} :=
  by
    intro s t hs hst
    cases hst
    assumption

theorem assign_intro (P) {x a} :
    {* fun s ↦ P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *} :=
  by
    intro s t P' hst
    cases hst with
    | assign => assumption

theorem seq_intro {P Q R S T} (hS : {* P *} (S) {* Q *})
      (hT : {* Q *} (T) {* R *}) :
    {* P *} (S; T) {* R *} :=
  by
    intro s t hs hst
    cases hst with
    | seq _ _ _ u d hS' hT' =>
      apply hT
      { apply hS
        { exact hs }
        { assumption } }
      { assumption }

theorem if_intro {B P Q S T}
      (hS : {* fun s ↦ P s ∧ B s *} (S) {* Q *})
      (hT : {* fun s ↦ P s ∧ ¬ B s *} (T) {* Q *}) :
    {* P *} (Stmt.ifThenElse B S T) {* Q *} :=
  by
    intro s t hs hst
    cases hst with
    | if_true _ _ _ _ _ hB hS' =>
      apply hS
      exact And.intro hs hB
      assumption
    | if_false _ _ _ _ _ hB hT' =>
      apply hT
      exact And.intro hs hB
      assumption

theorem while_intro (P) {B S}
      (h : {* fun s ↦ P s ∧ B s *} (S) {* P *}) :
    {* P *} (Stmt.whileDo B S) {* fun s ↦ P s ∧ ¬ B s *} :=
  by
    intro s t hs hst
    generalize ws_eq : (Stmt.whileDo B S, s) = Ss
    rw [ws_eq] at hst
    induction hst generalizing s with
    | skip s'                       => cases ws_eq
    | assign x a s'                 => cases ws_eq
    | seq S T s' t' u hS hT ih      => cases ws_eq
    | if_true B S T s' t' hB hS ih  => cases ws_eq
    | if_false B S T s' t' hB hT ih => cases ws_eq
    | while_true B' S' s' t' u hB' hS hw ih_hS ih_hw =>
      cases ws_eq
      apply ih_hw
      { apply h
        { apply And.intro <;>
            assumption }
        { exact hS } }
      { rfl }
    | while_false B' S' s' hB'      =>
      cases ws_eq
      aesop

theorem consequence {P P' Q Q' S}
      (h : {* P *} (S) {* Q *}) (hp : ∀s, P' s → P s)
      (hq : ∀s, Q s → Q' s) :
    {* P' *} (S) {* Q' *} :=
  fix s t : State
  assume hs : P' s
  assume hst : (S, s) ⟹ t
  show Q' t from
    hq _ (h s t (hp s hs) hst)

theorem consequence_left (P') {P Q S}
      (h : {* P *} (S) {* Q *}) (hp : ∀s, P' s → P s) :
    {* P' *} (S) {* Q *} :=
  consequence h hp (by aesop)

theorem consequence_right (Q) {Q' P S}
      (h : {* P *} (S) {* Q *}) (hq : ∀s, Q s → Q' s) :
    {* P *} (S) {* Q' *} :=
  consequence h (by aesop) hq

theorem skip_intro' {P Q} (h : ∀s, P s → Q s) :
    {* P *} (Stmt.skip) {* Q *} :=
  consequence skip_intro h (by aesop)

theorem assign_intro' {P Q x a}
      (h : ∀s, P s → Q (s[x ↦ a s])):
    {* P *} (Stmt.assign x a) {* Q *} :=
  consequence (assign_intro Q) h (by aesop)

theorem seq_intro' {P Q R S T} (hT : {* Q *} (T) {* R *})
      (hS : {* P *} (S) {* Q *}) :
    {* P *} (S; T) {* R *} :=
  seq_intro hS hT

theorem while_intro' {B P Q S} (I)
      (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
      (hP : ∀s, P s → I s)
      (hQ : ∀s, ¬ B s → I s → Q s) :
    {* P *} (Stmt.whileDo B S) {* Q *} :=
  consequence (while_intro I hS) hP (by aesop)

theorem assign_intro_forward (P) {x a} :
    {* P *}
    (Stmt.assign x a)
    {* fun s ↦ ∃n₀, P (s[x ↦ n₀])
       ∧ s x = a (s[x ↦ n₀]) *} :=
  by
    apply assign_intro'
    intro s hP
    apply Exists.intro (s x)
    simp [*]

theorem assign_intro_backward (Q) {x a} :
    {* fun s ↦ ∃n', Q (s[x ↦ n']) ∧ n' = a s *}
    (Stmt.assign x a)
    {* Q *} :=
  by
    apply assign_intro'
    intro s hP
    cases hP with
    | intro n' hQ => aesop

end PartialHoare


/- ## 第一个程序：交换两个变量 -/

def SWAP : Stmt :=
  Stmt.assign "t" (fun s ↦ s "a");
  Stmt.assign "a" (fun s ↦ s "b");
  Stmt.assign "b" (fun s ↦ s "t")

theorem SWAP_correct (a₀ b₀ : ℕ) :
    {* fun s ↦ s "a" = a₀ ∧ s "b" = b₀ *}
    (SWAP)
    {* fun s ↦ s "a" = b₀ ∧ s "b" = a₀ *} :=
  by
    apply PartialHoare.seq_intro'
    apply PartialHoare.seq_intro'
    apply PartialHoare.assign_intro
    apply PartialHoare.assign_intro
    apply PartialHoare.assign_intro'
    aesop


/- ## 第二个程序：两数相加 -/

def ADD : Stmt :=
  Stmt.whileDo (fun s ↦ s "n" ≠ 0)
    (Stmt.assign "n" (fun s ↦ s "n" - 1);
     Stmt.assign "m" (fun s ↦ s "m" + 1))

theorem ADD_correct (n₀ m₀ : ℕ) :
    {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
    (ADD)
    {* fun s ↦ s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
  PartialHoare.while_intro' (fun s ↦ s "n" + s "m" = n₀ + m₀)
    (by
      apply PartialHoare.seq_intro'
      { apply PartialHoare.assign_intro }
      { apply PartialHoare.assign_intro'
        aesop })
    (by aesop)
    (by aesop)

/- 我们是如何得出这个不变式的？不变式必须满足以下条件：

1. 在进入循环之前为真；
2. 如果在迭代之前为真，则在每次迭代后仍然为真；
3. 足够强以蕴含所需的循环后条件。

不变式 `True` 满足条件1和2，但通常不满足条件3。类似地，`False` 满足条件2和3，但通常不满足条件1。合适的不变式通常具有以下形式：

__已完成的工作__ + __剩余的工作__ = __期望的结果__

其中 `+` 是某种合适的运算符。当我们进入循环时，__已完成的工作__ 通常为 `0`。当我们退出循环时，__剩余的工作__ 应为 `0`。

对于 `ADD` 循环：

* __已完成的工作__ 是 `m`；
* __剩余的工作__ 是 `n`；
* __期望的结果__ 是 `n₀ + m₀`。

## 验证条件生成器

__验证条件生成器__（Verification Condition Generators，VCGs）是自动应用霍尔规则的程序，生成用户必须证明的__验证条件__。用户通常还需要在程序中提供足够强的不变式作为注释。

我们可以使用 Lean 的元编程框架来定义一个简单的验证条件生成器。

数以百计的程序验证工具都基于这些原理。

验证条件生成器通常从后条件开始逆向工作，使用逆向规则（这些规则以任意的 `Q` 作为其后条件）。这种方法效果很好，因为 `Assign` 是逆向的。 -/

def Stmt.invWhileDo (I B : State → Prop) (S : Stmt) : Stmt :=
  Stmt.whileDo B S

namespace PartialHoare

theorem invWhile_intro {B I Q S}
      (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
      (hQ : ∀s, ¬ B s → I s → Q s) :
    {* I *} (Stmt.invWhileDo I B S) {* Q *} :=
  while_intro' I hS (by aesop) hQ

theorem invWhile_intro' {B I P Q S}
      (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
      (hP : ∀s, P s → I s) (hQ : ∀s, ¬ B s → I s → Q s) :
    {* P *} (Stmt.invWhileDo I B S) {* Q *} :=
  while_intro' I hS hP hQ

end PartialHoare

def matchPartialHoare : Expr → Option (Expr × Expr × Expr)
  | (Expr.app (Expr.app (Expr.app
       (Expr.const ``PartialHoare _) P) S) Q) =>
    Option.some (P, S, Q)
  | _ =>
    Option.none

partial def vcg : TacticM Unit :=
  do
    let goals ← getUnsolvedGoals
    if goals.length != 0 then
      let target ← getMainTarget
      match matchPartialHoare target with
      | Option.none           => return
      | Option.some (P, S, Q) =>
        if Expr.isAppOfArity S ``Stmt.skip 0 then
          if Expr.isMVar P then
            applyConstant ``PartialHoare.skip_intro
          else
            applyConstant ``PartialHoare.skip_intro'
        else if Expr.isAppOfArity S ``Stmt.assign 2 then
          if Expr.isMVar P then
            applyConstant ``PartialHoare.assign_intro
          else
            applyConstant ``PartialHoare.assign_intro'
        else if Expr.isAppOfArity S ``Stmt.seq 2 then
          andThenOnSubgoals
            (applyConstant ``PartialHoare.seq_intro') vcg
        else if Expr.isAppOfArity S ``Stmt.ifThenElse 3 then
          andThenOnSubgoals
            (applyConstant ``PartialHoare.if_intro) vcg
        else if Expr.isAppOfArity S ``Stmt.invWhileDo 3 then
          if Expr.isMVar P then
            andThenOnSubgoals
              (applyConstant ``PartialHoare.invWhile_intro) vcg
          else
            andThenOnSubgoals
              (applyConstant ``PartialHoare.invWhile_intro')
              vcg
        else
          failure

elab "vcg" : tactic =>
  vcg


/- ## 第二个程序回顾：两数相加 -/

theorem ADD_correct_vcg (n₀ m₀ : ℕ) :
    {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
    (ADD)
    {* fun s ↦ s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
  show {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
     (Stmt.invWhileDo (fun s ↦ s "n" + s "m" = n₀ + m₀)
        (fun s ↦ s "n" ≠ 0)
        (Stmt.assign "n" (fun s ↦ s "n" - 1);
         Stmt.assign "m" (fun s ↦ s "m" + 1)))
     {* fun s ↦ s "n" = 0 ∧ s "m" = n₀ + m₀ *} from
  by
    vcg <;>
      aesop


/- ## 完全正确性的霍尔三元组

**完全正确性**不仅断言程序是部分正确的，还断言程序总是能正常终止。用于完全正确性的霍尔三元组具有以下形式：

    [P] S [Q]

其预期含义为：

    如果在执行 `S` 之前 `P` 成立，则执行会正常终止，并且在最终状态中 `Q` 成立。

对于确定性程序，等价的表述如下：

    如果在执行 `S` 之前 `P` 成立，则存在一个状态，在该状态下执行会正常终止，并且 `Q` 在该状态中成立。

示例：

    `[i ≤ 10] while i ≠ 10 do i := i + 1 [i = 10]`

在我们的 WHILE 语言中，这仅影响 while 循环，现在必须为 while 循环标注一个**变体** `V`（一个随着每次迭代递减的自然数）：

    [I ∧ B ∧ V = v₀] S [I ∧ V < v₀]
    ——————————————————————————————— While-Var
    [I] while B do S [I ∧ ¬B]

对于上述示例，合适的变体是什么？ -/

end LoVe
