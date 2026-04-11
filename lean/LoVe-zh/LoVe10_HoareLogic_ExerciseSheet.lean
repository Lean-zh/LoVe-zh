/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe10_HoareLogic_Demo


/- # LoVe 练习 10：霍尔逻辑

将占位符（例如，`:= sorry`）替换为您的解决方案。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：程序验证

1.1. 以下WHILE程序接收两个数字`a`和`b`，并递增`b`直到它达到`a`： -/

def COUNT_UP : Stmt :=
  Stmt.whileDo (fun s ↦ s "b" ≠ s "a")
    (Stmt.assign "b" (fun s ↦ s "b" + 1))

/- 证明以下霍尔三元组。主要难点在于确定用于while循环的不变量。不变量应同时捕获已完成的工作（中间结果）和剩余待完成的工作。使用`show`命令在程序中标注循环不变量。

提示：如果变量`x`在程序中保持不变，可以通过在不变式中添加一个合取项`s "x" = x₀`来记录这一点，这可能会很有用。 -/

theorem COUNT_UP_correct (a₀ : ℕ) :
    {* fun s ↦ s "a" = a₀ *} (COUNT_UP) {* fun s ↦ s "a" = a₀ ∧ s "b" = a₀ *} :=
  sorry

/- 1.2. 如果程序在 `b > a` 的情况下运行会发生什么？这种情况如何通过霍尔三元组（Hoare triple）来体现？

**解释：**
- **霍尔三元组（Hoare triple）**：一种形式化方法，用于描述程序的前置条件、程序执行和后置条件之间的关系，通常表示为 `{P} C {Q}`，其中 `P` 是前置条件，`C` 是程序代码，`Q` 是后置条件。
- 问题探讨的是当输入条件 `b > a` 时，程序的执行结果如何，以及这种条件如何在霍尔三元组中被形式化地描述。 -/

-- 请提供需要翻译的技术文档内容，我将为您进行准确且专业的翻译。
/- 1.3. 以下 WHILE 程序旨在计算高斯求和至 `n`，并将结果存储在 `r` 中。 -/

def GAUSS (N : ℕ) : Stmt :=
  Stmt.assign "r" (fun s ↦ 0);
  Stmt.assign "n" (fun s ↦ 0);
  Stmt.whileDo (fun s ↦ s "n" ≠ N)
    (Stmt.assign "n" (fun s ↦ s "n" + 1);
     Stmt.assign "r" (fun s ↦ s "r" + s "n"))

/- 以下是同一函数的功能实现： -/

def sumUpTo : ℕ → ℕ
  | 0     => 0
  | n + 1 => n + 1 + sumUpTo n

/- 在 `GAUSS` 上调用 `vcg`，并使用合适的循环不变量来证明生成的验证条件。 -/

theorem GAUSS_correct (N : ℕ) :
    {* fun s ↦ True *} (GAUSS N) {* fun s ↦ s "r" = sumUpTo N *} :=
  sorry

/- 1.4 （**可选**）。以下程序 `MUL` 旨在计算 `n` 和 `m` 的乘积，并将结果存储在 `r` 中。使用合适的循环不变量对 `MUL` 调用 `vcg`，并证明生成的验证条件。 -/

def MUL : Stmt :=
  Stmt.assign "r" (fun s ↦ 0);
  Stmt.whileDo (fun s ↦ s "n" ≠ 0)
    (Stmt.assign "r" (fun s ↦ s "r" + s "m");
     Stmt.assign "n" (fun s ↦ s "n" - 1))

theorem MUL_correct (n₀ m₀ : ℕ) :
    {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *} (MUL) {* fun s ↦ s "r" = n₀ * m₀ *} :=
  sorry


/- ## 问题2：完全正确性的霍尔三元组

以下定义描述了确定性语言中完全正确性的霍尔三元组： -/

def TotalHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀s, P s → ∃t, (S, s) ⟹ t ∧ Q t

macro "[*" P:term " *] " "(" S:term ")" " [* " Q:term " *]" : term =>
  `(TotalHoare $P $S $Q)

namespace TotalHoare

/- 2.1. 证明推论规则。 -/

theorem consequence {P P' Q Q' S}
      (hS : [* P *] (S) [* Q *]) (hP : ∀s, P' s → P s) (hQ : ∀s, Q s → Q' s) :
    [* P' *] (S) [* Q' *] :=
  sorry

/- 2.2. 证明 `skip` 的规则 -/

theorem skip_intro {P} :
    [* P *] (Stmt.skip) [* P *] :=
  sorry

/- 2.3. 证明 `assign` 的规则。 -/

theorem assign_intro {P x a} :
    [* fun s ↦ P (s[x ↦ a s]) *] (Stmt.assign x a) [* P *] :=
  sorry

/- 2.4. 证明 `seq` 的规则。 -/

theorem seq_intro {P Q R S T} (hS : [* P *] (S) [* Q *])
      (hT : [* Q *] (T) [* R *]) :
    [* P *] (S; T) [* R *] :=
  sorry

/- 2.5. 完成 `if`–`then`–`else` 规则的证明。

提示：证明需要对 `B s` 的真值进行情况区分。 -/

theorem if_intro {B P Q S T}
      (hS : [* fun s ↦ P s ∧ B s *] (S) [* Q *])
      (hT : [* fun s ↦ P s ∧ ¬ B s *] (T) [* Q *]) :
    [* P *] (Stmt.ifThenElse B S T) [* Q *] :=
  sorry

/- 2.6 （**可选**）。尝试证明 `while` 的规则。

该规则由一个循环不变量 `I` 和一个变体 `V` 参数化，其中 `V` 在每次循环体迭代时递减。

在我们证明所需定理之前，我们引入一个辅助定理。其证明需要通过模式匹配和递归进行归纳。当使用 `var_while_intro_aux` 作为归纳假设时，我们建议在证明参数小于 `v₀` 后直接使用：

    have ih : ∃u, (Stmt.whileDo B S, t) ⟹ u ∧ I u ∧ ¬ B u :=
      have _ : V t < v₀ :=
        …
      var_while_intro_aux I V h_inv (V t) …

与 `if`--`then`--`else` 类似，该证明需要对 `B s` 的真值进行情况区分。 -/} (I : State → Prop) (V : State → ℕ) {S}
    (h_inv : ∀v₀,
       [* fun s ↦ I s ∧ B s ∧ V s = v₀ *] (S) [* fun s ↦ I s ∧ V s < v₀ *]) :
    ∀v₀ s, V s = v₀ → I s → ∃t, (Stmt.whileDo B S, s) ⟹ t ∧ I t ∧ ¬ B t
  | v₀, s, V_eq, hs =>
    sorry

theorem var_while_intro {B} (I : State → Prop) (V : State → ℕ) {S}
    (hinv : ∀v₀,
       [* fun s ↦ I s ∧ B s ∧ V s = v₀ *] (S) [* fun s ↦ I s ∧ V s < v₀ *]) :
    [* I *] (Stmt.whileDo B S) [* fun s ↦ I s ∧ ¬ B s *] :=
  sorry

end TotalHoare

end LoVe
