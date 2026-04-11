/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe 演示 9：操作语义

在本讲及接下来的两讲中，我们将探讨如何使用 Lean 来指定编程语言的语法和语义，并基于语义进行推理。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 首要任务：形式化项目

作为两份作业的替代，你可以选择一个验证项目，价值20分。如果你选择这样做，请在本周末之前通过电子邮件向你的讲师发送消息。对于一个完全成功的项目，我们期望大约200行（或更多）的Lean代码，包括定义和证明。

以下是一些项目想法。

**计算机科学：**

* 带有静态数组或其他特性的扩展WHILE语言；
* 函数式数据结构（例如，平衡树）；
* 函数式算法（例如，冒泡排序、归并排序、Tarjan算法）；
* 从表达式或命令式程序到栈式机器的编译器；
* 类型系统（例如，Benjamin Pierce的《类型与编程语言》）；
* 安全属性（例如，Volpano-Smith风格的非干扰分析）；
* 一阶项理论，包括匹配、项重写；
* 自动机理论；
* 上下文无关文法或正则表达式的规范化；
* 进程代数和双相似性；
* 证明系统的可靠性及可能的完备性（例如，Genzen的序列演算、自然演绎、表列法）；
* 分离逻辑；
* 使用Hoare逻辑的验证程序。

**数学：**

* 图论；
* 组合数学；
* 数论。

**元编程：**

* 自定义策略；
* 自定义诊断工具。

**过往评价：**

问：你觉得这个项目怎么样？

答：很有趣。

答：既有趣又困难。

答：很好，我认为这种形式非常棒，因为它给了人们机会去做一些有挑战性的练习，并且可以提交未完成的作品。

答：我真的很喜欢。我认为这是一种很好的学习方式——找到你喜欢的东西，深入挖掘，遇到困难时寻求帮助。我希望我能做更多这样的项目！

答：有时间去尝试解决一些你自己感兴趣的东西真是太棒了。

答：实际上非常有趣！！！

答：非常有帮助。它提供了机会让我们在课程的某个特定方面花更多时间。

## 形式语义

形式语义有助于指定和推理编程语言本身以及个别程序。

它可以成为验证编译器、解释器、验证器、静态分析器、类型检查器等工具的基础。没有形式化证明，这些工具**几乎总是错误的**。

在这一领域，证明助手被广泛使用。每年，大约10-20%的POPL论文部分或全部形式化。这种成功的原因包括：

* 除了归纳类型、谓词和递归函数外，几乎不需要其他机制（背景库、策略）就可以开始。
* 证明往往有很多情况，这非常适合计算机处理。
* 证明助手会跟踪当我们在编程语言中添加更多特性时需要更改的内容。

以WebAssembly为例。引用Conrad Watt的话（略有缩写）：

    我们已经完成了WebAssembly语言核心执行语义和类型系统的完整Isabelle机械化。为了完成这个证明，**官方WebAssembly规范中的一些缺陷**，通过我们的证明和建模工作被发现并需要修正。在某些情况下，这些缺陷意味着类型系统**最初是不健全的**。

    我们与工作组保持了建设性的对话，验证了新增的特性。特别是，WebAssembly实现与其宿主环境交互的机制在工作组的原始论文中没有正式指定。扩展我们的机械化模型以模拟这一特性揭示了WebAssembly规范中的一个缺陷，该缺陷**破坏了类型系统的健全性**。

## 一个极简的命令式语言

状态`s`是一个从变量名到值的函数（`String → ℕ`）。

**WHILE** 是一个极简的命令式语言，其语法如下：

    S  ::=  skip                 -- 空操作
         |  x := a               -- 赋值
         |  S; S                 -- 顺序组合
         |  if B then S else S   -- 条件语句
         |  while B do S         -- while循环

其中`S`表示语句（也称为命令或程序），`x`表示变量，`a`表示算术表达式，`B`表示布尔表达式。 -/**

在计算机科学和编程中，"assignment"（任务分配）通常指的是将一个值或对象分配给一个变量。这个过程是通过赋值操作符（如 `=`）来完成的。例如，在Python中，`x = 5` 表示将整数值 `5` 分配给变量 `x`。

在更广泛的上下文中，"assignment" 也可以指在项目管理或团队协作中，将特定的任务或职责分配给个人或团队。这种分配通常涉及明确的任务描述、截止日期和预期结果。

在数据库管理中，"assignment" 可能涉及到将特定的数据记录或查询结果分配给某个用户或系统进行处理。

总之，"assignment" 是一个多用途的术语，具体含义取决于上下文。在编程中，它通常与变量赋值相关；在项目管理中，它涉及任务分配；在数据库管理中，它可能涉及数据记录的分配。         |  S; S                 -- 顺序组合         |  if B then S else S   -- 条件语句

在编程中，条件语句（conditional statement）用于根据特定条件的真假来执行不同的代码块。常见的条件语句包括 `if`、`else if`（或 `elif`）和 `else`。通过这些语句，程序可以根据不同的输入或状态做出相应的决策。

例如：
```python
if condition1:
    # 如果 condition1 为真，执行此代码块
    statement1
elif condition2:
    # 如果 condition1 为假且 condition2 为真，执行此代码块
    statement2
else:
    # 如果上述条件均为假，执行此代码块
    statement3
```

条件语句是控制程序流程的重要工具，广泛应用于各种编程语言中。         |  while B do S         -- while 循环

在编程中，`while` 循环是一种控制流语句，它允许代码在满足特定条件的情况下重复执行。`while` 循环的基本结构如下：

```python
while 条件:
    # 循环体
```

在这个结构中，`条件` 是一个布尔表达式。只要 `条件` 为 `True`，循环体中的代码就会不断执行。一旦 `条件` 变为 `False`，循环就会终止，程序将继续执行循环之后的代码。

### 示例

以下是一个简单的 `while` 循环示例，它从 1 数到 5：

```python
count = 1
while count <= 5:
    print(count)
    count += 1
```

在这个例子中，`count` 的初始值为 1。`while` 循环会检查 `count` 是否小于或等于 5。如果是，它会打印当前的 `count` 值，并将 `count` 增加 1。这个过程会一直重复，直到 `count` 的值超过 5，此时循环结束。

### 注意事项

1. **无限循环**：如果 `条件` 永远为 `True`，`while` 循环将无限执行下去，这通常是一个错误。为了避免这种情况，确保循环体中有改变 `条件` 的代码。

2. **循环控制**：可以使用 `break` 语句提前退出循环，或者使用 `continue` 语句跳过当前迭代，直接进入下一次循环。

### 总结

`while` 循环是一种强大的工具，适用于需要在满足特定条件时重复执行代码的场景。正确使用 `while` 循环可以简化代码逻辑，但需要注意避免无限循环等问题。

---

希望这个翻译对您有帮助！如果有其他问题，请随时提问。
where `S` stands for a statement (also called command or program), `x` for a
variable, `a` for an arithmetic expression, and `B` for a Boolean expression. -/

#print State

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- 在我们的语法中，我们有意未指定算术表达式和布尔表达式的具体语法。在 Lean 中，我们有以下选择：

* 我们可以使用类似于第 2 讲中的 `AExp` 类型来表示算术表达式，布尔表达式也可以类似处理。

* 我们可以决定将算术表达式简单地定义为从状态到自然数的函数（`State → ℕ`），而布尔表达式则定义为谓词（`State → Prop` 或 `State → Bool`）。

这对应于**深度嵌入**和**浅层嵌入**之间的区别：

* **深度嵌入**是指将某种语法（表达式、公式、程序等）的抽象语法树在证明助手中明确指定（例如 `AExp`），并为其定义语义（例如 `eval`）。

* 相比之下，**浅层嵌入**则直接复用逻辑中的相应机制（例如项、函数、谓词类型）。

深度嵌入允许我们对语法（及其语义）进行推理。浅层嵌入则更为轻量级，因为我们可以直接使用它，而无需定义语义。

我们将对程序使用深度嵌入（因为我们认为这很有趣），而对赋值和布尔表达式使用浅层嵌入（因为我们认为这些较为乏味）。

以下程序：

```
while x > y do
  skip;
  x := x - 1
```

将被建模为： -/

def sillyLoop : Stmt :=
  Stmt.whileDo (fun s ↦ s "x" > s "y")
    (Stmt.skip;
     Stmt.assign "x" (fun s ↦ s "x" - 1))


/- ## 大步语义

**操作语义**对应于一个理想化的解释器（用一种类似Prolog的语言指定）。主要有两种变体：

* 大步语义；
* 小步语义。

在**大步语义**（也称为**自然语义**）中，判断的形式为 `(S, s) ⟹ t`：

    从状态 `s` 开始，执行 `S` 终止于状态 `t`。

示例：

    `(x := x + y; y := 0, [x ↦ 3, y ↦ 5]) ⟹ [x ↦ 8, y ↦ 0]`

推导规则：

    ——————————————— Skip（跳过）
    (skip, s) ⟹ s

    ——————————————————————————— Assign（赋值）
    (x := a, s) ⟹ s[x ↦ s(a)]

    (S, s) ⟹ t   (T, t) ⟹ u
    ——————————————————————————— Seq（顺序）
    (S; T, s) ⟹ u

    (S, s) ⟹ t
    ————————————————————————————— If-True（如果为真）  如果 s(B) 为真
    (if B then S else T, s) ⟹ t

    (T, s) ⟹ t
    ————————————————————————————— If-False（如果为假）  如果 s(B) 为假
    (if B then S else T, s) ⟹ t

    (S, s) ⟹ t   (while B do S, t) ⟹ u
    —————————————————————————————————————— While-True（循环为真）  如果 s(B) 为真
    (while B do S, s) ⟹ u

    ————————————————————————— While-False（循环为假）  如果 s(B) 为假
    (while B do S, s) ⟹ s

在上文中，`s(e)` 表示表达式 `e` 在状态 `s` 中的值，而 `s[x ↦ s(e)]` 表示与 `s` 相同的状态，只是变量 `x` 被绑定到值 `s(e)`。

在Lean中，判断对应于一个归纳谓词，推导规则对应于该谓词的引入规则。使用归纳谓词而不是递归函数，可以处理非终止（例如，一个发散的 `while` 循环）和非确定性（例如，多线程）。 -/

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S T s t u) (hS : BigStep (S, s) t)
      (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S T s t) (hcond : B s)
      (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t) (hcond : ¬ B s)
      (hbody : BigStep (T, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | while_true (B S s t u) (hcond : B s)
      (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.whileDo B S, t) u) :
    BigStep (Stmt.whileDo B S, s) u
  | while_false (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.whileDo B S, s) s

infix:110 " ⟹ " => BigStep

theorem sillyLoop_from_1_BigStep :
    (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⟹ (fun _ ↦ 0) :=
  by
    rw [sillyLoop]
    apply BigStep.while_true
    { simp }
    { apply BigStep.seq
      { apply BigStep.skip }
      { apply BigStep.assign } }
    { simp
      apply BigStep.while_false
      simp }


/- ## 大步语义的性质

配备了大步语义后，我们可以：

* 证明编程语言的性质，例如程序之间的**等价性证明**和**确定性**；

* 对**具体程序**进行推理，证明与最终状态 `t` 和初始状态 `s` 相关的定理。 -/

theorem BigStep_deterministic {Ss l r} (hl : Ss ⟹ l)
      (hr : Ss ⟹ r) :
    l = r :=
  by
    induction hl generalizing r with
    | skip s =>
      cases hr with
      | skip => rfl
    | assign x a s =>
      cases hr with
      | assign => rfl
    | seq S T s l₀ l hS hT ihS ihT =>
      cases hr with
      | seq _ _ _ r₀ _ hS' hT' =>
        cases ihS hS' with
        | refl =>
          cases ihT hT' with
          | refl => rfl
    | if_true B S T s l hB hS ih =>
      cases hr with
      | if_true _ _ _ _ _ hB' hS'  => apply ih hS'
      | if_false _ _ _ _ _ hB' hS' => aesop
    | if_false B S T s l hB hT ih =>
      cases hr with
      | if_true _ _ _ _ _ hB' hS'  => aesop
      | if_false _ _ _ _ _ hB' hS' => apply ih hS'
    | while_true B S s l₀ l hB hS hw ihS ihw =>
      cases hr with
      | while_true _ _ _ r₀ hB' hB' hS' hw' =>
        cases ihS hS' with
        | refl =>
          cases ihw hw' with
          | refl => rfl
      | while_false _ _ _ hB' => aesop
    | while_false B S s hB =>
      cases hr with
      | while_true _ _ _ s' _ hB' hS hw => aesop
      | while_false _ _ _ hB'           => rfl

/- 定理 BigStep_终止性 {S s} :
    ∃t, (S, s) ⟹ t :=
  抱歉  -- 无法证明

（注：此处“抱歉”表示该定理在当前上下文中无法被证明，通常用于占位或表示未完成的部分。） -/"unprovable" 通常用于描述某个命题、定理或陈述在特定逻辑系统或理论框架内无法被证明为真或假。这个术语在数学、计算机科学和逻辑学中尤为重要，特别是在讨论形式系统、可计算性理论和哥德尔不完备定理时。

例如，在哥德尔不完备定理的背景下，某些命题在给定的公理系统中是“不可证明的”，即无法通过该系统的规则和公理来证明其真伪。

因此，"unprovable" 在中文技术文档中应翻译为“不可证明的”，以保持其专业性和准确性。-/

/- 我们可以定义关于大步语义的反演规则： -/

@[simp] theorem BigStep_skip_Iff {s t} :
    (Stmt.skip, s) ⟹ t ↔ t = s :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | skip => rfl }
    { intro h
      rw [h]
      apply BigStep.skip }

@[simp] theorem BigStep_assign_Iff {x a s t} :
    (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | assign => rfl }
    { intro h
      rw [h]
      apply BigStep.assign }

@[simp] theorem BigStep_seq_Iff {S T s u} :
    (S; T, s) ⟹ u ↔ (∃t, (S, s) ⟹ t ∧ (T, t) ⟹ u) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | seq =>
        apply Exists.intro
        apply And.intro <;>
          assumption }
    { intro h
      cases h with
      | intro s' h' =>
        cases h' with
        | intro hS hT =>
          apply BigStep.seq <;>
            assumption }

@[simp] theorem BigStep_if_Iff {B S T s t} :
    (Stmt.ifThenElse B S T, s) ⟹ t ↔
    (B s ∧ (S, s) ⟹ t) ∨ (¬ B s ∧ (T, s) ⟹ t) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | if_true _ _ _ _ _ hB hS =>
        apply Or.intro_left
        aesop
      | if_false _ _ _ _ _ hB hT =>
        apply Or.intro_right
        aesop }
    { intro h
      cases h with
      | inl h =>
        cases h with
        | intro hB hS =>
          apply BigStep.if_true <;>
            assumption
      | inr h =>
        cases h with
        | intro hB hT =>
          apply BigStep.if_false <;>
            assumption }

theorem BigStep_while_Iff {B S s u} :
    (Stmt.whileDo B S, s) ⟹ u ↔
    (B s ∧ ∃t, (S, s) ⟹ t ∧ (Stmt.whileDo B S, t) ⟹ u)
    ∨ (¬ B s ∧ u = s) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | while_true _ _ _ t _ hB hS hw => aesop
      | while_false _ _ _ hB => aesop }
    { intro h
      cases h with
      | inl hex =>
        cases hex with
        | intro t h =>
          cases h with
          | intro hB h =>
            cases h with
            | intro hS hwhile =>
              apply BigStep.while_true <;>
                assumption
      | inr h =>
        cases h with
        | intro hB hus =>
          rw [hus]
          apply BigStep.while_false
          assumption}

@[simp] theorem BigStep_while_true_Iff {B S s u}
      (hcond : B s) :
    (Stmt.whileDo B S, s) ⟹ u ↔
    (∃t, (S, s) ⟹ t ∧ (Stmt.whileDo B S, t) ⟹ u) :=
  by
    rw [BigStep_while_Iff]
    simp [hcond]

@[simp] theorem BigStep_while_false_Iff {B S s t}
      (hcond : ¬ B s) :
    (Stmt.whileDo B S, s) ⟹ t ↔ t = s :=
  by
    rw [BigStep_while_Iff]
    simp [hcond]


/- ## 小步语义

大步语义（Big-step semantics）

* 不允许我们推理中间状态；
* 不允许我们表达非终止性或交错执行（对于多线程）。

**小步语义**（也称为**结构操作语义**）解决了上述问题。

一个判断的形式为 `(S, s) ⇒ (T, t)`：

    从状态 `s` 开始，执行 `S` 的一步后，我们处于状态 `t`，并且程序 `T` 仍需执行。

一个执行过程是一个有限或无限的链 `(S₀, s₀) ⇒ (S₁, s₁) ⇒ …`。

一个对 `(S, s)` 被称为**配置**。如果不存在形式为 `(S, s) ⇒ _` 的转换，则该配置是**终止的**。

示例：

      `(x := x + y; y := 0, [x ↦ 3, y ↦ 5])`
    `⇒ (skip; y := 0,       [x ↦ 8, y ↦ 5])`
    `⇒ (y := 0,             [x ↦ 8, y ↦ 5])`
    `⇒ (skip,               [x ↦ 8, y ↦ 0])`

推导规则：

    ————————————————————————————————— 赋值
    (x := a, s) ⇒ (skip, s[x ↦ s(a)])

    (S, s) ⇒ (S', s')
    ———-——————————————————— 序列步骤
    (S; T, s) ⇒ (S'; T, s')

    ————————————————————— 序列跳过
    (skip; S, s) ⇒ (S, s)

    ———————————————————————————————— 如果为真   如果 s(B) 为真
    (if B then S else T, s) ⇒ (S, s)

    ———————————————————————————————— 如果为假   如果 s(B) 为假
    (if B then S else T, s) ⇒ (T, s)

    ——————————————————————————————————————————————————————————————— 循环
    (while B do S, s) ⇒ (if B then (S; while B do S) else skip, s)

没有针对 `skip` 的规则（为什么？）。 -/

inductive SmallStep : Stmt × State → Stmt × State → Prop where
  | assign (x a s) :
    SmallStep (Stmt.assign x a, s) (Stmt.skip, s[x ↦ a s])
  | seq_step (S S' T s s') (hS : SmallStep (S, s) (S', s')) :
    SmallStep (S; T, s) (S'; T, s')
  | seq_skip (T s) :
    SmallStep (Stmt.skip; T, s) (T, s)
  | if_true (B S T s) (hcond : B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (S, s)
  | if_false (B S T s) (hcond : ¬ B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (T, s)
  | whileDo (B S s) :
    SmallStep (Stmt.whileDo B S, s)
      (Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip, s)

infixr:100 " ⇒ " => SmallStep
infixr:100 " ⇒* " => RTC SmallStep

theorem sillyLoop_from_1_SmallStep :
    (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⇒*
    (Stmt.skip, (fun _ ↦ 0)) :=
  by
    rw [sillyLoop]
    apply RTC.head
    { apply SmallStep.whileDo }
    { apply RTC.head
      { apply SmallStep.if_true
        aesop }
      { apply RTC.head
        { apply SmallStep.seq_step
          apply SmallStep.seq_skip }
        { apply RTC.head
          { apply SmallStep.seq_step
            apply SmallStep.assign }
          { apply RTC.head
            { apply SmallStep.seq_skip }
            { apply RTC.head
              { apply SmallStep.whileDo }
              { apply RTC.head
                { apply SmallStep.if_false
                  simp }
                { simp
                  apply RTC.refl } } } } } } }

/- 配备了小步语义后，我们可以**定义**大步语义：

    `(S, s) ⟹ t` 当且仅当 `(S, s) ⇒* (skip, t)`

其中 `r*` 表示关系 `r` 的自反传递闭包。

或者，如果我们已经定义了大步语义，我们可以**证明**上述等价定理以验证我们的定义。

小步语义的主要缺点是现在我们有两个关系，`⇒` 和 `⇒*`，推理往往更加复杂。

## 小步语义的性质

我们可以证明配置 `(S, s)` 是最终的当且仅当 `S = skip`。这确保了我们没有遗漏任何推导规则。 -/

theorem SmallStep_final (S s) :
    (¬ ∃T t, (S, s) ⇒ (T, t)) ↔ S = Stmt.skip :=
  by
    induction S with
    | skip =>
      simp
      intros T t hstep
      cases hstep
    | assign x a =>
      simp
      apply Exists.intro Stmt.skip
      apply Exists.intro (s[x ↦ a s])
      apply SmallStep.assign
    | seq S T ihS ihT =>
      simp
      cases Classical.em (S = Stmt.skip) with
      | inl h =>
        rw [h]
        apply Exists.intro T
        apply Exists.intro s
        apply SmallStep.seq_skip
      | inr h =>
        simp [h] at ihS
        cases ihS with
        | intro S' hS₀ =>
          cases hS₀ with
          | intro s' hS =>
            apply Exists.intro (S'; T)
            apply Exists.intro s'
            apply SmallStep.seq_step
            assumption
    | ifThenElse B S T ihS ihT =>
      simp
      cases Classical.em (B s) with
      | inl h =>
        apply Exists.intro S
        apply Exists.intro s
        apply SmallStep.if_true
        assumption
      | inr h =>
        apply Exists.intro T
        apply Exists.intro s
        apply SmallStep.if_false
        assumption
    | whileDo B S ih =>
      simp
      apply Exists.intro
        (Stmt.ifThenElse B (S; Stmt.whileDo B S)
           Stmt.skip)
      apply Exists.intro s
      apply SmallStep.whileDo

theorem SmallStep_deterministic {Ss Ll Rr}
      (hl : Ss ⇒ Ll) (hr : Ss ⇒ Rr) :
    Ll = Rr :=
  by
    induction hl generalizing Rr with
    | assign x a s =>
      cases hr with
      | assign _ _ _ => rfl
    | seq_step S S₁ T s s₁ hS₁ ih =>
      cases hr with
      | seq_step S S₂ _ _ s₂ hS₂ =>
        have hSs₁₂ :=
          ih hS₂
        aesop
      | seq_skip => cases hS₁
    | seq_skip T s =>
      cases hr with
      | seq_step _ S _ _ s' hskip => cases hskip
      | seq_skip                  => rfl
    | if_true B S T s hB =>
      cases hr with
      | if_true  => rfl
      | if_false => aesop
    | if_false B S T s hB =>
      cases hr with
      | if_true  => aesop
      | if_false => rfl
    | whileDo B S s =>
      cases hr with
      | whileDo => rfl

/- 我们可以基于小步语义定义反转规则。以下是三个示例： -/

theorem SmallStep_skip {S s t} :
    ¬ ((Stmt.skip, s) ⇒ (S, t)) :=
  by
    intro h
    cases h

@[simp] theorem SmallStep_seq_Iff {S T s Ut} :
    (S; T, s) ⇒ Ut ↔
    (∃S' t, (S, s) ⇒ (S', t) ∧ Ut = (S'; T, t))
    ∨ (S = Stmt.skip ∧ Ut = (T, s)) :=
  by
    apply Iff.intro
    { intro hST
      cases hST with
      | seq_step _ S' _ _ s' hS =>
        apply Or.intro_left
        apply Exists.intro S'
        apply Exists.intro s'
        aesop
      | seq_skip =>
        apply Or.intro_right
        aesop }
    {
      intro hor
      cases hor with
      | inl hex =>
        cases hex with
        | intro S' hex' =>
          cases hex' with
          | intro s' hand =>
            cases hand with
            | intro hS hUt =>
              rw [hUt]
              apply SmallStep.seq_step
              assumption
      | inr hand =>
        cases hand with
        | intro hS hUt =>
          rw [hS, hUt]
          apply SmallStep.seq_skip }

@[simp] theorem SmallStep_if_Iff {B S T s Us} :
    (Stmt.ifThenElse B S T, s) ⇒ Us ↔
    (B s ∧ Us = (S, s)) ∨ (¬ B s ∧ Us = (T, s)) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | if_true _ _ _ _ hB  => aesop
      | if_false _ _ _ _ hB => aesop }
    { intro hor
      cases hor with
      | inl hand =>
        cases hand with
        | intro hB hUs =>
          rw [hUs]
          apply SmallStep.if_true
          assumption
      | inr hand =>
        cases hand with
        | intro hB hUs =>
          rw [hUs]
          apply SmallStep.if_false
          assumption }


/- ### 大步语义与小步语义的等价性（**可选**）

一个更为重要的结果是大步语义与小步语义之间的联系：

    `(S, s) ⟹ t ↔ (S, s) ⇒* (Stmt.skip, t)`

其证明如下，但超出了本课程的范围。 -/

theorem RTC_SmallStep_seq {S T s u}
      (h : (S, s) ⇒* (Stmt.skip, u)) :
    (S; T, s) ⇒* (Stmt.skip; T, u) :=
  by
    apply RTC.lift (fun Ss ↦ (Prod.fst Ss; T, Prod.snd Ss)) _ h
    intro Ss Ss' hrtc
    cases Ss with
    | mk S s =>
      cases Ss' with
      | mk S' s' =>
        apply SmallStep.seq_step
        assumption

theorem RTC_SmallStep_of_BigStep {Ss t} (hS : Ss ⟹ t) :
    Ss ⇒* (Stmt.skip, t) :=
  by
    induction hS with
    | skip => exact RTC.refl
    | assign =>
      apply RTC.single
      apply SmallStep.assign
    | seq S T s t u hS hT ihS ihT =>
      apply RTC.trans
      { exact RTC_SmallStep_seq ihS }
      { apply RTC.head
        apply SmallStep.seq_skip
        assumption }
    | if_true B S T s t hB hst ih =>
      apply RTC.head
      { apply SmallStep.if_true
        assumption }
      { assumption }
    | if_false B S T s t hB hst ih =>
      apply RTC.head
      { apply SmallStep.if_false
        assumption }
      { assumption }
    | while_true B S s t u hB hS hw ihS ihw =>
      apply RTC.head
      { apply SmallStep.whileDo }
      { apply RTC.head
        { apply SmallStep.if_true
          assumption }
        { apply RTC.trans
          { exact RTC_SmallStep_seq ihS }
          { apply RTC.head
            apply SmallStep.seq_skip
            assumption } } }
    | while_false B S s hB =>
      apply RTC.tail
      apply RTC.single
      apply SmallStep.whileDo
      apply SmallStep.if_false
      assumption

theorem BigStep_of_SmallStep_of_BigStep {Ss₀ Ss₁ s₂}
      (h₁ : Ss₀ ⇒ Ss₁) :
    Ss₁ ⟹ s₂ → Ss₀ ⟹ s₂ :=
  by
    induction h₁ generalizing s₂ with
    | assign x a s               => simp
    | seq_step S S' T s s' hS ih => aesop
    | seq_skip T s               => simp
    | if_true B S T s hB         => aesop
    | if_false B S T s hB        => aesop
    | whileDo B S s              => aesop

theorem BigStep_of_RTC_SmallStep {Ss t} :
    Ss ⇒* (Stmt.skip, t) → Ss ⟹ t :=
  by
    intro hS
    induction hS using RTC.head_induction_on with
    | refl =>
      apply BigStep.skip
    | head Ss Ss' hST hsmallT ih =>
      cases Ss' with
      | mk S' s' =>
        apply BigStep_of_SmallStep_of_BigStep hST
        apply ih

theorem BigStep_Iff_RTC_SmallStep {Ss t} :
    Ss ⟹ t ↔ Ss ⇒* (Stmt.skip, t) :=
  Iff.intro RTC_SmallStep_of_BigStep BigStep_of_RTC_SmallStep

end LoVe
