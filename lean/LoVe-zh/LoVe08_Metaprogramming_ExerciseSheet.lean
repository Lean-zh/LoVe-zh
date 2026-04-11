/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe08_Metaprogramming_Demo


/- # LoVe 练习 8：元编程

将占位符（例如，`:= sorry`）替换为你的解决方案。 -/


set_option autoImplicit false
set_option tactic.hygienic false
set_option linter.unusedTactic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## 问题1：增强版的 `destruct_and`

从讲座中回顾一下，`destruct_and` 在一些简单的目标上会失败，例如 -/

theorem abc_ac (a b c : Prop) (h : a ∧ b ∧ c) :
    a ∧ c :=
  sorry

/- 我们现在将通过开发一个名为 `destro_and` 的新策略来解决这个问题，该策略同时应用合取（conjunction）的**析构**（destruction）和**引入**（intro**duction）规则。它还会自动遍历假设，而不是接受参数。我们将分三个步骤来开发它。

1.1. 开发一个名为 `intro_and` 的策略，该策略将所有形式为 `a ∧ b` 的目标系统地替换为两个新目标 `a` 和 `b`，直到所有顶层的合取都被消除。将该策略定义为一个宏。 -/

#check repeat'

-- 请输入您的定义
theorem abcd_bd (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
    b ∧ d :=
  by
    intro_and
    /- 证明状态应如下所示：

        case left
        a b c d: 命题
        h : a ∧ (b ∧ c) ∧ d
        ⊢ b

        case right
        a b c d : 命题
        h : a ∧ (b ∧ c) ∧ d
        ⊢ d -/
    repeat' sorry

theorem abcd_bacb (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
    b ∧ (a ∧ (c ∧ b)) :=
  by
    intro_and
    /- 证明状态应如下所示：

        case left
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ b

        case right.left
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ a

        case right.right.left
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ c

        case right.right.right
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ b

翻译后的中文如下：

证明状态应如下所示：

        情况 left
        a b c d : 命题
        h : a ∧ (b ∧ c) ∧ d
        ⊢ b

        情况 right.left
        a b c d : 命题
        h : a ∧ (b ∧ c) ∧ d
        ⊢ a

        情况 right.right.left
        a b c d : 命题
        h : a ∧ (b ∧ c) ∧ d
        ⊢ c

        情况 right.right.right
        a b c d : 命题
        h : a ∧ (b ∧ c) ∧ d
        ⊢ b -/
    repeat' sorry

/- 1.2. 开发一个名为 `cases_and` 的策略，该策略将形式为 `h : a ∧ b` 的假设系统地替换为两个新的假设 `h_left : a` 和 `h_right : b`，直到所有顶层的合取式都被消除。

以下是一些可以遵循的伪代码：

1. 将整个 `do` 块包装在 `withMainContext` 调用中，以确保在正确的上下文中工作。

2. 从上下文中检索假设列表。这可以通过 `getLCtx` 提供。

3. 找到第一个类型（即命题）为 `_ ∧ _` 形式的假设（即项）。为了迭代，可以使用 `for … in … do` 语法。要获取项的类型，可以使用 `inferType`。要检查类型 `ty` 是否具有 `_ ∧ _` 的形式，可以使用 `Expr.isAppOfArity ty ``And 2`（在 `And` 前有两个反引号）。

4. 对找到的第一个假设进行情况分析。这可以通过使用 `LoVelib` 中提供的元程序 `cases` 来实现，它与 `cases` 策略类似，但是一个元程序。要提取与假设关联的自由变量，可以使用 `LocalDecl.fvarId`。

5. 重复（通过递归调用）。

6. 返回。

提示：在迭代本地上下文中的声明时，请确保跳过任何作为实现细节的声明。 -/

partial def casesAnd : TacticM Unit :=
  sorry

elab "cases_and" : tactic =>
  casesAnd

theorem abcd_bd_again (a b c d : Prop) :
    a ∧ (b ∧ c) ∧ d → b ∧ d :=
  by
    intro h
    cases_and
    /- 证明状态应如下所示：

        case intro.intro.intro
        a b c d : Prop
        left : a
        right : d
        left_1 : b
        right_1 : c
        ⊢ b ∧ d

翻译为中文：

证明状态应如下所示：

        case intro.intro.intro
        a b c d : 命题
        left : a
        right : d
        left_1 : b
        right_1 : c
        ⊢ b ∧ d

其中：
- `Prop` 翻译为“命题”
- `⊢` 表示“推导出”或“需要证明”
- `∧` 表示逻辑“与” -/
    sorry

/- 1.3. 实现一个 `destro_and` 策略，该策略首先调用 `cases_and`，然后调用 `intro_and`，接着尝试通过 `assumption` 直接证明所有可以立即解决的子目标。 -/

macro "destro_and" : tactic =>
  sorry

theorem abcd_bd_over_again (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
    b ∧ d :=
  by destro_and

theorem abcd_bacb_again (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
    b ∧ (a ∧ (c ∧ b)) :=
  by destro_and

theorem abd_bacb_again (a b c d : Prop) (h : a ∧ b ∧ d) :
    b ∧ (a ∧ (c ∧ b)) :=
  by
    destro_and
    /- 证明状态应大致如下：

        case intro.intro.right.right.left
        a b c d : 命题
        left : a
        left_1 : b
        right : d
        ⊢ c

解释：
- `case intro.intro.right.right.left`：表示当前处理的证明分支路径。
- `a b c d : 命题`：定义了四个命题变量 `a`, `b`, `c`, `d`。
- `left : a`：假设 `a` 为真。
- `left_1 : b`：假设 `b` 为真。
- `right : d`：假设 `d` 为真。
- `⊢ c`：当前需要证明的目标是 `c`。 -/
    sorry   -- 不可证明的

在技术文档中，"unprovable" 通常用于描述某个命题、定理或陈述在特定逻辑系统或理论框架内无法被证明为真或假。这个术语在数学、计算机科学和逻辑学中尤为重要，特别是在讨论形式系统、算法复杂性或理论计算机科学时。

例如，在哥德尔不完备定理的背景下，某些命题在给定的公理系统中是不可证明的，这意味着无法通过该系统的规则和公理来证明这些命题的真伪。

因此，"unprovable" 在中文技术文档中应翻译为“不可证明的”，以保持其专业性和准确性。
/- 1.4. 提供更多关于 `destro_and` 的示例，以验证其在更复杂的情况下也能按预期工作。 -/

-- 请输入您的示例内容

/- ## 问题2：定理查找器

我们将实现一个函数，该函数允许我们通过出现在定理陈述中的常量来查找定理。因此，给定一个常量名称列表，该函数将列出所有包含这些常量的定理。

2.1. 编写一个函数，用于检查表达式中是否包含特定常量。

提示：

* 你可以对 `e` 进行模式匹配，并递归处理。

* `Bool` 类型上的“非”连接词称为 `not`，“或”连接词称为 `||`，“与”连接词称为 `&&`，相等性判断称为 `==`。 -/

def constInExpr (name : Name) (e : Expr) : Bool :=
  sorry

/- 2.2. 编写一个函数，用于检查一个表达式是否包含列表中的**所有**常量。

提示：你可以选择递归处理，或者使用 `List.and` 和 `List.map`。 -/

def constsInExpr (names : List Name) (e : Expr) : Bool :=
  sorry

/- 2.3. 开发一种策略，使用 `constsInExpr` 打印所有在其陈述中包含所有常量 `names` 的定理的名称。

此代码应与演示文件中的 `proveDirect` 类似。通过 `ConstantInfo.type`，您可以提取与定理相关的命题。 -/

def findConsts (names : List Name) : TacticM Unit :=
  sorry

elab "find_consts" "(" names:ident+ ")" : tactic =>
  findConsts (Array.toList (Array.map getId names))

/- 测试解决方案。 -/

theorem List.a_property_of_reverse {α : Type} (xs : List α) (a : α) :
    List.concat xs a = List.reverse (a :: List.reverse xs) :=
  by
    find_consts (List.reverse)
    find_consts (List.reverse List.concat)
    sorry

end LoVe
