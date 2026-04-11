/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe 作业 8（10 分 + 2 分附加分）：元编程

将占位符（例如，`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## 问题 1（10 分）：`safe` 策略

你将开发一个策略，该策略会穷举地应用所有关于连接词和量词的安全引入和消解规则。如果一个规则在给定可证明的目标时，总是生成可证明的子目标，则该规则被称为**安全的**。此外，我们要求安全规则不引入元变量（因为这些元变量很容易被错误地实例化为不正确的项）。

你将分三个步骤进行。

1.1（4 分）。开发一个 `safe_intros` 策略，该策略会重复应用 `True`、`∧` 和 `↔` 的引入规则，并为 `→`/`∀` 调用 `intro _`。该策略是对练习中 `intro_and` 的推广。 -/

macro "safe_intros" : tactic =>
  sorry

theorem abcd (a b c d : Prop) :
    a → ¬ b ∧ (c ↔ d) :=
  by
    safe_intros
    /- 证明状态应大致如下：

        case left
        a b c d : Prop
        a_1 : a
        a_2 : b
        ⊢ False

        case right.mp
        a b c d : Prop
        a_1 : a
        a_2 : c
        ⊢ d

        case right.mpr
        a b c d : Prop
        a_1 : a
        a_2 : d
        ⊢ c

翻译如下：

证明状态应大致如下：

        case left
        a b c d : 命题
        a_1 : a
        a_2 : b
        ⊢ 假

        case right.mp
        a b c d : 命题
        a_1 : a
        a_2 : c
        ⊢ d

        case right.mpr
        a b c d : 命题
        a_1 : a
        a_2 : d
        ⊢ c -/
    repeat' sorry

/- 1.2 (4 分). 开发一个 `safe_cases` 策略，用于对 `False`、`∧` (`And`) 和 `∃` (`Exists`) 进行情况分析。该策略是对练习中 `cases_and` 的泛化。

提示：

* `Expr.isAppOfArity` 的最后一个参数是逻辑符号所期望的参数数量。例如，`∧` 的参数数量为 2。

* `Bool` 上的“或”连接词称为 `||`。

提示：在遍历局部上下文中的声明时，请确保跳过任何作为实现细节的声明。 -/

#check @False
#check @And
#check @Exists

partial def safeCases : TacticM Unit :=
  sorry

elab "safe_cases" : tactic =>
  safeCases

theorem abcdef (a b c d e f : Prop) (P : ℕ → Prop)
      (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
      (hex : ∃x, P x) :
    False :=
  by
    safe_cases
  /- 证明状态应大致如下：

      case intro.intro.intro
      a b c d e f : 命题
      P : ℕ → 命题
      hneg : ¬a
      hor : c ∨ d
      himp : b → e
      hiff : e ↔ f
      left : a
      w : ℕ
      h : P w
      left_1 : b
      right : c
      ⊢ False

翻译说明：
1. 保留了所有专业术语，如 `Prop`（命题）、`ℕ`（自然数）、`¬`（非）、`∨`（或）、`→`（蕴含）、`↔`（等价）等。
2. 保持了原文的结构和格式，确保翻译后的文档与原文在逻辑上一致。
3. 使用了中文数学符号和术语，确保专业性和准确性。 -/
    sorry

/- 1.3 （2分）。实现一个名为 `safe` 的策略，该策略首先在所有目标上调用 `safe_intros`，然后在所有生成的子目标上调用 `safe_cases`，最后在所有生成的子子目标上尝试 `assumption`。 -/

macro "safe" : tactic =>
  sorry

theorem abcdef_abcd (a b c d e f : Prop) (P : ℕ → Prop)
      (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
      (hex : ∃x, P x) :
    a → ¬ b ∧ (c ↔ d) :=
  by
    safe
    /- 证明状态应大致如下：

        case left.intro.intro.intro
        a b c d e f : 命题
        P : ℕ → 命题
        hneg : ¬a
        hor : c ∨ d
        himp : b → e
        hiff : e ↔ f
        a_1 : a
        a_2 : b
        left : a
        w : ℕ
        h : P w
        left_1 : b
        right : c
        ⊢ 假

        case right.mp.intro.intro.intro
        a b c d e f : 命题
        P : ℕ → 命题
        hneg : ¬a
        hor : c ∨ d
        himp : b → e
        hiff : e ↔ f
        a_1 : a
        a_2 : c
        left : a
        w : ℕ
        h : P w
        left_1 : b
        right : c
        ⊢ d -/
    repeat' sorry


/- ## 问题 2（2 个附加分）：类似 `aesop` 的策略

### 2.1（1 个附加分）：开发一个简单的类似 `aesop` 的策略

该策略应应用所有安全的引入（introduction）和消解（elimination）规则。此外，它还应尝试应用可能不安全的规则（例如 `Or.inl` 和 `False.elim`），但在某个时刻进行回溯（或并行尝试多种可能性）。迭代加深（iterative deepening）可能是一种有效的方法，或者也可以采用最佳优先搜索（best-first search）或广度优先搜索（breadth-first search）。该策略还应尝试应用那些结论与目标匹配的假设，但在必要时进行回溯。

提示：`MonadBacktrack` 单子类可能会有所帮助。

### 2.2（1 个附加分）：在一些基准测试上测试你的策略

你可以在我们在练习和作业 3 中证明的逻辑谜题上尝试你的策略。请将测试结果包含在下方。 -/

end LoVe
