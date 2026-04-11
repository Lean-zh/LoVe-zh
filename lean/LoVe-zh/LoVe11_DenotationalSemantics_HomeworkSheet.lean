/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe11_DenotationalSemantics_Demo


/- # LoVe 作业 11（10 分 + 2 分附加分）：指称语义

请将占位符（例如，`:= sorry`）替换为您的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

/- 以下命令在每个 `Prop` 上启用不可计算的可判定性。
`0` 参数确保仅在必要时使用此功能；否则，它可能会导致某些可计算的定义在 Lean 中变为不可计算。根据你如何解决第 2.2 题，此命令可能会对你有所帮助。 -/

attribute [instance 0] Classical.propDecidable

/- 指称语义（Denotational semantics）非常适用于函数式编程。在本练习中，我们将研究Lean中一些函数式程序的表示及其指称语义。

`Nondet` 类型表示可以执行非确定性计算（nondeterministic computations）的函数式程序：程序可以在许多不同的计算路径/返回值之间进行选择。完全不返回任何结果由 `fail` 表示，而在两个选项之间进行非确定性选择（由 `Bool` 值 `true` 和 `false` 标识）则由 `choice` 表示。 -/

inductive Nondet (α : Type) : Type
  | just   : α → Nondet α
  | fail   : Nondet α
  | choice : (Bool → Nondet α) → Nondet α

namespace Nondet


/- ## 问题 1（5 分 + 1 分附加分）：`Nondet` 单子

`Nondet` 归纳类型构成了一个单子。`pure` 操作符是 `Nondet.just`。`bind` 定义如下： -/

def bind {α β : Type} : Nondet α → (α → Nondet β) → Nondet β
  | just a,   f => f a
  | fail,     f => fail
  | choice k, f => choice (fun b ↦ bind (k b) f)

instance : Pure Nondet :=
  { pure := just }

instance : Bind Nondet :=
  { bind := bind }

/- 1.1 (5 分). 证明 `Nondet` 的三个单子定律。

提示：

* 要展开 `pure` 和 `>>=` 的定义，可以使用 `simp [Bind.bind, Pure.pure]`。

* 要将 `f = g` 简化为 `∀x, f x = g x`，可以使用定理 `funext`。 -/

theorem pure_bind {α β : Type} (a : α) (f : α → Nondet β) :
    pure a >>= f = f a :=
 sorry

theorem bind_pure {α : Type} :
    ∀na : Nondet α, na >>= pure = na :=
  sorry

theorem bind_assoc {α β γ : Type} :
    ∀(na : Nondet α) (f : α → Nondet β) (g : β → Nondet γ),
      ((na >>= f) >>= g) = (na >>= (fun a ↦ f a >>= g)) :=
  sorry

/- 函数 `portmanteau` 用于计算两个列表的混合体：`xs` 和 `ys` 的混合体以 `xs` 作为前缀，以 `ys` 作为后缀，并且它们之间存在重叠部分。我们使用 `startsWith xs ys` 来测试 `ys` 是否以 `xs` 作为前缀。 -/

def startsWith : List ℕ → List ℕ → Bool
  | x :: xs, []      => false
  | [],      ys      => true
  | x :: xs, y :: ys => x = y && startsWith xs ys

#eval startsWith [1, 2] [1, 2, 3]
#eval startsWith [1, 2, 3] [1, 2]

def portmanteau : List ℕ → List ℕ → List (List ℕ)
| [],      ys => []
| x :: xs, ys =>
  List.map (List.cons x) (portmanteau xs ys) ++
  (if startsWith (x :: xs) ys then [ys] else [])

/- 以下是一些混成词的例子： -/

#eval portmanteau [0, 1, 2, 3] [2, 3, 4]
#eval portmanteau [0, 1] [2, 3, 4]
#eval portmanteau [0, 1, 2, 1, 2] [1, 2, 1, 2, 3, 4]

/- 1.2 （1个附加分）。将 `portmanteau` 程序从 `List` 单子转换为 `Nondet` 单子。

### 翻译说明：
- **portmanteau**：在编程上下文中，通常指一个组合词或混合词的程序，这里保留原文。
- **List monad**：列表单子，是函数式编程中的一个概念，用于处理列表的上下文计算。
- **Nondet monad**：非确定性单子，用于表示非确定性计算，通常用于搜索或回溯算法中。

### 翻译后的内容：
1.2 （1个附加分）。将 `portmanteau` 程序从 `List` 单子转换为 `Nondet` 单子。 -/

def nondetPortmanteau : List ℕ → List ℕ → Nondet (List ℕ) :=
  sorry


/- ## 问题 2（5 分 + 1 分附加分）：非确定性，指称语义

2.1（2 分）。为 `Nondet` 提供一个指称语义，将其映射到所有结果的 `List` 中。`pure` 返回一个结果，`fail` 返回零个结果，而 `choice` 则组合两个选项的结果。 -/

def listSem {α : Type} : Nondet α → List α :=
  sorry

/- 请检查以下代码行是否与 `portmanteau` 的输出相同（如果您已回答了问题 1.2）： -/

#reduce listSem (nondetPortmanteau [0, 1, 2, 3] [2, 3, 4])
#reduce listSem (nondetPortmanteau [0, 1] [2, 3, 4])
#reduce listSem (nondetPortmanteau [0, 1, 2, 1, 2] [1, 2, 1, 2, 3, 4])

/- 2.2（3分）。通常，我们并不关心获取所有结果，而只关心第一个成功的结果。请为`Nondet`提供一个语义，使其能够生成第一个成功的结果（如果有的话）。你的解决方案*不应*使用`listSem`。 -/

noncomputable def optionSem {α : Type} : Nondet α → Option α :=
  sorry

/- 2.3 （1个附加分）。证明以下定理 `List_Option_compat`，表明你定义的两种语义是兼容的。

`List.head?` 返回一个列表的头部，并将其包装在 `Option.some` 中，如果列表为空则返回 `Option.none`。它对应于我们在第5讲中称为 `headOpt` 的函数。 -/

theorem List_Option_compat {α : Type} :
    ∀na : Nondet α, optionSem na = List.head? (listSem na) :=
  sorry

end Nondet

end LoVe
