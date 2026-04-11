/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe05_FunctionalProgramming_Demo


/- # LoVe 作业 5（10 分 + 2 分附加分）：函数式编程

将占位符（例如，`:= sorry`）替换为你的解决方案。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1（6分）：霍夫曼树

考虑以下类型的加权二叉树： -/

inductive HTree (α : Type)
  | leaf  : ℕ → α → HTree α
  | inner : ℕ → HTree α → HTree α → HTree α

/- 每个构造函数对应一种节点类型。`HTree.leaf` 节点存储一个数值权重和一个类型为 `α` 的标签，而 `HTree.inner` 节点存储一个数值权重、一个左子树和一个右子树。

1.1（1 分）。定义一个名为 `weight` 的多态 Lean 函数，该函数接受一个类型变量为 `α` 的树，并返回树根节点的权重部分： -/

def weight {α : Type} : HTree α → ℕ :=
  sorry

/- 1.2 （1 分）。定义一个名为 `unite` 的多态 Lean 函数，该函数接受两棵树 `l, r : HTree α`，并返回一棵新树，满足以下条件：(1) 其左子节点为 `l`；(2) 其右子节点为 `r`；(3) 其权重为 `l` 和 `r` 的权重之和。 -/

def unite {α : Type} : HTree α → HTree α → HTree α :=
  sorry

/- 1.3 （2分）。考虑以下 `insort` 函数，该函数将一个树 `u` 插入到一个按权重递增排序的树列表中，并保持排序不变。（如果输入列表未排序，结果不一定是有序的。） -/

def insort {α : Type} (u : HTree α) : List (HTree α) → List (HTree α)
  | []      => [u]
  | t :: ts => if weight u ≤ weight t then u :: t :: ts else t :: insort u ts

/- 证明将一棵树通过 `insort` 操作插入到列表中不会产生空列表：

在计算机科学中，`insort` 是一种将元素插入到已排序列表中的操作，同时保持列表的有序性。假设我们有一个已排序的列表 `L` 和一棵树 `T`，我们需要证明将 `T` 通过 `insort` 操作插入到 `L` 中不会导致结果为空列表。

首先，考虑 `insort` 操作的基本性质：它总是会在列表中添加一个元素（在本例中是树 `T`），而不会删除任何现有元素。因此，无论 `L` 的初始状态如何（即使 `L` 本身为空列表），`insort` 操作都会将 `T` 插入到 `L` 中，从而确保结果列表至少包含一个元素。

具体来说，如果 `L` 是空列表，`insort` 操作会将 `T` 插入到 `L` 中，生成一个只包含 `T` 的列表 `[T]`。如果 `L` 不为空，`insort` 操作会将 `T` 插入到适当的位置，生成一个包含 `L` 中所有元素以及 `T` 的新列表。

因此，无论 `L` 的初始状态如何，`insort` 操作都会确保结果列表至少包含一个元素，即 `T`。这证明了将一棵树通过 `insort` 操作插入到列表中不会产生空列表。

结论：`insort` 操作保证了列表的非空性，因此将一棵树插入到列表中不会产生空列表。 -/

theorem insort_Neq_nil {α : Type} (t : HTree α) :
    ∀ts : List (HTree α), insort t ts ≠ [] :=
  sorry

/- 1.4 （2分）。再次证明上述相同的性质，这次以“书面”证明的形式进行。请遵循练习中问题1.4给出的指导原则。 -/

-- 请在此处输入您的纸质证明

/- ## 问题 2（4 分 + 2 分附加分）：高斯求和公式

`sumUpToOfFun f n = f 0 + f 1 + ⋯ + f n` -/

def sumUpToOfFun (f : ℕ → ℕ) : ℕ → ℕ
  | 0     => f 0
  | m + 1 => sumUpToOfFun f m + f (m + 1)

/- 2.1 (2 分). 证明以下定理，该定理由卡尔·弗里德里希·高斯（Carl Friedrich Gauss）在学生时期发现。

提示：

* `mul_add` 和 `add_mul` 定理可能有助于推理乘法。

* 第 6 讲中介绍的 `linarith` 策略可能有助于推理加法。 -/

/- PAUL: 我在文件中没有看到任何关于 `linarith` 的引用。这是你在讲座中提到但没有在演示文件中提及的内容吗？值得在这里总结一下它是什么，或者参考指南。
实际上，我刚刚往前看了一下，第6章有一个注释。也许可以复制到这里？ -/

#check mul_add
#check add_mul

theorem sumUpToOfFun_eq :
    ∀m : ℕ, 2 * sumUpToOfFun (fun i ↦ i) m = m * (m + 1) :=
  sorry

/- 2.2 （2分）。证明 `sumUpToOfFun` 的以下性质。 -/

theorem sumUpToOfFun_mul (f g : ℕ → ℕ) :
    ∀n : ℕ, sumUpToOfFun (fun i ↦ f i + g i) n =
      sumUpToOfFun f n + sumUpToOfFun g n :=
  sorry

/- 2.3 （2个奖励分）。再次以“纸面”证明的形式证明 `sumUpToOfFun_mul`。
请遵循练习中问题1.4给出的指导原则。 -/

-- 请在此处输入您的纸质证明
end LoVe
