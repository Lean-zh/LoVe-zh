/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe13_BasicMathematicalStructures_Demo


/- # LoVe 练习 13：基本数学结构

将占位符（例如，`:= sorry`）替换为您的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：类型类

回顾我们在第5讲中引入的归纳类型 `Tree`： -/

#check Tree

/- 以下函数接收两棵树，并将第二棵树的副本附加到第一棵树的每个叶节点上。 -/

def Tree.graft {α : Type} : Tree α → Tree α → Tree α
  | Tree.nil,        u => u
  | Tree.node a l r, u =>
    Tree.node a (Tree.graft l u) (Tree.graft r u)

#reduce Tree.graft (Tree.node 1 Tree.nil Tree.nil)
  (Tree.node 2 Tree.nil Tree.nil)

/- 1.1. 通过对 `t` 进行结构归纳法，证明以下两个定理。 -/

theorem Tree.graft_assoc {α : Type} (t u v : Tree α) :
    Tree.graft (Tree.graft t u) v = Tree.graft t (Tree.graft u v) :=
  sorry

theorem Tree.graft_nil {α : Type} (t : Tree α) :
    Tree.graft t Tree.nil = t :=
  sorry

/- 1.2. 将 `Tree` 声明为 `AddMonoid` 的一个实例，并使用 `graft` 作为加法运算符。 -/

#print AddMonoid

instance Tree.AddMonoid {α : Type} : AddMonoid (Tree α) :=
  { add       :=
      sorry
    add_assoc :=
      sorry
    zero      :=
      sorry
    add_zero  :=
      sorry
    zero_add  :=
      sorry
    nsmul     := @nsmulRec (Tree α) (Zero.mk Tree.nil) (Add.mk Tree.graft)
  }

/- 1.3 （**可选**）。解释为什么带有 `graft` 作为加法操作的 `Tree` 不能被声明为 `AddGroup` 的实例。 -/

#print AddGroup

-- 请将以下技术文档翻译成中文，保持专业术语准确：

**输入您的解释内容**

---

**翻译：**

请将以下技术文档翻译成中文，保持专业术语准确：

**在此输入您的解释内容**

---

**说明：**
- 在翻译技术文档时，确保专业术语的准确性至关重要。例如，"API" 应翻译为 "应用程序编程接口"，"server" 应翻译为 "服务器" 等。
- 如果文档中包含代码或特定格式的内容，需保持原格式不变，仅对文本部分进行翻译。
- 翻译时应尽量保持原文的逻辑结构和表达方式，确保信息传递的准确性。
/- 1.4 （**可选**）。证明以下定理，说明为什么带有 `graft` 作为加法操作的 `Tree` 不构成一个 `AddGroup`。 -/

theorem Tree.add_left_neg_counterexample :
    ∃x : Tree ℕ, ∀y : Tree ℕ, Tree.graft y x ≠ Tree.nil :=
  sorry


/- ## 问题2：多重集与有限集

请回顾以下课堂中的定义： -/

#check Finset.elems
#check List.elems

/- 2.1. 证明在镜像一棵树时，节点的有限集合不会发生变化。 -/

theorem Finset.elems_mirror (t : Tree ℕ) :
    Finset.elems (mirror t) = Finset.elems t :=
  sorry

/- 2.2. 通过提供一个树 `t`，使得 `List.elems t ≠ List.elems (mirror t)`，证明该性质不适用于节点列表。

如果你定义了一个合适的反例，下面的证明将会成功。 -/

def rottenTree : Tree ℕ :=
  sorry

#eval List.elems rottenTree
#eval List.elems (mirror rottenTree)

theorem List.elems_mirror_counterexample :
    ∃t : Tree ℕ, List.elems t ≠ List.elems (mirror t) :=
  by
    apply Exists.intro rottenTree
    simp [List.elems]

end LoVe
