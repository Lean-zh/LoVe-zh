/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe 练习 6：归纳谓词

将占位符（例如，`:= sorry`）替换为您的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：偶数和奇数

`Even`（偶数）谓词对于偶数为`True`（真），对于奇数为`False`（假）。 -/

#check Even

/- 我们将 `Odd` 定义为 `Even` 的否定： -/

def Odd (n : ℕ) : Prop :=
  ¬ Even n

/- 1.1. 证明1是奇数，并将此事实注册为simp规则。

提示：`cases` 或 `induction` 对于处理形如 `Even …` 的假设非常有用。 -/

@[simp] theorem Odd_1 :
    Odd 1 :=
  sorry

/- 1.2. 证明3和5是奇数。 -/

-- 请提供需要翻译的技术文档内容，我将为您进行准确且专业的翻译。
/- 1.3. 通过结构归纳法完成以下证明。 -/

theorem Even_two_times :
    ∀m : ℕ, Even (2 * m)
  | 0     => Even.zero
  | m + 1 =>
    sorry


/- ## 问题2：网球比赛

回顾演示中的网球比分归纳类型： -/

#check Score

/- 2.1. 定义一个归纳谓词，如果服务器领先于接收器，则返回 `True`，否则返回 `False`。 -/

inductive ServAhead : Score → Prop
  -- 在此处输入缺失的案例
/- 2.2. 通过证明以下定理来验证您的谓词定义。 -/

theorem ServAhead_vs {m n : ℕ} (hgt : m > n) :
    ServAhead (Score.vs m n) :=
  sorry

theorem ServAhead_advServ :
    ServAhead Score.advServ :=
  sorry

theorem not_ServAhead_advRecv :
    ¬ ServAhead Score.advRecv :=
  sorry

theorem ServAhead_gameServ :
    ServAhead Score.gameServ :=
  sorry

theorem not_ServAhead_gameRecv :
    ¬ ServAhead Score.gameRecv :=
  sorry

/- 2.3. 将上述定理陈述与您的定义进行比较。您观察到了什么？ -/

-- 请提供需要翻译的技术文档内容，我将为您进行准确且专业的翻译。

/- ## 问题3：二叉树

3.1. 证明 `IsFull_mirror` 的逆命题。你可以利用已经证明的定理（例如，`IsFull_mirror`、`mirror_mirror`）。 -/

#check IsFull_mirror
#check mirror_mirror

theorem mirror_IsFull {α : Type} :
    ∀t : Tree α, IsFull (mirror t) → IsFull t :=
  sorry

/- 3.2. 在二叉树上定义一个 `map` 函数，类似于 `List.map`。 -/

def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β :=
  sorry

/- 3.3 通过分情况证明以下定理。 -/

theorem Tree.map_eq_empty_iff {α β : Type} (f : α → β) :
    ∀t : Tree α, Tree.map f t = Tree.nil ↔ t = Tree.nil :=
  sorry

/- 3.4 （**可选**）。通过规则归纳法证明以下定理。 -/

theorem map_mirror {α β : Type} (f : α → β) :
    ∀t : Tree α, IsFull t → IsFull (Tree.map f t) :=
  sorry

end LoVe
