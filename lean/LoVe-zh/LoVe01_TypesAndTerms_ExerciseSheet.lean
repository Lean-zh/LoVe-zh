/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe01_TypesAndTerms_Demo


/- # LoVe 练习 1：类型与项

将占位符（例如，`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1：术语

请通过替换 `sorry` 标记为预期类型的术语来完成以下定义。

提示：在《Hitchhiker's Guide》的第 1.4 节中描述了一种系统化的方法来完成此操作。如该节所述，您可以在构造术语时使用 `_` 作为占位符。将鼠标悬停在 `_` 上时，您将看到当前的逻辑上下文。 -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a b ↦ a

def C : (α → β → γ) → β → α → γ :=
  sorry

def projFst : α → α → α :=
  sorry

/- 请提供与 `projFst` 不同的答案。 -/

def projSnd : α → α → α :=
  sorry

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  sorry


/- ## 问题2：类型推导

展示你在上面定义的 `C` 的类型推导过程，可以使用纸笔或ASCII/Unicode艺术。你可能会发现字符 `–`（用于绘制水平线）和 `⊢` 很有用。 -/

-- 请将您的解决方案写在评论中或纸上。
end LoVe
