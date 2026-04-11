/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe 作业 1（10 分）：类型与项

将占位符（例如，`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1（6 分）：术语

我们首先声明四个新的不透明类型。 -/

opaque α : Type
opaque β : Type
opaque γ : Type
opaque δ : Type

/- 1.1 (4 分). 请通过提供具有预期类型的术语来完成以下定义。

请为绑定变量使用合理的名称，例如 `a : α`、`b : β`、`c : γ`。

提示：在《Hitchhiker's Guide》的第 1.4 节中描述了一种系统化的方法。如该节所述，您可以在构造术语时使用 `_` 作为占位符。将鼠标悬停在 `_` 上时，您将看到当前的逻辑上下文。 -/

def B : (α → β) → (γ → α) → γ → β :=
  sorry

def S : (α → β → γ) → (α → β) → α → γ :=
  sorry

def moreNonsense : ((α → β) → γ → δ) → γ → β → δ :=
  sorry

def evenMoreNonsense : (α → β) → (α → γ) → α → β → γ :=
  sorry

/- 1.2 （2分）。完成以下定义。

这个看起来更难一些，但如果你按照《Hitchhiker's Guide》中描述的程序操作，应该会相当直接。

注意：Peirce的发音类似于英语单词“purse”。 -/

def weakPeirce : ((((α → β) → α) → α) → β) → β :=
  sorry

/- ## 问题 2（4 分）：类型推导

请使用 ASCII 或 Unicode 艺术展示你上面定义的 `B` 的类型推导过程。你可能会发现字符 `–`（用于绘制水平线）和 `⊢` 很有用。

可以自由引入缩写，以避免重复较大的上下文 `C`。 -/

-- 请将您的解决方案写在这里。
end LoVe
