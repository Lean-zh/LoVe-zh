/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe 作业 6（10 分）：归纳谓词

将占位符（例如，`:= sorry`）替换为您的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1（4 分）：一种术语类型

回顾练习 5 中问题 3 的术语类型： -/

inductive Term : Type
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term

/- 1.1 (2 分). 定义一个归纳谓词 `IsLam`，如果其参数的形式为 `Term.lam …`，则返回 `True`，否则返回 `False`。 -/

-- 请输入您的定义
/- 1.2 （2 分）。通过证明以下定理来验证你对问题 1.1 的答案： -/

theorem IsLam_lam (s : String) (t : Term) :
    IsLam (Term.lam s t) :=
  sorry

theorem not_IsLamVar (s : String) :
    ¬ IsLam (Term.var s) :=
  sorry

theorem not_IsLam_app (t u : Term) :
    ¬ IsLam (Term.app t u) :=
  sorry


/- ## 问题 2（6 分）：传递闭包

在数学中，集合 `A` 上的二元关系 `R` 的传递闭包 `R⁺` 可以定义为满足以下规则的最小解：

    （基础）对于所有 `a, b ∈ A`，如果 `a R b`，则 `a R⁺ b`；
    （递推）对于所有 `a, b, c ∈ A`，如果 `a R b` 且 `b R⁺ c`，则 `a R⁺ c`。

在 Lean 中，我们可以通过将集合 `A` 与类型 `α` 等同来定义这一概念，如下所示： -/

inductive TCV1 {α : Type} (R : α → α → Prop) : α → α → Prop
  | base (a b : α)   : R a b → TCV1 R a b
  | step (a b c : α) : R a b → TCV1 R b c → TCV1 R a c

/- 2.1 (2 分). 规则 `(step)` 通过向左侧添加链接，方便地扩展了传递链。另一种定义传递闭包 `R⁺` 的方法是使用以下右倾规则替换 `(step)`：

    (pets) 对于所有 `a, b, c ∈ A`，如果 `a R⁺ b` 且 `b R c`，则 `a R⁺ c`。

定义一个谓词 `TCV2`，以体现这种替代定义。 -/

-- 请在此处输入您的定义
/- 2.2 (2 分). 传递闭包 `R⁺` 的另一种定义可以使用以下对称规则，而不是 `(step)` 或 `(pets)`：

    (trans) 对于所有 `a, b, c ∈ A`，如果 `a R⁺ b` 且 `b R⁺ c`，则 `a R⁺ c`。

定义一个谓词 `TCV3`，以体现这种替代定义。 -/

-- 请输入您的定义
/- 2.3 （1分）。证明 `(step)` 也是关于 `TCV3` 的一个定理。 -/

theorem TCV3_step {α : Type} (R : α → α → Prop) (a b c : α) (rab : R a b)
      (tbc : TCV3 R b c) :
    TCV3 R a c :=
  sorry

/- 2.4 （1 分）。通过规则归纳法证明以下定理： -/

theorem TCV1_pets {α : Type} (R : α → α → Prop) (c : α) :
    ∀a b, TCV1 R a b → R b c → TCV1 R a c :=
  sorry

end LoVe
