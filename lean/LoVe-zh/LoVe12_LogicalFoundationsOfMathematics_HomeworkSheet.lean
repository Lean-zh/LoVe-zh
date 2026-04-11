/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe 作业 12（10 分 + 2 分附加分）：
# 数学的逻辑基础

请将占位符（例如，`:= sorry`）替换为您的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1（8 分）：偶数作为子类型

通常，表示偶数自然数最方便的方法是使用更大的类型 `ℕ`，该类型也包括奇数自然数。如果我们只想对偶数 `n` 进行量化，可以在定理陈述中添加一个假设 `Even n`。

另一种方法是在类型中编码偶数性，使用子类型。我们将探讨这种方法。

1.1（1 分）。使用第 5 讲演示中引入的 `Even` 谓词，定义偶数自然数的类型 `Eveℕ`。 -/

#print Even

def Eveℕ : Type :=
  sorry

/- 1.2 （1 分）。请证明以下关于 `Even` 谓词的定理。你需要用它来回答问题 1.3。

提示：定理 `add_assoc` 和 `add_comm` 可能会有所帮助。 -/

theorem Even.add {m n : ℕ} (hm : Even m) (hn : Even n) :
    Even (m + n) :=
  sorry

/- 1.3 （2分）。通过填写 `sorry` 占位符来定义偶数的零和加法。 -/

def Eveℕ.zero : Eveℕ :=
  sorry

def Eveℕ.add (m n : Eveℕ) : Eveℕ :=
  sorry

/- 1.4 （4分）。证明偶数的加法满足交换律和结合律，并且0是其单位元。 -/

theorem Eveℕ.add_comm (m n : Eveℕ) :
    Eveℕ.add m n = Eveℕ.add n m :=
  sorry

theorem Eveℕ.add_assoc (l m n : Eveℕ) :
    Eveℕ.add (Eveℕ.add l m) n = Eveℕ.add l (Eveℕ.add m n) :=
  sorry

theorem Eveℕ.add_iden_left (n : Eveℕ) :
    Eveℕ.add Eveℕ.zero n = n :=
  sorry

theorem Eveℕ.add_iden_right (n : Eveℕ) :
    Eveℕ.add n Eveℕ.zero = n :=
  sorry


/- ## 问题 2（2 分 + 2 分附加分）：希尔伯特选择

2.1（2 分附加分）。证明以下定理。

提示：

* 一个好的开始方法是根据 `∃n, f n < x` 是否为真进行情况区分。

* 定理 `le_of_not_gt` 可能有用。 -/

theorem exists_minimal_arg_helper (f : ℕ → ℕ) :
    ∀x m, f m = x → ∃n, ∀i, f n ≤ f i
  | x, m, eq =>
    by
      sorry, sorry

/- 现在，这个有趣的定理出现了： -/

theorem exists_minimal_arg (f : ℕ → ℕ) :
    ∃n : ℕ, ∀i : ℕ, f n ≤ f i :=
  exists_minimal_arg_helper f _ 0 (by rfl)

/- 2.2 （1分）。利用你在讲座中学到的关于希尔伯特选择的知识，定义以下函数，该函数返回 `f` 的像中最小元素的（或一个）索引。 -/

noncomputable def minimal_arg (f : ℕ → ℕ) : ℕ :=
  sorry

/- 2.3 （1分）。证明以下关于你定义的特性定理。 -/

theorem minimal_arg_spec (f : ℕ → ℕ) :
    ∀i : ℕ, f (minimal_arg f) ≤ f i :=
  sorry

end LoVe
