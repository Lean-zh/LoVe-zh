/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe 作业 3（10 分）：逆向证明

将占位符（例如，`:= sorry`）替换为您的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## 问题 1（5 分）：连接词与量词

1.1（4 分）。使用基本策略（如 `intro`、`apply` 和 `exact`）完成以下证明。

提示：在《Hitchhiker's Guide》第 3.3 节的末尾描述了一些执行此类证明的策略。 -/

theorem B (a b c : Prop) :
    (a → b) → (c → a) → c → b :=
  sorry

theorem S (a b c : Prop) :
    (a → b → c) → (a → b) → a → c :=
  sorry

theorem more_nonsense (a b c d : Prop) :
    ((a → b) → c → d) → c → b → d :=
  sorry

theorem even_more_nonsense (a b c : Prop) :
    (a → b) → (a → c) → a → b → c :=
  sorry

/- 1.2 （1 分）。使用基本策略证明以下定理。 -/

theorem weak_peirce (a b : Prop) :
    ((((a → b) → a) → a) → b) → b :=
  sorry


/- ## 问题 2（5 分）：逻辑连接词

2.1（1 分）。使用基本策略证明以下关于双重否定的性质。

提示：

* 请记住，`¬ a` 被定义为 `a → False`。如果这对你有帮助，你可以从调用 `simp [Not]` 开始。

* 在证明的关键点，你需要应用 `False` 的消解规则。 -/

theorem herman (a : Prop) :
    ¬¬ (¬¬ a → a) :=
  sorry

/- 2.2 （2分）。证明我们经典公理蕴含链中缺失的一环。

提示：

* 快速找到 `DoubleNegation`（双重否定）和 `ExcludedMiddle`（排中律）定义的一种方法是：

  1. 按住 Control 键（在 Linux 和 Windows 上）或 Command 键（在 macOS 上）；
  2. 将光标移动到标识符 `DoubleNegation` 或 `ExcludedMiddle` 上；
  3. 点击该标识符。

* 你可以使用 `rw DoubleNegation` 来展开 `DoubleNegation` 的定义，其他定义也类似。

* 你需要对 `a ∨ ¬ a` 应用双重否定假设。在某些时候，你还需要使用 `∨` 的左右引入规则。 -/

#check DoubleNegation
#check ExcludedMiddle

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle :=
  sorry

/- 2.3 (2分). 我们已经证明了`ExcludedMiddle`、`Peirce`和`DoubleNegation`之间六种可能蕴含关系中的三种。请陈述并证明剩下的三种蕴含关系，利用我们已经掌握的三个定理。 -/

#check Peirce_of_EM
#check DN_of_Peirce
#check EM_of_DN

-- 请在此处输入您的解决方案。
end BackwardProofs

end LoVe
