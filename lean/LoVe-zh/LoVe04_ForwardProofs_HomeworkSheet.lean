/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe 作业 4（10 分）：正向证明

将占位符（例如，`:= sorry`）替换为您的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1（4 分）：逻辑谜题

考虑以下战术证明： -/

theorem about_Impl :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- 1.1 （2分）。再次证明相同的定理，这次通过提供一个证明项来完成。

提示：有一个简单的方法。 -/

theorem about_Impl_term :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  sorry

/- 1.2 （2分）。再次证明相同的定理，这次通过提供一个结构化的证明，使用 `fix`、`assume` 和 `show`。 -/

theorem about_Impl_struct :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  sorry


/- ## 问题 2（6 分）：连接词与量词

2.1（3 分）。提供一个结构化的证明，证明在 `∀` 量词下 `∨` 的可交换性，仅使用 `∀`、`∨` 和 `↔` 的引入和消解规则，不使用其他定理。 -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
    (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  sorry

/- 2.2 (3 分). 在第三讲的练习中，我们已经证明或陈述了 `ExcludedMiddle`、`Peirce` 和 `DoubleNegation` 之间六种可能蕴含关系中的三种。利用我们已经掌握的三个定理，通过结构化证明，证明剩下的三种蕴含关系。 -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

theorem Peirce_of_DN :
    DoubleNegation → Peirce :=
  sorry

theorem EM_of_Peirce :
    Peirce → ExcludedMiddle :=
  sorry

theorem dn_of_em :
    ExcludedMiddle → DoubleNegation :=
  sorry

end BackwardProofs

end LoVe
