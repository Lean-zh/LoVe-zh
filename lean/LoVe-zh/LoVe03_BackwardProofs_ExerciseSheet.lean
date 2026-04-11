/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe 练习 3：逆向证明

将占位符（例如，`:= sorry`）替换为您的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## 问题1：连接词与量词

1.1 使用基本策略完成以下证明。

提示：在《Hitchhiker's Guide》第3.3节的末尾描述了一些完成此类证明的策略。 -/

theorem I (a : Prop) :
    a → a :=
  sorry

theorem K (a b : Prop) :
    a → b → b :=
  sorry

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  sorry

theorem proj_fst (a : Prop) :
    a → a → a :=
  sorry

/- 请提供与`proj_fst`不同的答案： -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  sorry

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  sorry

/- 1.2. 使用基本策略证明逆否命题规则。 -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  sorry

/- 1.3. 使用基本策略证明 `∀` 对 `∧` 的分配性。

提示：这个练习较为复杂，尤其是从右到左的方向。可能需要一些前向推理，类似于课程中 `and_swap_braces` 的证明。 -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  sorry


/- ## 问题2：自然数

2.1. 证明以下关于第一讲中定义的 `mul` 运算符第一个参数的递归方程。 -/

#check mul

theorem mul_zero (n : ℕ) :
    mul 0 n = 0 :=
  sorry

#check add_succ
theorem mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n :=
  sorry

/- 2.2. 使用 `induction` 策略证明乘法的交换律和结合律。请谨慎选择归纳变量。 -/

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
  sorry

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  sorry

/- 2.3. 使用 `rw` 证明 `mul_add` 的对称变体。要在特定位置应用交换律，可以通过传递一些参数来实例化该规则（例如，`mul_comm _ l`）。 -/

theorem add_mul (l m n : ℕ) :
    mul (add l m) n = add (mul n l) (mul n m) :=
  sorry


/- ## 问题 3（**可选**）：直觉主义逻辑

直觉主义逻辑通过假设一个经典公理扩展为经典逻辑。选择公理有多种可能性。在本问题中，我们关注三种不同公理的逻辑等价性： -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- 在以下证明中，请避免使用Lean的`Classical`命名空间中的定理。

3.1 (**可选**). 使用策略证明以下蕴含关系。

提示：你将需要使用`Or.elim`和`False.elim`。你可以使用`rw [ExcludedMiddle]`来展开`ExcludedMiddle`的定义，对于`Peirce`也可以类似操作。 -/

theorem Peirce_of_EM :
    ExcludedMiddle → Peirce :=
  sorry

/- 3.2 （**可选**）。使用策略证明以下蕴含关系。 -/

theorem DN_of_Peirce :
    Peirce → DoubleNegation :=
  sorry

/- 我们将剩下的含义留给作业： -/

namespace SorryTheorems

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle :=
  sorry

end SorryTheorems

end BackwardProofs

end LoVe
