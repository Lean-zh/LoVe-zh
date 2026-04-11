/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe12_LogicalFoundationsOfMathematics_Demo


/- # LoVe 练习 12：数学的逻辑基础

将占位符（例如，`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：向量作为子类型

回顾演示中向量的定义： -/

#check Vector

/- 以下函数将两个整数列表按元素逐个相加。如果其中一个列表比另一个长，则较长列表的尾部将被忽略。 -/

def List.add : List ℤ → List ℤ → List ℤ
  | [],      []      => []
  | x :: xs, y :: ys => (x + y) :: List.add xs ys
  | [],      y :: ys => []
  | x :: xs, []      => []

/- 1.1. 证明如果列表的长度相同，则生成的列表也具有相同的长度。 -/

theorem List.length_add :
    ∀xs ys, List.length xs = List.length ys →
      List.length (List.add xs ys) = List.length xs
  | [], [] =>
    sorry
  | x :: xs, y :: ys =>
    sorry
  | [], y :: ys =>
    sorry
  | x :: xs, [] =>
    sorry

/- 1.2. 使用 `List.add` 和 `List.length_add` 定义向量的逐分量加法。 -/

def Vector.add {n : ℕ} : Vector ℤ n → Vector ℤ n → Vector ℤ n :=
  sorry

/- 1.3. 证明 `List.add` 和 `Vector.add` 是可交换的。

**翻译说明：**
- **List.add** 和 **Vector.add** 是编程中的方法名，通常表示向列表或向量中添加元素的操作。在翻译时保留了原文的术语，以确保技术准确性。
- **commutative** 翻译为“可交换的”，这是数学和计算机科学中的标准术语，表示操作的顺序不影响最终结果。 -/

theorem List.add.comm :
    ∀xs ys, List.add xs ys = List.add ys xs :=
  sorry

theorem Vector.add.comm {n : ℕ} (u v : Vector ℤ n) :
    Vector.add u v = Vector.add v u :=
  sorry


/- ## 问题2：作为商的整数

回顾一下讲座中关于整数的构造，不要与Lean预定义的类型`Int`（即`ℤ`）混淆： -/

#check Int.Setoid
#check Int.Setoid_Iff
#check Int

/- 2.1. 在这些整数上定义取反操作。注意，如果 `(p, n)` 表示一个整数，那么 `(n, p)` 表示它的取反。 -/

def Int.neg : Int → Int :=
  sorry

/- 2.2 证明以下关于否定的定理。 -/

theorem Int.neg_eq (p n : ℕ) :
    Int.neg ⟦(p, n)⟧ = ⟦(n, p)⟧ :=
  sorry

theorem int.neg_neg (a : Int) :
    Int.neg (Int.neg a) = a :=
  sorry

end LoVe
