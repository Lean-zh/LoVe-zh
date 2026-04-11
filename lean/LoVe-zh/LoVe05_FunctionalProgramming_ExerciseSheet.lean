/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe04_ForwardProofs_Demo


/- # LoVe 练习 5：函数式编程

将占位符（例如，`:= sorry`）替换为你的解决方案。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1：列表的反转

我们定义了一个基于累加器的 `reverse` 变体。第一个参数 `as` 作为累加器使用。这个定义是**尾递归**的，意味着编译器和解释器可以轻松地优化掉递归，从而生成更高效的代码。 -/

def reverseAccu {α : Type} : List α → List α → List α
  | as, []      => as
  | as, x :: xs => reverseAccu (x :: as) xs

/- 1.1. 我们的意图是使 `reverseAccu [] xs` 等于 `reverse xs`。但如果我们开始进行归纳，很快会发现归纳假设不够强。首先证明以下推广（使用 `induction` 策略或模式匹配）： -/

theorem reverseAccu_Eq_reverse_append {α : Type} :
    ∀as xs : List α, reverseAccu as xs = reverse xs ++ as :=
  sorry

/- 1.2. 推导所需方程。 -/

theorem reverseAccu_eq_reverse {α : Type} (xs : List α) :
    reverseAccu [] xs = reverse xs :=
  sorry

/- 1.3. 证明以下性质。

提示：可以使用一行无归纳法的证明。 -/

theorem reverseAccu_reverseAccu {α : Type} (xs : List α) :
    reverseAccu [] (reverseAccu [] xs) = xs :=
  sorry

/- 1.4. 通过结构归纳法证明以下定理，作为“书面”证明。这是一个很好的练习，可以帮助你更深入地理解结构归纳法的工作原理（也是为期末考试做准备的好练习）。

**定理** `reverseAccu_Eq_reverse_append {α : Type}`：
  ∀as xs : list α, reverseAccu as xs = reverse xs ++ as

**书面证明指南**：

我们期望详细、严谨的数学证明。你可以使用标准的数学符号或Lean的结构化命令（例如，`assume`、`have`、`show`、`calc`）。你也可以使用战术证明（例如，`intro`、`apply`），但请注明一些中间目标，以便我们能够理解推理的链条。

主要的证明步骤，包括归纳法的应用和归纳假设的调用，必须明确陈述。对于归纳证明的每个情况，你必须列出所假设的归纳假设（如果有的话）以及要证明的目标。对应于`rfl`或`simp`的次要证明步骤，如果你认为它们对人类来说是显而易见的，则无需进一步解释，但你应该说明它们依赖于哪些关键定理。每当你使用函数定义时，应该明确说明。

---

**证明**：

我们将通过结构归纳法证明该定理。给定类型为`α`的列表`as`和`xs`，我们需要证明：
```
reverseAccu as xs = reverse xs ++ as
```

**归纳基础**：当`xs`为空列表`[]`时，我们需要证明：
```
reverseAccu as [] = reverse [] ++ as
```
根据`reverseAccu`的定义，`reverseAccu as [] = as`。同时，`reverse [] = []`，因此`reverse [] ++ as = [] ++ as = as`。因此，基础情况成立。

**归纳步骤**：假设对于某个列表`xs`，归纳假设成立，即：
```
reverseAccu as xs = reverse xs ++ as
```
我们需要证明对于`x :: xs`（即`xs`前添加一个元素`x`），以下等式成立：
```
reverseAccu as (x :: xs) = reverse (x :: xs) ++ as
```
根据`reverseAccu`的定义，`reverseAccu as (x :: xs) = reverseAccu (x :: as) xs`。根据归纳假设，我们有：
```
reverseAccu (x :: as) xs = reverse xs ++ (x :: as)
```
另一方面，`reverse (x :: xs) = reverse xs ++ [x]`，因此：
```
reverse (x :: xs) ++ as = (reverse xs ++ [x]) ++ as = reverse xs ++ ([x] ++ as) = reverse xs ++ (x :: as)
```
因此，我们得到：
```
reverseAccu as (x :: xs) = reverse (x :: xs) ++ as
```
归纳步骤成立。

综上所述，通过结构归纳法，我们证明了：
```
∀as xs : list α, reverseAccu as xs = reverse xs ++ as
```
证毕。

---

**关键点**：
- 在归纳步骤中，我们使用了`reverseAccu`的递归定义。
- 在归纳假设的应用中，我们依赖于`reverse`函数的定义及其性质。
- 在证明过程中，我们明确使用了列表的连接操作`++`的结合律。 -/

-- 请在此处输入您的纸质证明

/- ## 问题2：删除与获取

`drop` 函数用于从列表的前端移除前 `n` 个元素。 -/

def drop {α : Type} : ℕ → List α → List α
  | 0,     xs      => xs
  | _ + 1, []      => []
  | m + 1, _ :: xs => drop m xs

/- 2.1. 定义 `take` 函数，该函数返回一个列表，该列表由原列表前 `n` 个元素组成。

为了避免在证明过程中出现意外情况，我们建议您遵循与上述 `drop` 函数相同的递归模式。 -/

def take {α : Type} : ℕ → List α → List α :=
  sorry

#eval take 0 [3, 7, 11]   -- 预期：[]#eval take 1 [3, 7, 11]   -- 预期值：[3]#eval take 2 [3, 7, 11]   -- 预期值：[3, 7]#eval take 3 [3, 7, 11]   -- 预期值：[3, 7, 11]#eval take 4 [3, 7, 11]   -- 预期值：[3, 7, 11]
#eval take 2 ["a", "b", "c"]   -- 预期值：["a", "b"]
/- 2.2 使用`归纳法`或模式匹配证明以下定理。
请注意，由于`@[simp]`属性的作用，它们已被注册为简化规则。 -/

@[simp] theorem drop_nil {α : Type} :
    ∀n : ℕ, drop n ([] : List α) = [] :=
  sorry

@[simp] theorem take_nil {α : Type} :
    ∀n : ℕ, take n ([] : List α) = [] :=
  sorry

/- 2.3. 按照 `drop` 和 `take` 的递归模式来证明以下定理。换句话说，对于每个定理，应该有三种情况，第三种情况需要调用归纳假设。

提示：注意在 `drop_drop` 定理中有三个变量（但 `drop` 只有两个参数）。对于第三种情况，`← add_assoc` 可能会派上用场。 -/

theorem drop_drop {α : Type} :
    ∀(m n : ℕ) (xs : List α), drop n (drop m xs) = drop (n + m) xs
  | 0,     n, xs      => by rfl
  -- 请在此处补充两个缺失的案例
theorem take_take {α : Type} :
    ∀(m : ℕ) (xs : List α), take m (take m xs) = take m xs :=
  sorry

theorem take_drop {α : Type} :
    ∀(n : ℕ) (xs : List α), take n xs ++ drop n xs = xs :=
  sorry


/- ## 问题 3：一种类型的项

3.1. 定义一个归纳类型，对应于无类型 λ-演算的项，其语法如下：

    Term  ::=  `var` String        -- 变量（例如，`x`）
            |  `lam` String Term   -- λ-表达式（例如，`λx. t`）
            |  `app` Term Term     -- 应用（例如，`t u`）

### 翻译说明：
- **Term**：项
- **var**：变量
- **lam**：λ-表达式
- **app**：应用
- **String**：字符串
- **inductive type**：归纳类型
- **untyped λ-calculus**：无类型 λ-演算

该问题要求定义一个归纳类型来表示无类型 λ-演算中的项，这些项可以是变量、λ-表达式或应用。 -/`Term` 的文本表示注册为 `Repr` 类型类的一个实例。确保提供足够的括号以保证输出的无歧义性。 -/

def Term.repr : Term → String
-- 请将以下技术文档翻译成中文，保持专业术语准确：

**原文：**

The system architecture is designed to support high availability and scalability. It consists of multiple layers, including the presentation layer, business logic layer, and data access layer. The presentation layer is responsible for handling user interactions and rendering the user interface. The business logic layer processes the core functionalities and enforces business rules. The data access layer manages the interaction with the database, ensuring data integrity and security.

**翻译：**

系统架构设计旨在支持高可用性和可扩展性。它由多个层次组成，包括表示层、业务逻辑层和数据访问层。表示层负责处理用户交互并渲染用户界面。业务逻辑层处理核心功能并执行业务规则。数据访问层管理与数据库的交互，确保数据的完整性和安全性。
instance Term.Repr : Repr Term :=
  { reprPrec := fun t prec ↦ Term.repr t }

/- 3.3 （**可选**）。测试你的文本表示。以下命令应打印类似 `(λx. ((y x) x)` 的内容。 -/

#eval (Term.lam "x" (Term.app (Term.app (Term.var "y") (Term.var "x"))
    (Term.var "x")))

end LoVe
