/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe04_ForwardProofs_Demo
import LoVe.LoVe05_FunctionalProgramming_Demo


/- # LoVe 演示 6：归纳谓词

**归纳谓词**，或称归纳定义的命题，是一种方便的方式来指定类型为 `⋯ → Prop` 的函数。它们让人联想到形式系统和逻辑编程语言中的 Horn 子句，尤其是 Prolog。

对 Lean 的一种可能的看法是：

    Lean = 函数式编程 + 逻辑编程 + 更多逻辑 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 入门示例

### 偶数

数学家通常将集合定义为满足某些条件的最小集合。例如：

    偶数自然数集合 `E` 被定义为满足以下规则的最小集合：(1) `0 ∈ E` 且 (2) 对于每一个 `k ∈ ℕ`，如果 `k ∈ E`，则 `k + 2 ∈ E`。

在 Lean 中，我们可以定义相应的“是偶数”谓词如下： -/

inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀k : ℕ, Even k → Even (k + 2)

/- 这应该看起来很熟悉。我们使用了相同的语法，只是用 `Type` 代替了 `Prop`，用于归纳类型。

上述命令引入了一个新的一元谓词 `Even`，以及两个构造器 `Even.zero` 和 `Even.add_two`，它们可以用来构建证明项。得益于归纳定义的“无冗余”保证，`Even.zero` 和 `Even.add_two` 是构造 `Even` 证明的唯二方式。

根据 PAT 原则，`Even` 可以被视为一个归纳类型，其值即为证明项。 -/

theorem Even_4 :
    Even 4 :=
  have Even_0 : Even 0 :=
    Even.zero
  have Even_2 : Even 2 :=
    Even.add_two _ Even_0
  show Even 4 from
    Even.add_two _ Even_2

/- 为什么我们不能简单地递归定义 `Even` 呢？确实，为什么不呢？ -/

def evenRec : ℕ → Bool
  | 0     => true
  | 1     => false
  | k + 2 => evenRec k

/- 这两种风格各有优缺点。

递归版本要求我们指定一个错误情况（1），并且需要我们关注终止条件。另一方面，由于它是计算性的，它与 `rfl`、`simp`、`#reduce` 和 `#eval` 配合得很好。

归纳版本通常被认为更加抽象和优雅。每条规则都是独立陈述的。

定义 `Even` 的另一种方式是非递归定义： -/

def evenNonrec (k : ℕ) : Prop :=
  k % 2 = 0

/- 数学家可能会认为这是最令人满意的定义。
但归纳版本是一个方便、直观的示例，它是许多实际归纳定义的典型代表。

### 网球比赛

转换系统由转换规则组成，这些规则共同指定了一个连接“之前”状态和“之后”状态的二元谓词。
作为一个简单的转换系统示例，我们考虑网球比赛中从0-0开始的可能转换。 -/

inductive Score : Type where
  | vs       : ℕ → ℕ → Score
  | advServ  : Score
  | advRecv  : Score
  | gameServ : Score
  | gameRecv : Score

infixr:50 " – " => Score.vs

inductive Step : Score → Score → Prop where
  | serv_0_15     : ∀n, Step (0–n) (15–n)
  | serv_15_30    : ∀n, Step (15–n) (30–n)
  | serv_30_40    : ∀n, Step (30–n) (40–n)
  | serv_40_game  : ∀n, n < 40 → Step (40–n) Score.gameServ
  | serv_40_adv   : Step (40–40) Score.advServ
  | serv_adv_40   : Step Score.advServ (40–40)
  | serv_adv_game : Step Score.advServ Score.gameServ
  | recv_0_15     : ∀n, Step (n–0) (n–15)
  | recv_15_30    : ∀n, Step (n–15) (n–30)
  | recv_30_40    : ∀n, Step (n–30) (n–40)
  | recv_40_game  : ∀n, n < 40 → Step (n–40) Score.gameRecv
  | recv_40_adv   : Step (40–40) Score.advRecv
  | recv_adv_40   : Step Score.advRecv (40–40)
  | recv_adv_game : Step Score.advRecv Score.gameRecv

infixr:45 " ↝ " => Step

/- 请注意，虽然 `Score.vs` 允许任意数字作为参数，但 `Step` 构造函数的定义确保了只有有效的网球比分才能从 `0–0` 开始生成。

我们可以提出并正式回答以下问题：比分是否有可能再次回到 `0–0`？ -/

theorem no_Step_to_0_0 (s : Score) :
    ¬ s ↝ 0–0 :=
  by
    intro h
    cases h


/- ### 自反传递闭包

我们最后一个介绍性示例是关系 `R` 的自反传递闭包，它被建模为一个二元谓词 `Star R`。 -/

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
where
  | base (a b : α)    : R a b → Star R a b
  | refl (a : α)      : Star R a a
  | trans (a b c : α) : Star R a b → Star R b c → Star R a c

/- 第一条规则将 `R` 嵌入到 `Star R` 中。第二条规则实现了自反闭包。第三条规则实现了传递闭包。

这个定义非常优雅。如果你对此有所怀疑，可以尝试将 `Star` 实现为一个递归函数： -/

def starRec {α : Type} (R : α → α → Bool) :
  α → α → Bool :=
  sorry


/- ### 一个反例

并非所有的归纳定义都是合法的。 -/

/- -- 失败
归纳定义 Illegal : Prop 其中
  | 引入 : ¬ Illegal → Illegal -/"fails" 通常指系统、设备或操作未能按预期执行，导致功能中断或性能下降。根据上下文，可以翻译为“失败”、“故障”或“失效”。例如：
- **系统失败 (System fails)**：指系统无法正常运行或完成指定任务。
- **硬件故障 (Hardware fails)**：指硬件设备出现故障，无法正常工作。
- **操作失效 (Operation fails)**：指某项操作未能成功执行。

如果需要更具体的翻译，请提供完整的句子或上下文。inductive Illegal : Prop where
  | intro : ¬ Illegal → Illegal
-/


/- ## 逻辑符号

真值 `False` 和 `True`、连接词 `∧`、`∨` 和 `↔`、存在量词 `∃` 以及等值谓词 `=` 都被定义为归纳命题或谓词。相比之下，`∀` 和 `→` 是逻辑系统内置的。

语法糖：

    `∃x : α, P` := `Exists (λx : α, P)`
    `x = y`     := `Eq x y` -/

namespace logical_symbols

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

inductive Iff (a b : Prop) : Prop where
  | intro : (a → b) → (b → a) → Iff a b

inductive Exists {α : Type} (P : α → Prop) : Prop where
  | intro : ∀a : α, P a → Exists P

inductive True : Prop where
  | intro : True

inductive False : Prop where

inductive Eq {α : Type} : α → α → Prop where
  | refl : ∀a : α, Eq a a

end logical_symbols

#print And
#print Or
#print Iff
#print Exists
#print True
#print False
#print Eq


/- ## 规则归纳

正如我们可以对项进行归纳一样，我们也可以对证明项进行归纳。

这被称为**规则归纳**，因为归纳是基于引入规则（即证明项的构造器）进行的。得益于PAT原则，这种方法能够如预期般工作。 -/

theorem mod_two_Eq_zero_of_Even (n : ℕ) (h : Even n) :
    n % 2 = 0 :=
  by
    induction h with
    | zero            => rfl
    | add_two k hk ih => simp [ih]

theorem Not_Even_two_mul_add_one (m n : ℕ)
      (hm : m = 2 * n + 1) :
    ¬ Even m :=
  by
    intro h
    induction h generalizing n with
    | zero            => linarith
    | add_two k hk ih =>
      apply ih (n - 1)
      cases n with
      | zero    => simp [Nat.ctor_eq_zero] at *
      | succ n' =>
        simp [Nat.succ_eq_add_one] at *
        linarith

/- `linarith` 用于证明涉及线性算术等式或不等式的目标。"线性"意味着它仅适用于 `+` 和 `-`，而不适用于 `*` 和 `/`（但支持乘以常数的运算）。 -/

theorem linarith_example (i : Int) (hi : i > 5) :
    2 * i + 3 > 11 :=
  by linarith

theorem Star_Star_Iff_Star {α : Type} (R : α → α → Prop)
      (a b : α) :
    Star (Star R) a b ↔ Star R a b :=
  by
    apply Iff.intro
    { intro h
      induction h with
      | base a b hab                  => exact hab
      | refl a                        => apply Star.refl
      | trans a b c hab hbc ihab ihbc =>
        apply Star.trans a b
        { exact ihab }
        { exact ihbc } }
    { intro h
      apply Star.base
      exact h }

@[simp] theorem Star_Star_Eq_Star {α : Type}
      (R : α → α → Prop) :
    Star (Star R) = Star R :=
  by
    apply funext
    intro a
    apply funext
    intro b
    apply propext
    apply Star_Star_Iff_Star

#check funext
#check propext


/- ## 消解（Elimination）

给定一个归纳谓词 `P`，其引入规则通常具有以下形式：
`∀…, ⋯ → P …`，并且可以用于证明形如 `⊢ P …` 的目标。

消解则是相反的过程：它从形如 `P …` 的定理或假设中提取信息。消解有多种形式：模式匹配、`cases` 和 `induction` 策略，以及自定义的消解规则（例如 `And.left`）。

* `cases` 的工作方式类似于 `induction`，但没有归纳假设。

* `match` 也可以使用。

现在，我们终于可以理解 `cases h`（其中 `h : l = r`）以及 `cases Classical.em h` 的工作原理了。 -/

#print Eq

theorem cases_Eq_example {α : Type} (l r : α) (h : l = r)
      (P : α → α → Prop) :
    P l r :=
  by
    cases h
    sorry

#check Classical.em
#print Or

theorem cases_Classical_em_example {α : Type} (a : α)
      (P Q : α → Prop) :
    Q a :=
  by
    have hor : P a ∨ ¬ P a :=
      Classical.em (P a)
    cases hor with
    | inl hl => sorry
    | inr hr => sorry

/- 通常，将形式为 `P (c …)` 的具体项重写是方便的，其中 `c` 通常是一个构造函数。我们可以陈述并证明一个**反演规则**来支持这种消除性推理。

典型的反演规则如下：

    `∀x y, P (c x y) → (∃…, ⋯ ∧ ⋯) ∨ ⋯ ∨ (∃…, ⋯ ∧ ⋯)`

将引入规则和消除规则结合到一个单一的定理中可能非常有用，该定理可以用于重写目标的前提和结论：

    `∀x y, P (c x y) ↔ (∃…, ⋯ ∧ ⋯) ∨ ⋯ ∨ (∃…, ⋯ ∧ ⋯)` -/

theorem Even_Iff (n : ℕ) :
    Even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) :=
  by
    apply Iff.intro
    { intro hn
      cases hn with
      | zero         => simp
      | add_two k hk =>
        apply Or.inr
        apply Exists.intro k
        simp [hk] }
    { intro hor
      cases hor with
      | inl heq => simp [heq, Even.zero]
      | inr hex =>
        cases hex with
        | intro k hand =>
          cases hand with
          | intro heq hk =>
            simp [heq, Even.add_two _ hk] }

theorem Even_Iff_struct (n : ℕ) :
    Even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) :=
  Iff.intro
    (assume hn : Even n
     match n, hn with
     | _, Even.zero         =>
       show 0 = 0 ∨ _ from
         by simp
     | _, Even.add_two k hk =>
       show _ ∨ (∃m, k + 2 = m + 2 ∧ Even m) from
         Or.inr (Exists.intro k (by simp [*])))
    (assume hor : n = 0 ∨ (∃m, n = m + 2 ∧ Even m)
     match hor with
     | Or.inl heq =>
       show Even n from
         by simp [heq, Even.zero]
     | Or.inr hex =>
       match hex with
       | Exists.intro m hand =>
         match hand with
         | And.intro heq hm =>
           show Even n from
             by simp [heq, Even.add_two _ hm])


/- ## 更多示例

### 排序列表 -/

inductive Sorted : List ℕ → Prop where
  | nil : Sorted []
  | single (x : ℕ) : Sorted [x]
  | two_or_more (x y : ℕ) {zs : List ℕ} (hle : x ≤ y)
      (hsorted : Sorted (y :: zs)) :
    Sorted (x :: y :: zs)

theorem Sorted_nil :
    Sorted [] :=
  Sorted.nil

theorem Sorted_2 :
    Sorted [2] :=
  Sorted.single _

theorem Sorted_3_5 :
    Sorted [3, 5] :=
  by
    apply Sorted.two_or_more
    { simp }
    { exact Sorted.single _ }

theorem Sorted_3_5_raw :
    Sorted [3, 5] :=
  Sorted.two_or_more _ _ (by simp) (Sorted.single _)

theorem sorted_7_9_9_11 :
    Sorted [7, 9, 9, 11] :=
  Sorted.two_or_more _ _ (by simp)
    (Sorted.two_or_more _ _ (by simp)
       (Sorted.two_or_more _ _ (by simp)
          (Sorted.single _)))

theorem Not_Sorted_17_13 :
    ¬ Sorted [17, 13] :=
  by
    intro h
    cases h with
    | two_or_more _ _ hlet hsorted => simp at hlet


/- ### 回文

**回文**（Palindrome）是指正读和反读都相同的字符串、数字序列或其他序列。例如，"madam"、"racecar" 和 "12321" 都是回文的例子。回文在计算机科学、数学和语言学中都有广泛的应用。

在计算机科学中，回文常用于算法设计和字符串处理。例如，判断一个字符串是否为回文是一个常见的编程问题。通常，可以通过比较字符串与其反转后的字符串是否相等来实现这一判断。

在数学中，回文数是指正读和反读都相同的数字。例如，121 和 1331 都是回文数。回文数在数论中也有一定的研究价值。

在语言学中，回文可以指正读和反读都相同的单词、短语或句子。例如，"A man, a plan, a canal, Panama!" 是一个著名的回文句子。

总之，回文是一个跨学科的概念，具有广泛的应用和研究价值。 -/

inductive Palindrome {α : Type} : List α → Prop where
  | nil : Palindrome []
  | single (x : α) : Palindrome [x]
  | sandwich (x : α) (xs : List α) (hxs : Palindrome xs) :
    Palindrome ([x] ++ xs ++ [x])

/- 以下是技术文档的中文翻译，保持专业术语准确：

```plaintext
-- 失败
def palindromeRec {α : Type} : List α → Bool
  | []                 => true  -- 空列表是回文
  | [_]                => true  -- 单元素列表是回文
  | ([x] ++ xs ++ [x]) => palindromeRec xs  -- 如果列表的首尾元素相同，递归检查中间部分
  | _                  => false  -- 其他情况不是回文
```

### 解释：
- `palindromeRec` 是一个递归函数，用于判断一个列表是否为回文。
- `α : Type` 表示类型参数，`List α` 表示元素类型为 `α` 的列表。
- `[]` 表示空列表，`[_]` 表示单元素列表。
- `([x] ++ xs ++ [x])` 表示列表的首尾元素相同，中间部分为 `xs`。
- 如果列表的首尾元素相同，则递归检查中间部分 `xs`。
- 其他情况返回 `false`，表示列表不是回文。 -/The system fails to start" 可译为 **“系统启动失败”**。
- "If the sensor fails, the backup system will activate" 可译为 **“如果传感器失效，备用系统将启动”**。

请根据具体场景选择合适的术语。def palindromeRec {α : Type} : List α → Bool
  | []                 => true
  | [_]                => true
  | ([x] ++ xs ++ [x]) => palindromeRec xs
  | _                  => false
-/

theorem Palindrome_aa {α : Type} (a : α) :
    Palindrome [a, a] :=
  Palindrome.sandwich a _ Palindrome.nil

theorem Palindrome_aba {α : Type} (a b : α) :
    Palindrome [a, b, a] :=
  Palindrome.sandwich a _ (Palindrome.single b)

theorem Palindrome_reverse {α : Type} (xs : List α)
      (hxs : Palindrome xs) :
    Palindrome (reverse xs) :=
  by
    induction hxs with
    | nil                  => exact Palindrome.nil
    | single x             => exact Palindrome.single x
    | sandwich x xs hxs ih =>
      { simp [reverse, reverse_append]
        exact Palindrome.sandwich _ _ ih }


/- ### 满二叉树

**满二叉树**（Full Binary Tree）是一种特殊的二叉树结构，其中每个节点要么是叶子节点（没有子节点），要么恰好有两个子节点（左子节点和右子节点）。换句话说，满二叉树中不存在只有一个子节点的节点。

#### 特点
1. **节点数量**：如果一个满二叉树的深度为 \( h \)，那么它的节点总数为 \( 2^h - 1 \)。
2. **叶子节点**：所有叶子节点都位于同一层级。
3. **平衡性**：满二叉树是一种高度平衡的二叉树，因为它的左右子树的高度差始终为0。

#### 应用场景
满二叉树常用于以下场景：
- **堆数据结构**：二叉堆（如最大堆或最小堆）通常基于满二叉树实现。
- **哈夫曼编码**：在数据压缩中，哈夫曼树通常是一个满二叉树。
- **完全二叉树的基础**：满二叉树是完全二叉树的一种特殊情况。

#### 示例
以下是一个深度为3的满二叉树的示例：

```
        A
       / \
      B   C
     / \ / \
    D  E F  G
```

在这个例子中，节点A、B、C都有两个子节点，而节点D、E、F、G都是叶子节点。

#### 总结
满二叉树是一种结构严谨的二叉树，具有明确的节点数量和层级关系。它在计算机科学中有着广泛的应用，尤其是在需要高效存储和检索数据的场景中。 -/

#check Tree

inductive IsFull {α : Type} : Tree α → Prop where
  | nil : IsFull Tree.nil
  | node (a : α) (l r : Tree α)
      (hl : IsFull l) (hr : IsFull r)
      (hiff : l = Tree.nil ↔ r = Tree.nil) :
    IsFull (Tree.node a l r)

theorem IsFull_singleton {α : Type} (a : α) :
    IsFull (Tree.node a Tree.nil Tree.nil) :=
  by
    apply IsFull.node
    { exact IsFull.nil }
    { exact IsFull.nil }
    { rfl }

theorem IsFull_mirror {α : Type} (t : Tree α)
      (ht : IsFull t) :
    IsFull (mirror t) :=
  by
    induction ht with
    | nil                             => exact IsFull.nil
    | node a l r hl hr hiff ih_l ih_r =>
      { rw [mirror]
        apply IsFull.node
        { exact ih_r }
        { exact ih_l }
        { simp [mirror_Eq_nil_Iff, *] } }

theorem IsFull_mirror_struct_induct {α : Type} (t : Tree α) :
    IsFull t → IsFull (mirror t) :=
  by
    induction t with
    | nil                  =>
      { intro ht
        exact ht }
    | node a l r ih_l ih_r =>
      { intro ht
        cases ht with
        | node _ _ _ hl hr hiff =>
          { rw [mirror]
            apply IsFull.node
            { exact ih_r hr }
            { apply ih_l hl }
            { simp [mirror_Eq_nil_Iff, *] } } }


/- ### 一阶项 -/

inductive Term (α β : Type) : Type where
  | var : β → Term α β
  | fn  : α → List (Term α β) → Term α β

inductive WellFormed {α β : Type} (arity : α → ℕ) :
  Term α β → Prop where
  | var (x : β) : WellFormed arity (Term.var x)
  | fn (f : α) (ts : List (Term α β))
      (hargs : ∀t ∈ ts, WellFormed arity t)
      (hlen : length ts = arity f) :
    WellFormed arity (Term.fn f ts)

inductive VariableFree {α β : Type} : Term α β → Prop where
  | fn (f : α) (ts : List (Term α β))
      (hargs : ∀t ∈ ts, VariableFree t) :
    VariableFree (Term.fn f ts)

end LoVe
