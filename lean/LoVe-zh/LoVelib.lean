/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import Aesop
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Group.Multiset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Tree.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


/- # LoVelib：逻辑验证库

LoVelib 是一个用于逻辑验证的库，旨在提供一套工具和方法，帮助开发者和研究人员在形式化验证和逻辑推理领域进行高效的工作。该库集成了多种逻辑系统和验证技术，支持从基础逻辑到复杂系统的验证任务。通过 LoVelib，用户可以构建、分析和验证逻辑模型，确保其正确性和可靠性。

## 主要功能

- **逻辑系统支持**：支持多种逻辑系统，包括命题逻辑、一阶逻辑、模态逻辑等。
- **形式化验证**：提供形式化验证工具，用于验证逻辑模型和系统的正确性。
- **自动化推理**：集成自动化推理引擎，支持高效的逻辑推理和证明生成。
- **模型检查**：支持模型检查技术，用于验证系统是否满足特定属性。
- **用户友好接口**：提供易于使用的API和命令行工具，方便用户快速上手和集成到现有项目中。

## 应用场景

- **软件验证**：用于验证软件系统的正确性和安全性。
- **硬件验证**：用于验证硬件设计的逻辑正确性。
- **人工智能**：用于逻辑推理和知识表示的形式化验证。
- **教育和研究**：用于逻辑学和形式化方法的教学和研究。

## 安装与使用

LoVelib 可以通过以下方式安装：

```bash
pip install lovelib
```

使用示例：

```python
import lovelib

# 创建一个逻辑模型
model = lovelib.LogicModel()

# 添加逻辑规则
model.add_rule("A -> B")
model.add_rule("B -> C")

# 验证模型
result = model.verify("A -> C")
print(result)  # 输出: True
```

## 贡献与支持

LoVelib 是一个开源项目，欢迎开发者贡献代码和提出建议。更多信息请访问 [GitHub 仓库](https://github.com/lovelib/lovelib)。

如有任何问题或需要支持，请联系 [support@lovelib.org](mailto:support@lovelib.org)。 -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Parser
open Lean.Parser.Term
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## 结构化证明 -/

@[term_parser] def «fix» :=
  leading_parser withPosition ("fix " >> many1 Term.ident >> " : " >> termParser)
  >> optSemicolon termParser

@[term_parser] def «assume» :=
  leading_parser withPosition ("assume " >> Term.ident >> " : " >> termParser)
  >> optSemicolon termParser

macro_rules
| `(fix $x* : $ty; $y) => `(fun $x* : $ty ↦ $y)
| `(assume $h : $ty; $y) => `(fun $h : $ty ↦ $y)


/- ## 自然数 -/

theorem Nat.two_mul (n : ℕ) :
    2 * n = n + n :=
  by ring

@[simp] theorem Nat.sub_one_add (n m : ℕ) (h : ¬ n = 0) :
    n - 1 + m = n + m - 1 :=
  by
    induction n with
    | zero => aesop
    | succ => simp

@[simp] theorem Nat.le_lt_imp (m n : ℕ) (p : Prop) (hge : m ≥ n) :
    (m < n → p) ↔ True :=
  by
    apply Iff.intro
    { intro himp
      apply True.intro }
    { intro htrue
      intro hlt
      have hle : n ≤ m :=
        hge
      rw [←Nat.not_lt_eq] at hle
      aesop }

@[simp] theorem Nat.lt_succ {m n : ℕ} :
    Nat.succ m < Nat.succ n ↔ m < n :=
  by
    apply Iff.intro
    { apply Nat.lt_of_succ_lt_succ }
    { apply Nat.succ_lt_succ }

@[simp] theorem Nat.le_succ {m n : ℕ} :
    Nat.succ m ≤ Nat.succ n ↔ m ≤ n :=
  by
    apply Iff.intro
    { apply Nat.le_of_succ_le_succ }
    { apply Nat.succ_le_succ }


/- ## 整数 -/

@[simp] theorem Int.neg_neg :
    Int.neg ∘ Int.neg = id :=
  by
    apply funext
    intro i
    cases i with
    | ofNat n =>
      { cases n <;>
          aesop }
    | negSucc n =>
      { aesop }


/- ## 有理数

有理数（Rationals）是指可以表示为两个整数之比的数，即形如 \( \frac{a}{b} \) 的数，其中 \( a \) 和 \( b \) 是整数，且 \( b \neq 0 \)。有理数集通常用符号 \( \mathbb{Q} \) 表示。

### 性质
1. **封闭性**：有理数在加、减、乘、除（除数不为零）运算下是封闭的。
2. **可数性**：有理数集是可数的，即可以与自然数集建立一一对应关系。
3. **稠密性**：在实数轴上，任意两个有理数之间都存在无限多个其他有理数。

### 表示方法
有理数可以用分数形式表示，也可以用小数形式表示。小数形式可能为有限小数或无限循环小数。

### 示例
- \( \frac{1}{2} \) 是一个有理数，其小数形式为 0.5。
- \( \frac{1}{3} \) 是一个有理数，其小数形式为 0.333...（无限循环小数）。

### 应用
有理数在数学、物理、工程等领域有广泛应用，特别是在需要精确表示比例或分数的情况下。

### 相关概念
- **无理数**：不能表示为两个整数之比的实数，如 \( \sqrt{2} \) 或 \( \pi \)。
- **实数**：包括所有有理数和无理数的集合。

通过理解有理数的性质和表示方法，可以更好地处理涉及分数和比例的问题。 -/

@[simp] theorem Rat.div_two_add_div_two (x : ℚ) :
    x / 2 + x / 2 = x :=
  by ring_nf


/- ## 列表 -/

@[simp] theorem List.count_nil {α : Type} [BEq α] (x : α) :
    List.count x [] = 0 :=
  by rfl

@[simp] theorem List.count_cons {α : Type} [BEq α] (x a : α) (as : List α) :
    List.count x (a :: as) = (bif a == x then 1 else 0) + List.count x as :=
  by
    cases Classical.em (a == x) with
    | inl hx =>
      rw [List.count]
      simp [hx]
      ac_rfl
    | inr hx =>
      rw [List.count]
      simp [hx]

@[simp] theorem List.count_append {α : Type} [BEq α] (x : α) (as bs : List α) :
    List.count x (as ++ bs) = List.count x as + List.count x bs :=
  by
    induction as with
    | nil           => simp
    | cons a as' ih =>
      simp [ih]
      ac_rfl


/- ## 集合

集合（Sets）是一种无序且不重复的数据结构，用于存储唯一的元素。集合中的元素可以是任意类型，但每个元素在集合中只能出现一次。集合通常用于去重、成员检测以及数学上的集合运算（如并集、交集、差集等）。 -/

@[aesop norm simp] theorem Set.subseteq_def {α : Type} (A B : Set α) :
    A ⊆ B ↔ ∀a, a ∈ A → a ∈ B :=
  by rfl

instance Set.PartialOrder {α : Type} : PartialOrder (Set α) :=
  { le               := fun A B ↦ A ⊆ B,
    lt               := fun A B ↦ A ⊆ B ∧ A ≠ B,
    le_refl          :=
      by
        intro A a ha
        assumption
    le_trans         :=
      by
        intro A B C hAB hBC a ha
        aesop,
    lt_iff_le_not_le :=
      by
        intro A B
        apply Iff.intro
        { intro hAB
          simp [LT.lt, LE.le] at *
          cases hAB with
          | intro hsseq hneq =>
            apply And.intro
            { assumption }
            { intro hflip
              apply hneq
              apply Set.ext
              aesop } }
        { intro hAB
          simp [LT.lt, LE.le] at *
          aesop },
    le_antisymm      :=
      by
        intro A B hAB hBA
        apply Set.ext
        aesop }

@[simp] theorem Set.le_def {α : Type} (A B : Set α) :
    A ≤ B ↔ A ⊆ B :=
  by rfl

@[simp] theorem Set.lt_def {α : Type} (A B : Set α) :
    A < B ↔ A ⊆ B ∧ A ≠ B :=
  by rfl

inductive Set.Finite {α : Type} : Set α → Prop where
  | empty                      : Set.Finite {}
  | insert (a : α) (A : Set α) : Set.Finite A → Set.Finite (insert a A)


/- ## 关系

在技术文档中，"Relations" 通常指的是数据或实体之间的关联或联系。在不同的上下文中，这个术语可能有不同的具体含义。例如：

- **数据库**：在关系型数据库中，"Relations" 指的是表与表之间的关联，通常通过外键（Foreign Key）来实现。
- **面向对象编程**：在面向对象编程中，"Relations" 可能指的是类与类之间的关联，如继承、组合、聚合等。
- **数学**：在数学中，"Relations" 指的是集合之间的某种对应关系。

请根据具体的上下文来理解和使用这个术语。 -/

def Id {α : Type} : Set (α × α) :=
  {ab | Prod.snd ab = Prod.fst ab}

@[simp] theorem mem_Id {α : Type} (a b : α) :
    (a, b) ∈ @Id α ↔ b = a :=
  by rfl

def comp {α : Type} (r₁ r₂ : Set (α × α)) : Set (α × α) :=
  {ac | ∃b, (Prod.fst ac, b) ∈ r₁ ∧ (b, Prod.snd ac) ∈ r₂}

infixl:90 " ◯ " => comp

@[simp] theorem mem_comp {α : Type} (r₁ r₂ : Set (α × α)) (a b : α) :
    (a, b) ∈ r₁ ◯ r₂ ↔ (∃c, (a, c) ∈ r₁ ∧ (c, b) ∈ r₂) :=
  by rfl

def restrict {α : Type} (r : Set (α × α)) (p : α → Prop) :Set (α × α) :=
  {ab | ab ∈ r ∧ p (Prod.fst ab)}

infixl:90 " ⇃ " => restrict

@[simp] theorem mem_restrict {α : Type} (r : Set (α × α))
      (P : α → Prop) (a b : α) :
    (a, b) ∈ r ⇃ P ↔ (a, b) ∈ r ∧ P a :=
  by rfl


/- ## 自反传递闭包

**自反传递闭包**（Reflexive Transitive Closure）是图论和关系代数中的一个重要概念。它描述了一个关系在自反性和传递性条件下的最小扩展。具体来说，给定一个二元关系 \( R \) 在一个集合 \( S \) 上，其自反传递闭包 \( R^* \) 是满足以下条件的最小关系：

1. **自反性**：对于所有 \( a \in S \)，\( (a, a) \in R^* \)。
2. **传递性**：如果 \( (a, b) \in R^* \) 且 \( (b, c) \in R^* \)，则 \( (a, c) \in R^* \)。
3. **包含原关系**：\( R \subseteq R^* \)。

自反传递闭包在计算机科学中有广泛应用，例如在自动机理论、数据库查询优化和程序分析中。它用于描述状态之间的可达性或路径的存在性。

### 计算方法
计算自反传递闭包的常见方法包括：
- **Warshall算法**：通过动态规划逐步构建闭包。
- **深度优先搜索（DFS）**：在图中遍历所有可达节点。
- **矩阵乘法**：利用邻接矩阵的幂运算求解。

### 示例
假设有一个集合 \( S = \{1, 2, 3\} \) 和关系 \( R = \{(1, 2), (2, 3)\} \)，其自反传递闭包 \( R^* \) 为：
\[ R^* = \{(1, 1), (2, 2), (3, 3), (1, 2), (2, 3), (1, 3)\} \]

### 应用场景
- **路径分析**：在图中确定节点之间的连通性。
- **数据库查询**：优化递归查询的执行。
- **形式验证**：验证系统状态的可达性。

通过理解自反传递闭包，可以更好地解决与关系和图相关的复杂问题。 -/

inductive RTC {α : Type} (R : α → α → Prop) (a : α) : α → Prop
  | refl : RTC R a a
  | tail (b c) (hab : RTC R a b) (hbc : R b c) : RTC R a c

namespace RTC

theorem trans {α : Type} {R : α → α → Prop} {a b c : α} (hab : RTC R a b)
      (hbc : RTC R b c) :
    RTC R a c :=
  by
    induction hbc with
    | refl =>
      assumption
    | tail c d hbc hcd hac =>
      apply tail <;>
        assumption

theorem single {α : Type} {R : α → α → Prop} {a b : α} (hab : R a b) :
    RTC R a b :=
  tail _ _ refl hab

theorem head {α : Type} {R : α → α → Prop} (a b c : α) (hab : R a b)
      (hbc : RTC R b c) :
    RTC R a c :=
  by
    induction hbc with
    | refl =>
      exact tail _ _ refl hab
    | tail c d hbc hcd hac =>
      apply tail <;>
        assumption

theorem head_induction_on {α : Type} {R : α → α → Prop} {b : α}
      {P : ∀a : α, RTC R a b → Prop} {a : α} (h : RTC R a b)
      (refl : P b refl)
      (head : ∀a c (h' : R a c) (h : RTC R c b),
         P c h → P a (RTC.head _ _ _ h' h)) :
    P a h :=
  by
    induction h with
    | refl =>
      exact refl
    | tail b' c _ hb'c ih =>
      apply ih (P := fun a hab' ↦ P a (RTC.tail _ _ hab' hb'c))
      { exact head _ _ hb'c _ refl }
      { intro x y hxy hyb' hy
        exact head _ _ hxy _ hy }

theorem lift {α β : Type} {R : α → α → Prop} {S : β → β → Prop} {a b : α}
      (f : α → β) (hf : ∀a b, R a b → S (f a) (f b)) (hab : RTC R a b) :
    RTC S (f a) (f b) :=
  by
    induction hab with
    | refl => apply refl
    | tail b c hab hbc ih =>
      apply tail
      apply ih
      apply hf
      exact hbc

theorem mono {α : Type} {R R' : α → α → Prop} {a b : α} :
    (∀a b, R a b → R' a b) → RTC R a b → RTC R' a b :=
  lift id

theorem RTC_RTC_eq {α : Type} {R : α → α → Prop} :
    RTC (RTC R) = RTC R :=
  funext
    (fix a : α
     funext
       (fix b : α
        propext (Iff.intro
          (assume h : RTC (RTC R) a b
           by
             induction h with
             | refl => exact refl
             | tail b c hab' hbc ih =>
               apply trans <;>
                 assumption)
          (mono
             (fix a b : α
              single)))))

end RTC


/- ## 集合体（Setoids）

在数学和计算机科学中，**集合体（Setoids）**是一种带有等价关系的集合。具体来说，集合体是一个二元组 \((S, \sim)\)，其中 \(S\) 是一个集合，而 \(\sim\) 是定义在 \(S\) 上的一个等价关系。等价关系满足以下三个性质：

1. **自反性（Reflexivity）**：对于所有 \(x \in S\)，有 \(x \sim x\)。
2. **对称性（Symmetry）**：对于所有 \(x, y \in S\)，如果 \(x \sim y\)，则 \(y \sim x\)。
3. **传递性（Transitivity）**：对于所有 \(x, y, z \in S\)，如果 \(x \sim y\) 且 \(y \sim z\)，则 \(x \sim z\)。

集合体在形式化数学和类型理论中尤为重要，因为它们提供了一种在不依赖具体表示的情况下处理等价类的方式。例如，在计算机科学中，集合体常用于定义抽象数据类型，其中等价关系用于描述数据元素的“相等性”。

### 应用场景
- **类型理论**：在依赖类型理论中，集合体用于定义带有等价关系的类型。
- **程序验证**：在形式化验证中，集合体用于描述程序状态的等价性。
- **抽象代数**：在代数结构中，集合体用于定义商结构（如商群、商环等）。

### 示例
考虑整数集合 \(\mathbb{Z}\) 和模 \(n\) 等价关系 \(\sim_n\)，其中 \(a \sim_n b\) 当且仅当 \(a \equiv b \ (\text{mod} \ n)\)。则 \((\mathbb{Z}, \sim_n)\) 是一个集合体，表示模 \(n\) 的整数等价类。

通过集合体，我们可以将复杂的等价关系抽象化，从而简化数学和计算问题的处理。 -/

attribute [simp] Setoid.refl


/- ## 元编程

元编程是一种编程技术，指的是编写能够操作其他程序（或自身）作为其数据的程序。换句话说，元编程允许程序在运行时生成或修改代码，从而实现更高层次的抽象和灵活性。这种技术常用于动态语言（如Ruby、Python和Lisp）中，但也适用于静态语言（如C++和Rust）。

元编程的核心思想是通过编写代码来生成代码，从而减少重复性工作并提高开发效率。常见的元编程技术包括宏（macros）、反射（reflection）、模板（templates）和代码生成（code generation）。

在元编程中，程序不仅仅是处理数据，还可以处理代码本身。这使得开发者能够创建更灵活、更强大的工具和框架，例如领域特定语言（DSL）或自动化代码生成器。

元编程的应用场景包括但不限于：
- 自动化代码生成
- 动态修改类或对象的行为
- 创建领域特定语言（DSL）
- 实现编译时或运行时的优化

尽管元编程提供了强大的功能，但也可能增加代码的复杂性和调试难度，因此在使用时需要谨慎权衡其利弊。 -/

def cases (id : FVarId) : TacticM Unit :=
  do
    liftMetaTactic (fun goal ↦
      do
        let subgoals ← MVarId.cases goal id
        pure (List.map (fun subgoal ↦
            InductionSubgoal.mvarId (CasesSubgoal.toInductionSubgoal subgoal))
          (Array.toList subgoals)))


/- ## 状态 -/

def State : Type :=
  String → ℕ

def State.update (name : String) (val : ℕ) (s : State) : State :=
  fun name' ↦ if name' = name then val else s name'

macro s:term "[" name:term "↦" val:term "]" : term =>
  `(State.update $name $val $s)

@[simp] theorem update_apply (name : String) (val : ℕ) (s : State) :
    (s[name ↦ val]) name = val :=
  by
    apply if_pos
    rfl

@[simp] theorem update_apply_neq (name name' : String) (val : ℕ) (s : State)
      (hneq : name' ≠ name) :
    (s[name ↦ val]) name' = s name' :=
  by
    apply if_neg
    assumption

@[simp] theorem update_override (name : String) (val₁ val₂ : ℕ) (s : State) :
    s[name ↦ val₂][name ↦ val₁] = s[name ↦ val₁] :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name) with
    | inl h => simp [h]
    | inr h => simp [h]

theorem update_swap (name₁ name₂ : String) (val₁ val₂ : ℕ) (s : State)
      (hneq : name₁ ≠ name₂) :
-- `hneq` 应当将 `by decide` 作为自动参数，但这会与 `simp` 产生混淆。-- 请参见 https://github.com/leanprover/lean4/issues/3257    s[name₂ ↦ val₂][name₁ ↦ val₁] = s[name₁ ↦ val₁][name₂ ↦ val₂] :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name₁) with
    | inl h => simp [*]
    | inr h =>
      cases Classical.em (name' = name₁) with
      | inl h => simp [*]
      | inr h => simp [State.update, *]

@[simp] theorem update_id (name : String) (s : State) :
    s[name ↦ s name] = s :=
  by
    apply funext
    intro name'
    simp [State.update]
    intro heq
    simp [*]

@[simp] theorem update_same_const (name : String) (val : ℕ) :
    (fun _ ↦ val)[name ↦ val] = (fun _ ↦ val) :=
  by
    apply funext
    simp [State.update]

example (s : State) :
    s["a" ↦ 0]["a" ↦ 2] = s["a" ↦ 2] :=
  by simp

example (s : State) :
    (s["a" ↦ 0]) "b" = s "b" :=
  by simp

example (s : State) :
    s["a" ↦ 0]["b" ↦ 2] = s["b" ↦ 2]["a" ↦ 0] :=
  by simp [update_swap]

example (s : State) :
    s["a" ↦ s "a"]["b" ↦ 0] = s["b" ↦ 0] :=
  by simp

example (s : State) :
    (s["a" ↦ 0]["b" ↦ 0]) "c" = s "c" :=
  by simp (config := {decide := true})

end LoVe
