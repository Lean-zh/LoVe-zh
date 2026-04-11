/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe 演示 11：指称语义

我们回顾第三种指定编程语言语义的方法：**指称语义**。指称语义试图直接指定程序的含义。

如果操作语义是一个理想化的解释器，霍尔逻辑是一个理想化的验证器，那么指称语义就是一个理想化的编译器。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 组合性

__指称语义学__ 将每个程序的含义定义为一个数学对象：

    `⟦ ⟧ : 语法 → 语义`

指称语义学的一个关键属性是 __组合性__：复合语句的含义应基于其组成部分的含义来定义。这使得以下定义不符合要求：

    `⟦S⟧ = {st | (S, Prod.fst st) ⟹ Prod.snd st}`

（即

    `⟦S⟧ = {(s, t) | (S, s) ⟹ t}`）

因为操作语义学不具备组合性。

简而言之，我们希望：

    `⟦S; T⟧               = … ⟦S⟧ … ⟦T⟧ …`
    `⟦if B then S else T⟧ = … ⟦S⟧ … ⟦T⟧ …`
    `⟦while B do S⟧       = … ⟦S⟧ …`

算术表达式的求值函数

    `eval : AExp → ((String → ℤ) → ℤ)`

是指称语义学的一个例子。我们希望命令式程序也能有类似的语义定义。

## 一种关系型指称语义学

我们可以将命令式程序的语义表示为从初始状态到最终状态的函数，或者更一般地表示为初始状态与最终状态之间的关系：`Set (State × State)`。

对于 `skip`、`:=`、`;` 和 `if then else`，指称语义学的定义是简单的： -/

namespace SorryDefs

def denote : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       =>
    {st | Prod.snd st = (Prod.fst st)[x ↦ a (Prod.fst st)]}
  | Stmt.seq S T          => denote S ◯ denote T
  | Stmt.ifThenElse B S T =>
    (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      => sorry

end SorryDefs

/- 我们将 `⟦S⟧` 表示为 `denote S`。对于 `while` 语句，我们希望写成

    `((denote S ◯ denote (Stmt.whileDo B S)) ⇃ B)`
    `∪ (Id ⇃ (fun s ↦ ¬ B s))`

但由于对 `Stmt.whileDo B S` 的递归调用，这是不合理的。

我们需要找到一个 `X`，使得

    `X = ((denote S ◯ X) ⇃ B) ∪ (Id ⇃ (fun s ↦ ¬ B s))`

换句话说，我们正在寻找一个不动点。

本讲座的大部分内容涉及构建一个最小不动点操作符 `lfp`，它将允许我们定义 `while` 语句的情况：

    `lfp (fun X ↦ ((denote S ◯ X) ⇃ B) ∪ (Id ⇃ (fun s ↦ ¬ B s)))`

## 不动点

`f` 的**不动点**（或固定点）是方程 `X = f X` 中 `X` 的解。

通常，不动点可能根本不存在（例如，`f := Nat.succ`），或者可能存在多个不动点（例如，`f := id`）。但在某些条件下，`f` 的唯一**最小不动点**和唯一**最大不动点**是保证存在的。

考虑以下**不动点方程**：

    `X = (fun (P : ℕ → Prop) (n : ℕ) ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ P m) X`
      `= (fun n : ℕ ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ X m)`

其中 `X : ℕ → Prop` 且
`f := (fun (P : ℕ → Prop) (n : ℕ) ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ P m)`。

上述示例仅有一个不动点。不动点方程唯一地指定 `X` 为描述偶数的谓词。

通常，最小和最大不动点可能不同：

    `X = X`

这里，最小不动点是 `fun _ ↦ False`，最大不动点是 `fun _ ↦ True`。按照惯例，`False < True`，因此 `(fun _ ↦ False) < (fun _ ↦ True)`。类似地，`∅ < @Set.univ ℕ`。

对于编程语言的语义：

* `X` 的类型为 `Set (State × State)`（与 `State → State → Prop` 同构），表示状态之间的关系；
* `f` 对应于要么进行循环的额外一次迭代（如果条件 `B` 为真），要么是恒等函数（如果 `B` 为假）。

最小不动点对应于程序的有限执行，这是我们关心的全部内容。

**关键观察**：

    归纳谓词对应于最小不动点，但它们已内置于 Lean 的逻辑（归纳构造的演算）中。

## 单调函数

设 `α` 和 `β` 为具有偏序 `≤` 的类型。函数 `f : α → β` 是**单调的**，如果

    `a₁ ≤ a₂ → f a₁ ≤ f a₂`   对于所有 `a₁`, `a₂`

许多集合操作（例如，`∪`）、关系操作（例如，`◯`）和函数操作（例如，`fun x ↦ x`，`fun _ ↦ k`，`∘`）是单调的或保持单调性。

所有单调函数 `f : Set α → Set α` 都允许最小和最大不动点。

**非单调函数的示例**：

    `f A = (if A = ∅ then Set.univ else ∅)`

假设 `α` 是非空的，我们有 `∅ ⊆ Set.univ`，但 `f ∅ = Set.univ ⊈ ∅ = f Set.univ`。 -/

def Monotone {α β : Type} [PartialOrder α] [PartialOrder β]
  (f : α → β) : Prop :=
  ∀a₁ a₂, a₁ ≤ a₂ → f a₁ ≤ f a₂

theorem Monotone_id {α : Type} [PartialOrder α] :
    Monotone (fun a : α ↦ a) :=
  by
    intro a₁ a₂ ha
    exact ha

theorem Monotone_const {α β : Type} [PartialOrder α]
    [PartialOrder β] (b : β) :
    Monotone (fun _ : α ↦ b) :=
  by
    intro a₁ a₂ ha
    exact le_refl b

theorem Monotone_union {α β : Type} [PartialOrder α]
      (f g : α → Set β) (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun a ↦ f a ∪ g a) :=
  by
    intro a₁ a₂ ha b hb
    cases hb with
    | inl h => exact Or.inl (hf a₁ a₂ ha h)
    | inr h => exact Or.inr (hg a₁ a₂ ha h)

/- 我们将在练习中证明以下两个定理。 -/

namespace SorryTheorems

theorem Monotone_comp {α β : Type} [PartialOrder α]
      (f g : α → Set (β × β)) (hf : Monotone f)
      (hg : Monotone g) :
    Monotone (fun a ↦ f a ◯ g a) :=
  sorry

theorem Monotone_restrict {α β : Type} [PartialOrder α]
      (f : α → Set (β × β)) (P : β → Prop) (hf : Monotone f) :
    Monotone (fun a ↦ f a ⇃ P) :=
  sorry

end SorryTheorems


/- ## 完全格

为了在集合上定义最小不动点，我们需要使用 `⊆` 和 `⋂`：⋂ {A | f A ⊆ A}。完全格抽象地捕捉了这一概念。一个**完全格**是一个有序类型 `α`，其中每个类型为 `Set α` 的集合都有一个下确界。

更准确地说，一个完全格由以下部分组成：

* 一个偏序关系 `≤ : α → α → Prop`（即一个自反、反对称、传递的二元谓词）；
* 一个操作符 `Inf : Set α → α`，称为**下确界**。

此外，`Inf A` 必须满足以下两个性质：

* `Inf A` 是 `A` 的一个下界：对于所有 `b ∈ A`，有 `Inf A ≤ b`；
* `Inf A` 是最大的下界：对于所有满足 `∀a, a ∈ A → b ≤ a` 的 `b`，有 `b ≤ Inf A`。

**警告：** `Inf A` 不一定是 `A` 的元素。

示例：

* 对于所有 `α`，`Set α` 是关于 `⊆` 和 `⋂` 的一个实例；
* `Prop` 是关于 `→` 和 `∀` 的一个实例（`Inf A := ∀a ∈ A, a`）；
* `ENat := ℕ ∪ {∞}`；
* `EReal := ℝ ∪ {- ∞, ∞}`；
* 如果 `α` 是一个完全格，那么 `β → α` 也是一个完全格；
* 如果 `α` 和 `β` 都是完全格，那么 `α × β` 也是一个完全格。

有限示例（抱歉使用 ASCII 艺术）：

                Z            Inf {}           = ?
              /   \          Inf {Z}          = ?
             A     B         Inf {A, B}       = ?
              \   /          Inf {Z, A}       = ?
                Y            Inf {Z, A, B, Y} = ?

非示例：

* `ℕ`、`ℤ`、`ℚ`、`ℝ`：对于 `∅` 没有下确界。
* `ERat := ℚ ∪ {- ∞, ∞}`：`Inf {q | 2 < q * q} = sqrt 2` 不在 `ERat` 中。 -/

class CompleteLattice (α : Type)
  extends PartialOrder α : Type where
  Inf    : Set α → α
  Inf_le : ∀A b, b ∈ A → Inf A ≤ b
  le_Inf : ∀A b, (∀a, a ∈ A → b ≤ a) → b ≤ Inf A

/- 对于集合： -/

instance Set.CompleteLattice {α : Type} :
  CompleteLattice (Set α) :=
  { @Set.PartialOrder α with
    Inf         := fun X ↦ {a | ∀A, A ∈ X → a ∈ A}
    Inf_le      := by aesop
    le_Inf      := by aesop }


/- ## 最小不动点

在计算机科学和数学中，**最小不动点**（Least Fixpoint）是一个重要的概念，尤其在形式化方法、程序分析和语义学等领域中广泛应用。不动点是指一个函数在某个点上的值等于该点本身，即 \( f(x) = x \)。最小不动点则是指在所有满足这一条件的点中，最小的那个点。

### 应用场景
最小不动点常用于递归定义和迭代计算中。例如，在程序分析中，最小不动点可以用来确定程序变量的可能取值范围；在形式化语义中，它可以用来定义递归函数的语义。

### 计算方法
计算最小不动点通常使用迭代方法，从一个初始值开始，反复应用函数 \( f \)，直到结果不再变化。这个过程被称为**不动点迭代**。

### 示例
假设有一个函数 \( f(x) = x^2 \)，我们想要找到它的最小不动点。通过迭代计算，可以发现当 \( x = 0 \) 时，\( f(0) = 0 \)，因此 0 是这个函数的最小不动点。

### 相关概念
- **最大不动点**（Greatest Fixpoint）：在所有满足 \( f(x) = x \) 的点中，最大的那个点。
- **不动点定理**（Fixpoint Theorem）：保证在某些条件下，不动点存在的定理。

理解最小不动点的概念对于深入掌握程序分析和形式化方法至关重要。 -/

def lfp {α : Type} [CompleteLattice α] (f : α → α) : α :=
  CompleteLattice.Inf {a | f a ≤ a}

theorem lfp_le {α : Type} [CompleteLattice α] (f : α → α)
      (a : α) (h : f a ≤ a) :
    lfp f ≤ a :=
  CompleteLattice.Inf_le _ _ h

theorem le_lfp {α : Type} [CompleteLattice α] (f : α → α)
      (a : α) (h : ∀a', f a' ≤ a' → a ≤ a') :
    a ≤ lfp f :=
  CompleteLattice.le_Inf _ _ h

/- **Knaster-Tarski 定理：** 对于任意单调函数 `f`：

* `lfp f` 是一个不动点：`lfp f = f (lfp f)`（定理 `lfp_eq`）；
* `lfp f` 小于任何其他不动点：`X = f X → lfp f ≤ X`。 -/

theorem lfp_eq {α : Type} [CompleteLattice α] (f : α → α)
      (hf : Monotone f) :
    lfp f = f (lfp f) :=
  by
    have h : f (lfp f) ≤ lfp f :=
      by
        apply le_lfp
        intro a' ha'
        apply le_trans
        { apply hf
          apply lfp_le
          assumption }
        { assumption }
    apply le_antisymm
    { apply lfp_le
      apply hf
      assumption }
    { assumption }


/- ## 关系指称语义学（续）

在本节中，我们将继续探讨关系指称语义学的相关内容。关系指称语义学是一种形式化方法，用于描述程序或语言构造的语义，通过建立输入与输出之间的关系来定义其行为。这种方法在程序验证、编译器优化以及形式化方法中具有重要应用。

### 1. 基本概念

在关系指称语义学中，程序的行为被建模为一个二元关系，其中输入状态与输出状态之间通过程序执行建立联系。具体来说，给定一个程序 \( P \)，其语义可以表示为一个关系 \( R_P \subseteq \Sigma \times \Sigma \)，其中 \( \Sigma \) 表示程序状态空间。对于任意两个状态 \( \sigma, \sigma' \in \Sigma \)，如果 \( (\sigma, \sigma') \in R_P \)，则表示程序 \( P \) 从状态 \( \sigma \) 开始执行，可能终止于状态 \( \sigma' \)。

### 2. 关系的组合与迭代

关系指称语义学的一个重要特性是支持关系的组合与迭代操作。给定两个程序 \( P_1 \) 和 \( P_2 \)，其语义关系分别为 \( R_{P_1} \) 和 \( R_{P_2} \)，则顺序组合 \( P_1; P_2 \) 的语义关系可以通过关系的复合运算得到：
\[
R_{P_1; P_2} = R_{P_2} \circ R_{P_1}
\]
其中，\( \circ \) 表示关系的复合运算，定义为：
\[
R_2 \circ R_1 = \{ (\sigma, \sigma'') \mid \exists \sigma' \in \Sigma, (\sigma, \sigma') \in R_1 \land (\sigma', \sigma'') \in R_2 \}
\]

此外，对于循环结构（如 `while` 循环），其语义可以通过关系的迭代来定义。具体来说，给定一个条件 \( b \) 和一个程序体 \( P \)，`while b do P` 的语义关系可以表示为：
\[
R_{\text{while } b \text{ do } P} = \bigcup_{n=0}^{\infty} R_{\text{while } b \text{ do } P}^n
\]
其中，\( R_{\text{while } b \text{ do } P}^n \) 表示关系 \( R_P \) 在条件 \( b \) 下的 \( n \) 次迭代。

### 3. 非确定性语义

关系指称语义学天然支持非确定性程序的语义描述。对于非确定性程序，其语义关系可能包含多个可能的输出状态。例如，给定一个非确定性选择语句 \( P_1 \sqcup P_2 \)，其语义关系为：
\[
R_{P_1 \sqcup P_2} = R_{P_1} \cup R_{P_2}
\]
这表示程序可能选择执行 \( P_1 \) 或 \( P_2 \)，从而导致不同的输出状态。

### 4. 应用与扩展

关系指称语义学在程序验证中具有重要应用。通过将程序的语义表示为关系，可以方便地使用形式化方法（如霍尔逻辑或抽象解释）来验证程序的性质。此外，关系指称语义学还可以扩展到并发程序、概率程序以及高阶函数等更复杂的语言构造中。

### 5. 总结

关系指称语义学提供了一种强大且灵活的工具，用于形式化描述程序的行为。通过将程序语义建模为关系，可以清晰地表达程序的输入输出行为，并支持组合、迭代以及非确定性等复杂语义的建模。这种方法在程序验证、编译器设计以及形式化方法研究中具有广泛的应用前景。

---

以上是关系指称语义学的进一步讨论。通过深入理解其基本概念与操作，可以更好地应用这一理论工具解决实际问题。 -/

def denote : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       =>
    {st | Prod.snd st = (Prod.fst st)[x ↦ a (Prod.fst st)]}
  | Stmt.seq S T          => denote S ◯ denote T
  | Stmt.ifThenElse B S T =>
    (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      =>
    lfp (fun X ↦ ((denote S ◯ X) ⇃ B)
      ∪ (Id ⇃ (fun s ↦ ¬ B s)))

notation (priority := high) "⟦" S "⟧" => denote S

theorem Monotone_while_lfp_arg (S B) :
    Monotone (fun X ↦ ⟦S⟧ ◯ X ⇃ B ∪ Id ⇃ (fun s ↦ ¬ B s)) :=
  by
    apply Monotone_union
    { apply SorryTheorems.Monotone_restrict
      apply SorryTheorems.Monotone_comp
      { exact Monotone_const _ }
      { exact Monotone_id } }
    { apply SorryTheorems.Monotone_restrict
      exact Monotone_const _ }


/- ## 程序等价性应用

基于指称语义学，我们引入程序等价性的概念：`S₁ ~ S₂`。（与练习9进行比较。） -/

def DenoteEquiv (S₁ S₂ : Stmt) : Prop :=
  ⟦S₁⟧ = ⟦S₂⟧

infix:50 (priority := high) " ~ " => DenoteEquiv

/- 从定义中可以明显看出，`~` 是一个等价关系。

程序等价性可用于将子程序替换为具有相同语义的其他子程序。这是通过以下同余规则实现的： -/

theorem DenoteEquiv.seq_congr {S₁ S₂ T₁ T₂ : Stmt}
      (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    S₁; T₁ ~ S₂; T₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

theorem DenoteEquiv.if_congr {B} {S₁ S₂ T₁ T₂ : Stmt}
      (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

theorem DenoteEquiv.while_congr {B} {S₁ S₂ : Stmt}
      (hS : S₁ ~ S₂) :
    Stmt.whileDo B S₁ ~ Stmt.whileDo B S₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

/- 请比较这些证明的简洁性与大步语义（练习8）中相应证明的简洁性。

让我们证明一些程序等价性。 -/

theorem DenoteEquiv.skip_assign_id {x} :
    Stmt.assign x (fun s ↦ s x) ~ Stmt.skip :=
  by simp [DenoteEquiv, denote, Id]

theorem DenoteEquiv.seq_skip_left {S} :
    Stmt.skip; S ~ S :=
  by simp [DenoteEquiv, denote, Id, comp]

theorem DenoteEquiv.seq_skip_right {S} :
    S; Stmt.skip ~ S :=
  by simp [DenoteEquiv, denote, Id, comp]

theorem DenoteEquiv.if_seq_while {B S} :
    Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip
    ~ Stmt.whileDo B S :=
  by
    simp [DenoteEquiv, denote]
    apply Eq.symm
    apply lfp_eq
    apply Monotone_while_lfp_arg


/- ## 指称语义与大步语义的等价性
## （**可选**） -/

theorem denote_of_BigStep (Ss : Stmt × State) (t : State)
      (h : Ss ⟹ t) :
    (Prod.snd Ss, t) ∈ ⟦Prod.fst Ss⟧ :=
  by
    induction h with
    | skip s => simp [denote]
    | assign x a s => simp [denote]
    | seq S T s t u hS hT ihS ihT =>
      simp [denote]
      aesop
    | if_true B S T s t hB hS ih =>
      simp at *
      simp [denote, *]
    | if_false B S T s t hB hT ih =>
      simp at *
      simp [denote, *]
    | while_true B S s t u hB hS hw ihS ihw =>
      rw [Eq.symm DenoteEquiv.if_seq_while]
      simp at *
      simp [denote, *]
      aesop
    | while_false B S s hB =>
      rw [Eq.symm DenoteEquiv.if_seq_while]
      simp at *
      simp [denote, *]

theorem BigStep_of_denote :
    ∀(S : Stmt) (s t : State), (s, t) ∈ ⟦S⟧ → (S, s) ⟹ t
  | Stmt.skip,             s, t => by simp [denote]
  | Stmt.assign x a,       s, t => by simp [denote]
  | Stmt.seq S T,          s, t =>
    by
      intro hst
      simp [denote] at hst
      cases hst with
      | intro u hu =>
        cases hu with
        | intro hsu hut =>
          apply BigStep.seq
          { exact BigStep_of_denote _ _ _ hsu }
          { exact BigStep_of_denote _ _ _ hut }
  | Stmt.ifThenElse B S T, s, t =>
    by
      intro hst
      simp [denote] at hst
      cases hst with
      | inl htrue =>
        cases htrue with
        | intro hst hB =>
          apply BigStep.if_true
          { exact hB }
          { exact BigStep_of_denote _ _ _ hst }
      | inr hfalse =>
        cases hfalse with
        | intro hst hB =>
          apply BigStep.if_false
          { exact hB }
          { exact BigStep_of_denote _ _ _ hst }
  | Stmt.whileDo B S,      s, t =>
    by
      have hw : ⟦Stmt.whileDo B S⟧
        ≤ {st | (Stmt.whileDo B S, Prod.fst st) ⟹
             Prod.snd st} :=
        by
          apply lfp_le _ _ _
          intro uv huv
          cases uv with
          | mk u v =>
            simp at huv
            cases huv with
            | inl hand =>
              cases hand with
              | intro hst hB =>
                cases hst with
                | intro w hw =>
                  cases hw with
                  | intro huw hw =>
                    apply BigStep.while_true
                    { exact hB }
                    { exact BigStep_of_denote _ _ _ huw }
                    { exact hw }
            | inr hand =>
              cases hand with
              | intro hvu hB =>
                cases hvu
                apply BigStep.while_false
                exact hB
      apply hw

theorem denote_Iff_BigStep (S : Stmt) (s t : State) :
    (s, t) ∈ ⟦S⟧ ↔ (S, s) ⟹ t :=
  Iff.intro (BigStep_of_denote S s t) (denote_of_BigStep (S, s) t)


/- ## 基于归纳谓词的简化方法（**可选**） -/

inductive Awhile (B : State → Prop)
    (r : Set (State × State)) :
  State → State → Prop
  | true {s t u} (hcond : B s) (hbody : (s, t) ∈ r)
      (hrest : Awhile B r t u) :
    Awhile B r s u
  | false {s} (hcond : ¬ B s) :
    Awhile B r s s

def denoteAwhile : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       =>
    {st | Prod.snd st = (Prod.fst st)[x ↦ a (Prod.fst st)]}
  | Stmt.seq S T          => denoteAwhile S ◯ denoteAwhile T
  | Stmt.ifThenElse B S T =>
    (denoteAwhile S ⇃ B)
    ∪ (denoteAwhile T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      =>
    {st | Awhile B (denoteAwhile S) (Prod.fst st)
       (Prod.snd st)}

end LoVe
