/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe 演示 12：数学的逻辑基础

我们深入探讨 Lean 的逻辑基础。本文描述的大多数特性特别适用于定义数学对象并证明与之相关的定理。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 宇宙（Universes）

不仅项（terms）具有类型，类型本身也具有类型。例如：

    `@And.intro : ∀a b, a → b → a ∧ b`

以及

    `∀a b, a → b → a ∧ b : Prop`

那么，`Prop` 的类型是什么？`Prop` 的类型与我们迄今为止构造的几乎所有其他类型相同：

    `Prop : Type`

`Type` 的类型又是什么？如果写成 `Type : Type`，会导致一个矛盾，称为 **吉拉尔悖论（Girard's paradox）**，类似于罗素悖论（Russell's paradox）。因此，取而代之的是：

    `Type   : Type 1`
    `Type 1 : Type 2`
    `Type 2 : Type 3`
    ⋮

别名：

    `Type`   := `Type 0`
    `Prop`   := `Sort 0`
    `Type u` := `Sort (u + 1)`

类型的类型（`Sort u`、`Type u` 和 `Prop`）被称为 **宇宙（universes）**。`Sort u` 中的 `u` 被称为 **宇宙层级（universe level）**。

这种层级关系通过以下类型判断（typing judgment）来体现：

    ————————————————————————— Sort
    C ⊢ Sort u : Sort (u + 1) -/

#check @And.intro
#check ∀a b : Prop, a → b → a ∧ b
#check Prop
#check ℕ
#check Type
#check Type 1
#check Type 2

universe u v

#check Type u

#check Sort 0
#check Sort 1
#check Sort 2
#check Sort u

#check Type _


/- ## Prop 的特殊性

`Prop` 在许多方面与其他宇宙（universe）不同。

### 非直谓性（Impredicativity）

函数类型 `σ → τ` 被放入 `σ` 和 `τ` 所在的较大宇宙中：

    C ⊢ σ : Type u    C ⊢ τ : Type v
    ————————————————————————————————— SimpleArrow-Type
    C ⊢ σ → τ : Type (max u v)

对于依赖类型，这可以推广为：

    C ⊢ σ : Type u    C, x : σ ⊢ τ[x] : Type v
    ——————————————————————————————————————————— Arrow-Type
    C ⊢ (x : σ) → τ[x] : Type (max u v)

宇宙 `Type v` 的这种行为被称为**直谓性（predicativity）**。

为了强制将诸如 `∀a : Prop, a → a` 这样的表达式仍然归类为 `Prop` 类型，我们需要为 `Prop` 制定一个特殊的类型规则：

    C ⊢ σ : Sort u    x : σ ⊢ τ[x] : Prop
    —————————————————————————————————————— Arrow-Prop
    C ⊢ (∀x : σ, τ[x]) : Prop

`Prop` 的这种行为被称为**非直谓性（impredicativity）**。

规则 `Arrow-Type` 和 `Arrow-Prop` 可以推广为一条规则：

    C ⊢ σ : Sort u    C, x : σ ⊢ τ[x] : Sort v
    ——————————————————————————————————————————— Arrow
    C ⊢ (x : σ) → τ[x] : Sort (imax u v)

其中

    `imax u 0       = 0`
    `imax u (v + 1) = max u (v + 1)` -/

#check fun (α : Type u) (β : Type v) ↦ α → β
#check ∀a : Prop, a → a


/- ### 证明无关性

`Prop` 和 `Type u` 之间的第二个区别是 **证明无关性**：

    `∀(a : Prop) (h₁ h₂ : a), h₁ = h₂`

这使得依赖类型的推理更加容易。

当我们将命题视为类型，并将证明视为该类型的元素时，证明无关性意味着一个命题要么是一个空类型，要么恰好有一个元素。

证明无关性可以通过 `rfl` 来证明。

证明无关性的一个不幸后果是，它阻止了我们通过模式匹配和递归来执行规则归纳。 -/

#check proof_irrel

theorem proof_irrel {a : Prop} (h₁ h₂ : a) :
    h₁ = h₂ :=
  by rfl


/- ### 无大消去

`Prop` 和 `Type u` 之间的另一个区别是，`Prop` 不允许**大消去**（large elimination），这意味着无法从命题的证明中提取数据。

这是为了保证**证明无关性**（proof irrelevance）所必需的。 -/

/-
-- 失败
def unsquare (i : ℤ) (hsq : ∃j, i = j * j) : ℤ :=
  match hsq with
  | Exists.intro j _ => j
-/

/- 如果上述内容被接受，我们可以按如下方式推导出 `False`。

令

    `hsq₁` := `Exists.intro 3 (by linarith)`
    `hsq₂` := `Exists.intro (-3) (by linarith)`

为 `∃j, (9 : ℤ) = j * j` 的两个证明。那么

    `unsquare 9 hsq₁ = 3`
    `unsquare 9 hsq₂ = -3`

然而，根据证明无关性（proof irrelevance），`hsq₁ = hsq₂`。因此

    `unsquare 9 hsq₂ = 3`

从而

    `3 = -3`

这是一个矛盾。

作为一种折衷方案，Lean 允许**小消去**（small elimination）。之所以称为小消去，是因为它只能消除到 `Prop` 中，而大消去（large elimination）可以消除到任意大的宇宙 `Sort u` 中。这意味着我们可以使用 `match` 来分析证明的结构、提取存在性见证等，只要 `match` 表达式本身是一个证明。我们在第5讲中已经看到了几个这样的例子。

作为进一步的折衷，Lean 允许对**语法单例**（syntactic subsingletons）进行大消去：这些是 `Prop` 中的类型，可以通过语法方式确定它们的基数为0或1。这些命题包括 `False` 和 `a ∧ b` 等，它们最多只能以一种方式被证明。

## 选择公理

Lean 的逻辑包含了选择公理（Axiom of Choice），这使得从任何非空类型中获取任意元素成为可能。

考虑 Lean 的 `Nonempty` 归纳谓词： -/

#print Nonempty

/- 该谓词表明 `α` 至少有一个元素。

为了证明 `Nonempty α`，我们必须向 `Nonempty.intro` 提供一个 `α` 值。 -/

theorem Nat.Nonempty :
    Nonempty ℕ :=
  Nonempty.intro 0

/- 由于 `Nonempty` 存在于 `Prop` 中，无法进行大范围消除（large elimination），因此我们无法从 `Nonempty α` 的证明中提取出所使用的元素。

选择公理（axiom of choice）允许我们在能够证明 `Nonempty α` 的情况下，获取某个类型为 `α` 的元素。 -/

#check Classical.choice

/- 这将仅仅为我们提供一个 `α` 的任意元素；我们无法确定这是否是用于证明 `Nonempty α` 的那个元素。

常量 `Classical.choice` 是不可计算的，这就是为什么一些逻辑学家倾向于在没有这个公理的情况下工作。 -/

/- #eval Classical.choice Nat.Nonempty     -- 失败
#reduce Classical.choice Nat.Nonempty

/- 选择公理在Lean的核心库中仅作为一条公理存在，这为用户提供了选择是否使用它的自由。

使用选择公理的定义必须标记为`noncomputable`（不可计算的）。 -/

noncomputable def arbitraryNat : ℕ :=
  Classical.choice Nat.Nonempty


### 排中律 -/

#check Classical.em


/- ### 希尔伯特选择 -/

#check Classical.choose
#check Classical.choose_spec


/- ### 集合论的选择公理 -/

#print Classical.axiomOfChoice


/- ## 子类型

子类型化是一种从现有类型创建新类型的机制。

给定一个关于基类型元素的谓词，**子类型**仅包含满足该属性的基类型元素。更准确地说，子类型包含元素-证明对，这些对由基类型的元素和证明其满足该属性的证明组成。

子类型化对于那些无法定义为归纳类型的类型非常有用。例如，任何尝试按照以下方式定义有限集类型的尝试都注定会失败： -/

inductive Finset (α : Type) : Type
  | empty  : Finset α
  | insert : α → Finset α → Finset α

/- 为什么这不适用于有限集合的建模？

给定一个基类型和一个属性，子类型的语法如下：

    `{` _变量_ `:` _基类型_ `//` _应用于变量的属性_ `}`

别名：

    `{x : τ // P[x]}` := `@Subtype τ (fun x ↦ P[x])`

示例：

    `{i : ℕ // i ≤ n}`            := `@Subtype ℕ (fun i ↦ i ≤ n)`
    `{A : Set α // Set.Finite A}` := `@Subtype (Set α) Set.Finite`

### 第一个示例：满二叉树 -/

#check Tree
#check IsFull
#check mirror
#check IsFull_mirror
#check mirror_mirror

def FullTree (α : Type) : Type :=
  {t : Tree α // IsFull t}

#print Subtype
#check Subtype.mk

/- 要定义 `FullTree` 的元素，我们需要提供一个 `Tree` 并证明它是满的： -/

def nilFullTree : FullTree ℕ :=
  Subtype.mk Tree.nil IsFull.nil

def fullTree6 : FullTree ℕ :=
  Subtype.mk (Tree.node 6 Tree.nil Tree.nil)
    (by
       apply IsFull.node
       apply IsFull.nil
       apply IsFull.nil
       rfl)

#reduce Subtype.val fullTree6
#check Subtype.property fullTree6

/- 我们可以将现有的 `Tree` 操作提升到 `FullTree` 上： -/

def FullTree.mirror {α : Type} (t : FullTree α) :
  FullTree α :=
  Subtype.mk (LoVe.mirror (Subtype.val t))
    (by
       apply IsFull_mirror
       apply Subtype.property t)

#reduce Subtype.val (FullTree.mirror fullTree6)

/- 当然，我们可以证明关于提升操作的定理： -/

theorem FullTree.mirror_mirror {α : Type}
      (t : FullTree α) :
    (FullTree.mirror (FullTree.mirror t)) = t :=
  by
    apply Subtype.eq
    simp [FullTree.mirror, LoVe.mirror_mirror]

#check Subtype.eq


/- ### 第二个示例：向量 -/

def Vector (α : Type) (n : ℕ) : Type :=
  {xs : List α // List.length xs = n}

def vector123 : Vector ℤ 3 :=
  Subtype.mk [1, 2, 3] (by rfl)

def Vector.neg {n : ℕ} (v : Vector ℤ n) : Vector ℤ n :=
  Subtype.mk (List.map Int.neg (Subtype.val v))
    (by
       rw [List.length_map]
       exact Subtype.property v)

theorem Vector.neg_neg (n : ℕ) (v : Vector ℤ n) :
    Vector.neg (Vector.neg v) = v :=
  by
    apply Subtype.eq
    simp [Vector.neg]


/- ## 商类型

商类型是数学中一种强大的构造方法，用于构建 `ℤ`、`ℚ`、`ℝ` 以及许多其他类型。

与子类型类似，商类型也是从现有类型中构造出一个新类型。但与子类型不同的是，商类型包含了基类型的所有元素，只不过在基类型中不同的某些元素在商类型中被视为相等。用数学术语来说，商类型与基类型的一个划分是同构的。

要定义一个商类型，我们需要提供一个基类型以及一个等价关系，该等价关系决定了哪些元素在商类型中被视为相等。 -/

#check Quotient
#print Setoid

#check Quotient.mk
#check Quotient.sound
#check Quotient.exact

#check Quotient.lift
#check Quotient.lift₂
#check @Quotient.inductionOn


/- ## 第一个示例：整数

让我们通过自然数对 `ℕ × ℕ` 的商集来构建整数 `ℤ`。

一个自然数对 `(p, n)` 表示整数 `p - n`。非负整数 `p` 可以用 `(p, 0)` 表示。负整数 `-n` 可以用 `(0, n)` 表示。然而，同一个整数可能有多种表示方式；例如，`(7, 0)`、`(8, 1)`、`(9, 2)` 和 `(10, 3)` 都表示整数 `7`。

我们应该使用哪种等价关系呢？

我们希望当 `p₁ - n₁ = p₂ - n₂` 时，两个对 `(p₁, n₁)` 和 `(p₂, n₂)` 相等。然而，这在 `ℕ` 上并不适用，因为减法在 `ℕ` 上表现不佳（例如，`0 - 1 = 0`）。因此，我们改用 `p₁ + n₂ = p₂ + n₁`。 -/

instance Int.Setoid : Setoid (ℕ × ℕ) :=
  { r :=
      fun pn₁ pn₂ : ℕ × ℕ ↦
        Prod.fst pn₁ + Prod.snd pn₂ =
        Prod.fst pn₂ + Prod.snd pn₁
    iseqv :=
      { refl :=
          by
            intro pn
            rfl
        symm :=
          by
            intro pn₁ pn₂ h
            rw [h]
        trans :=
          by
            intro pn₁ pn₂ pn₃ h₁₂ h₂₃
            linarith } }

theorem Int.Setoid_Iff (pn₁ pn₂ : ℕ × ℕ) :
    pn₁ ≈ pn₂ ↔
    Prod.fst pn₁ + Prod.snd pn₂ =
    Prod.fst pn₂ + Prod.snd pn₁ :=
  by rfl

def Int : Type :=
  Quotient Int.Setoid

def Int.zero : Int :=
  ⟦(0, 0)⟧

theorem Int.zero_Eq (m : ℕ) :
    Int.zero = ⟦(m, m)⟧ :=
  by
    rw [Int.zero]
    apply Quotient.sound
    rw [Int.Setoid_Iff]
    simp

def Int.add : Int → Int → Int :=
  Quotient.lift₂
    (fun pn₁ pn₂ : ℕ × ℕ ↦
       ⟦(Prod.fst pn₁ + Prod.fst pn₂,
         Prod.snd pn₁ + Prod.snd pn₂)⟧)
    (by
       intro pn₁ pn₂ pn₁' pn₂' h₁ h₂
       apply Quotient.sound
       rw [Int.Setoid_Iff] at *
       linarith)

theorem Int.add_Eq (p₁ n₁ p₂ n₂ : ℕ) :
    Int.add ⟦(p₁, n₁)⟧ ⟦(p₂, n₂)⟧ =
    ⟦(p₁ + p₂, n₁ + n₂)⟧ :=
  by rfl

theorem Int.add_zero (i : Int) :
    Int.add Int.zero i = i :=
  by
    induction i using Quotient.inductionOn with
    | h pn =>
      cases pn with
      | mk p n => simp [Int.zero, Int.add]

/- 这个定义语法会很不错： -/

/-
-- 失败
def Int.add : Int → Int → Int
  | ⟦(p₁, n₁)⟧, ⟦(p₂, n₂)⟧ => ⟦(p₁ + p₂, n₁ + n₂)⟧
-/

/- 不过这会很危险： -/

/- -- 失败
def Int.fst : Int → ℕ
  | ⟦(p, n)⟧ => p
-/

/- 使用 `Int.fst`，我们可以推导出 `False`。首先，我们有

    `Int.fst ⟦(0, 0)⟧ = 0`
    `Int.fst ⟦(1, 1)⟧ = 1`

但由于 `⟦(0, 0)⟧ = ⟦(1, 1)⟧`，我们得到

    `0 = 1` -/


/- ### 第二个示例：无序对

__无序对__ 是指不区分第一个和第二个元素的对。它们通常写作 `{a, b}`。

我们将引入无序对的类型 `UPair`，作为对 `(a, b)` 关于“包含相同元素”关系的商类型。 -/

instance UPair.Setoid (α : Type) : Setoid (α × α) :=
{ r :=
    fun ab₁ ab₂ : α × α ↦
      ({Prod.fst ab₁, Prod.snd ab₁} : Set α) =
      ({Prod.fst ab₂, Prod.snd ab₂} : Set α)
  iseqv :=
    { refl  := by simp
      symm  := by aesop
      trans := by aesop } }

theorem UPair.Setoid_Iff {α : Type} (ab₁ ab₂ : α × α) :
    ab₁ ≈ ab₂ ↔
    ({Prod.fst ab₁, Prod.snd ab₁} : Set α) =
    ({Prod.fst ab₂, Prod.snd ab₂} : Set α) :=
  by rfl

def UPair (α : Type) : Type :=
  Quotient (UPair.Setoid α)

#check UPair.Setoid

/- 很容易证明我们的配对确实是无序的： -/

theorem UPair.mk_symm {α : Type} (a b : α) :
    (⟦(a, b)⟧ : UPair α) = ⟦(b, a)⟧ :=
  by
    apply Quotient.sound
    rw [UPair.Setoid_Iff]
    aesop

/- 无序对的另一种表示形式是基数为1或2的集合。以下操作将`UPair`转换为该表示形式： -/

def Set_of_UPair {α : Type} : UPair α → Set α :=
  Quotient.lift (fun ab : α × α ↦ {Prod.fst ab, Prod.snd ab})
    (by
       intro ab₁ ab₂ h
       rw [UPair.Setoid_Iff] at *
       exact h)


/- ### 通过归一化和子类型化的替代定义

商类型的每个元素对应于一个`≈`等价类。如果存在一种系统化的方法来为每个类获取**规范代表**，我们可以使用子类型而不是商类型，仅保留规范代表。

考虑上述的商类型`Int`。我们可以说，如果`p`或`n`为`0`，则一对`(p, n)`是**规范的**。 -/

namespace Alternative

inductive Int.IsCanonical : ℕ × ℕ → Prop
  | nonpos {n : ℕ} : Int.IsCanonical (0, n)
  | nonneg {p : ℕ} : Int.IsCanonical (p, 0)

def Int : Type :=
  {pn : ℕ × ℕ // Int.IsCanonical pn}

/- **归一化**自然数对的操作非常简单： -/

def Int.normalize : ℕ × ℕ → ℕ × ℕ
  | (p, n) => if p ≥ n then (p - n, 0) else (0, n - p)

theorem Int.IsCanonical_normalize (pn : ℕ × ℕ) :
    Int.IsCanonical (Int.normalize pn) :=
  by
    cases pn with
    | mk p n =>
      simp [Int.normalize]
      cases Classical.em (p ≥ n) with
      | inl hpn =>
        simp [*]
        exact Int.IsCanonical.nonneg
      | inr hpn =>
        simp [*]
        exact Int.IsCanonical.nonpos

/- 对于无序对，除了始终将较小的元素放在前面（或后面）之外，没有明显的标准形式。这需要在类型 `α` 上定义一个线性序 `≤`。 -/

def UPair.IsCanonical {α : Type} [LinearOrder α] :
  α × α → Prop
  | (a, b) => a ≤ b

def UPair (α : Type) [LinearOrder α] : Type :=
  {ab : α × α // UPair.IsCanonical ab}

end Alternative

end LoVe
