/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe 演示 4：正向证明

在开发证明时，通常采用**正向**的方式进行是有意义的：从我们已经知道的内容开始，逐步推进到我们的目标。Lean 的结构化证明和原始证明项是两种支持正向推理的风格。 -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace ForwardProofs


/- ## 结构化构造

结构化证明是撒在Lean的**证明项**之上的语法糖。

最简单的结构化证明形式是定理的名称，可能带有参数。 -/

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  sorry

theorem add_comm_zero_left (n : ℕ) :
    add 0 n = add n 0 :=
  add_comm 0 n

/- 等效逆向证明： -/

theorem add_comm_zero_left_by_exact (n : ℕ) :
    add 0 n = add n 0 :=
  by exact add_comm 0 n

/- `fix` 和 `assume` 将目标中的 `∀` 量词变量和假设移动到局部上下文中。它们可以被视为 `intro` 策略的结构化版本。

`show` 重复需要证明的目标。它对于文档记录或重新表述目标（直到计算）非常有用。 -/

theorem fst_of_two_props :
    ∀a b : Prop, a → b → a :=
  fix a b : Prop
  assume ha : a
  assume hb : b
  show a from
    ha

theorem fst_of_two_props_show (a b : Prop) (ha : a) (hb : b) :
    a :=
  show a from
    ha

theorem fst_of_two_props_no_show (a b : Prop) (ha : a) (hb : b) :
    a :=
  ha

/- `have` 用于证明一个中间定理，该定理可以引用局部上下文。 -/

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  assume ha : a
  have hb : b :=
    hab ha
  have hc : c :=
    hbc hb
  show c from
    hc

theorem prop_comp_inline (a b c : Prop) (hab : a → b)
    (hbc : b → c) :
  a → c :=
  assume ha : a
  show c from
    hbc (hab ha)


/- ## 关于连接词和量词的前向推理 -/

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a :=
  assume hab : a ∧ b
  have ha : a :=
    And.left hab
  have hb : b :=
    And.right hab
  show b ∧ a from
    And.intro hb ha

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  assume hab : a ∨ b
  show b ∨ a from
    Or.elim hab
      (assume ha : a
       show b ∨ a from
         Or.inr ha)
      (assume hb : b
       show b ∨ a from
         Or.inl hb)

def double (n : ℕ) : ℕ :=
  n + n

theorem Nat_exists_double_iden :
    ∃n : ℕ, double n = n :=
  Exists.intro 0
    (show double 0 = 0 from
     by rfl)

theorem Nat_exists_double_iden_no_show :
    ∃n : ℕ, double n = n :=
  Exists.intro 0 (by rfl)

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  assume hab : a → b
  assume ha : a
  show b from
    hab ha

theorem not_not_intro (a : Prop) :
    a → ¬¬ a :=
  assume ha : a
  assume hna : ¬ a
  show False from
    hna ha

/- 正如您可以在逆向证明中应用正向推理一样，您也可以在正向证明中应用逆向推理（使用 `by` 表示）： -/

theorem Forall.one_point {α : Type} (t : α) (P : α → Prop) :
    (∀x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume hall : ∀x, x = t → P x
     show P t from
       by
         apply hall t
         rfl)
    (assume hp : P t
     fix x : α
     assume heq : x = t
     show P x from
       by
         rw [heq]
         exact hp)

theorem beast_666 (beast : ℕ) :
    (∀n, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
  Forall.one_point _ _

#print beast_666

theorem Exists.one_point {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume hex : ∃x, x = t ∧ P x
     show P t from
       Exists.elim hex
         (fix x : α
          assume hand : x = t ∧ P x
          have hxt : x = t :=
            And.left hand
          have hpx : P x :=
            And.right hand
          show P t from
            by
              rw [←hxt]
              exact hpx))
    (assume hp : P t
     show ∃x : α, x = t ∧ P x from
       Exists.intro t
         (have tt : t = t :=
            by rfl
          show t = t ∧ P t from
            And.intro tt hp))


/- ## 计算式证明

在非正式的数学中，我们经常使用等式、不等式或等价关系的传递链（例如，`a ≥ b ≥ c`）。在 Lean 中，这种计算式证明由 `calc` 支持。

语法：

    calc
      _项₀_ _操作₁_ _项₁_ :=
        _证明₁_
      _ _操作₂_ _项₂_ :=
        _证明₂_
     ⋮
      _ _操作N_ _项N_ :=
        _证明N_ -/

theorem two_mul_example (m n : ℕ) :
    2 * m + n = m + n + m :=
  calc
    2 * m + n = m + m + n :=
      by rw [Nat.two_mul]
    _ = m + n + m :=
      by ac_rfl

/- `calc` 节省了一些重复的步骤、一些 `have` 标签以及一些传递性推理： -/

theorem two_mul_example_have (m n : ℕ) :
    2 * m + n = m + n + m :=
  have hmul : 2 * m + n = m + m + n :=
    by rw [Nat.two_mul]
  have hcomm : m + m + n = m + n + m :=
    by ac_rfl
  show _ from
    Eq.trans hmul hcomm


/- ## 使用策略进行前向推理

`have`、`let` 和 `calc` 这些结构化证明命令也可以作为策略使用。即使在策略模式下，以向前推进的方式陈述中间结果和定义仍然非常有用。 -/

theorem prop_comp_tactical (a b c : Prop) (hab : a → b)
    (hbc : b → c) :
    a → c :=
  by
    intro ha
    have hb : b :=
      hab ha
    let c' := c
    have hc : c' :=
      hbc hb
    exact hc


/- ## 依赖类型

依赖类型是依赖类型理论家族逻辑的定义性特征。

考虑一个函数 `pick`，它接受一个数字 `n : ℕ` 并返回一个介于 0 和 `n` 之间的数字。从概念上讲，`pick` 具有一个依赖类型，即

    `(n : ℕ) → {i : ℕ // i ≤ n}`

我们可以将这个类型视为一个 `ℕ` 索引的族，其中每个成员的类型可能依赖于索引：

    `pick n : {i : ℕ // i ≤ n}`

但一个类型也可能依赖于另一个类型，例如 `List`（或 `fun α ↦ List α`）和 `fun α ↦ α → α`。

一个项可能依赖于一个类型，例如 `fun α ↦ fun (x : α) ↦ x`（一个多态恒等函数）。

当然，一个项也可能依赖于另一个项。

除非另有说明，**依赖类型** 指的是依赖于项的类型。这就是我们说简单类型理论不支持依赖类型时的含义。

总结一下，在归纳构造演算中（参见 Barendregt 的 `λ`-立方体），`fun x ↦ t` 有四种情况：

主体 (`t`) |              | 参数 (`x`) | 描述
---------- | ------------ | ---------- | ----------------------------------
一个项     | 依赖于       | 一个项     | 简单类型的匿名函数
一个类型   | 依赖于       | 一个项     | 依赖类型（严格来说）
一个项     | 依赖于       | 一个类型   | 多态项
一个类型   | 依赖于       | 一个类型   | 类型构造器

修订后的类型规则：

    C ⊢ t : (x : σ) → τ[x]    C ⊢ u : σ
    ———————————————————————————————————— App'
    C ⊢ t u : τ[u]

    C, x : σ ⊢ t : τ[x]
    ———————————————————————————————————— Fun'
    C ⊢ (fun x : σ ↦ t) : (x : σ) → τ[x]

如果 `x` 不在 `τ[x]` 中出现，这两条规则退化为 `App` 和 `Fun`。

`App'` 的示例：

    ⊢ pick : (n : ℕ) → {i : ℕ // i ≤ n}    ⊢ 5 : ℕ
    ——————————————————————————————————————————————— App'
    ⊢ pick 5 : {i : ℕ // i ≤ 5}

`Fun'` 的示例：

    α : Type, x : α ⊢ x : α
    —————————————————————————————————— Fun 或 Fun'
    α : Type ⊢ (fun x : α ↦ x) : α → α
    ————————————————————————————————————————————————————— Fun'
    ⊢ (fun α : Type ↦ fun x : α ↦ x) : (α : Type) → α → α

值得注意的是，全称量化只是依赖类型的别名：

    `∀x : σ, τ` := `(x : σ) → τ`

这一点在下面会变得更加清晰。

## PAT 原则

`→` 既用作蕴涵符号，也用作函数的类型构造器。这两对概念不仅看起来相同，而且根据 PAT 原则，它们是相同的：

* PAT = 命题即类型；
* PAT = 证明即项。

类型：

* `σ → τ` 是从 `σ` 到 `τ` 的全函数类型。
* `(x : σ) → τ[x]` 是从 `x : σ` 到 `τ[x]` 的依赖函数类型。

命题：

* `P → Q` 可以读作“`P` 蕴涵 `Q`”，或者作为将 `P` 的证明映射到 `Q` 的证明的函数类型。
* `∀x : σ, Q[x]` 可以读作“对于所有 `x`，`Q[x]`”，或者作为类型为 `(x : σ) → Q[x]` 的函数类型，将类型为 `σ` 的值 `x` 映射到 `Q[x]` 的证明。

项：

* 常量是一个项。
* 变量是一个项。
* `t u` 是将函数 `t` 应用于值 `u`。
* `fun x ↦ t[x]` 是一个将 `x` 映射到 `t[x]` 的函数。

证明：

* 定理或假设名称是一个证明。
* `H t`，它将证明 `H` 的语句中的前导参数或量词实例化为项 `t`，是一个证明。
* `H G`，它用证明 `G` 来解除 `H` 的语句中的前导假设，是一个证明。
* `fun h : P ↦ H[h]` 是 `P → Q` 的证明，假设 `H[h]` 是 `Q` 对于 `h : P` 的证明。
* `fun x : σ ↦ H[x]` 是 `∀x : σ, Q[x]` 的证明，假设 `H[x]` 是 `Q[x]` 对于 `x : σ` 的证明。
theorem And_swap_raw (a b : Prop) :
    a ∧ b → b ∧ a :=
  fun hab : a ∧ b ↦ And.intro (And.right hab) (And.left hab)

theorem And_swap_tactical (a b : Prop) :
    a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

/- 战术证明被简化为证明项。 -/

#print And_swap
#print And_swap_raw
#print And_swap_tactical

end ForwardProofs


/- ## 通过模式匹配和递归进行归纳

根据PAT（Proofs as Types）原则，归纳证明与递归定义的证明项是相同的。因此，作为`induction`策略的替代方案，归纳也可以通过模式匹配和递归来完成：

* 归纳假设可以在我们正在证明的定理的名称下使用；

* 参数的良基性通常会自动得到证明。 -/

#check reverse

theorem reverse_append {α : Type} :
    ∀xs ys : List α,
      reverse (xs ++ ys) = reverse ys ++ reverse xs
  | [],      ys => by simp [reverse]
  | x :: xs, ys => by simp [reverse, reverse_append xs]

theorem reverse_append_tactical {α : Type} (xs ys : List α) :
    reverse (xs ++ ys) = reverse ys ++ reverse xs :=
  by
    induction xs with
    | nil           => simp [reverse]
    | cons x xs' ih => simp [reverse, ih]

theorem reverse_reverse {α : Type} :
    ∀xs : List α, reverse (reverse xs) = xs
  | []      => by rfl
  | x :: xs =>
    by simp [reverse, reverse_append, reverse_reverse xs]

end LoVe
