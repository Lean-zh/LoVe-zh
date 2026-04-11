/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe 演示 3：逆向证明

**策略**（tactic）作用于证明目标，要么证明该目标，要么生成新的子目标。策略是一种**逆向**证明机制：它们从目标出发，朝着可用的假设和定理方向进行推理。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## 策略模式

策略证明的语法如下：

    by
      _策略₁_
      …
      _策略N_

关键字 `by` 向 Lean 表明该证明是策略式的。 -/

theorem fst_of_two_props :
    ∀a b : Prop, a → b → a :=
  by
    intro a b
    intro ha hb
    apply ha

/- 请注意，`a → b → a` 被解析为 `a → (b → a)`。

在 Lean 中，命题是类型为 `Prop` 的项。`Prop` 是一个类型，就像 `Nat` 和 `List Bool` 一样。实际上，命题和类型之间存在密切的对应关系，这将在第 4 讲中详细解释。

## 基本策略

`intro` 将 `∀` 量化的变量或蕴含 `→` 的假设从目标的结论（在 `⊢` 之后）移动到目标的前提（在 `⊢` 之前）。

`apply` 将目标的结论与指定定理的结论进行匹配，并将定理的前提作为新的目标添加进来。 -/

theorem fst_of_two_props_params (a b : Prop) (ha : a) (hb : b) :
    a :=
  by apply ha

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  by
    intro ha
    apply hbc
    apply hab
    apply ha

/- 上述证明步骤逐步展开如下：

* 假设我们有一个关于 `a` 的证明。
* 目标是 `c`，如果我们能证明 `b`（通过 `hbc`），则可以达成目标。
* 目标是 `b`，如果我们能证明 `a`（通过 `hab`），则可以达成目标。
* 我们已经知道 `a`（通过 `ha`）。

接下来，`exact` 将目标的结论与指定的定理进行匹配，从而完成该目标。在这种情况下，我们通常可以使用 `apply`，但 `exact` 更能清晰地表达我们的意图。 -/

theorem fst_of_two_props_exact (a b : Prop) (ha : a) (hb : b) :
    a :=
  by exact ha

/- `assumption` 从局部上下文中找到一个与目标结论匹配的假设，并应用该假设来证明目标。 -/

theorem fst_of_two_props_assumption (a b : Prop)
      (ha : a) (hb : b) :
    a :=
  by assumption

/- `rfl` 用于证明 `l = r`，其中等式两边的表达式在计算后是语法上相等的。这里的“计算”指的是定义的展开、β-归约（将 `fun` 应用于参数）、`let` 绑定以及其他相关操作。 -/

theorem α_example {α β : Type} (f : α → β) :
    (fun x ↦ f x) = (fun y ↦ f y) :=
  by rfl

theorem β_example {α β : Type} (f : α → β) (a : α) :
    (fun x ↦ f x) a = f a :=
  by rfl

def double (n : ℕ) : ℕ :=
  n + n

theorem δ_example :
    double 5 = 5 + 5 :=
  by rfl

/- `let` 引入了一个局部作用域的定义。在下面的例子中，`n := 2` 仅在表达式 `n + n` 的作用域内有效。 -/

theorem ζ_example :
    (let n : ℕ := 2
     n + n) = 4 :=
  by rfl

theorem η_example {α β : Type} (f : α → β) :
    (fun x ↦ f x) = f :=
  by rfl

/- `(a, b)` 是一个有序对，其中第一个元素是 `a`，第二个元素是 `b`。`Prod.fst` 是一个所谓的投影函数，用于提取有序对中的第一个元素。 -/

theorem ι_example {α β : Type} (a : α) (b : β) :
    Prod.fst (a, b) = a :=
  by rfl


/- ## 逻辑连接词与量词的推理

### 引入规则： -/

#check True.intro
#check And.intro
#check Or.inl
#check Or.inr
#check Iff.intro
#check Exists.intro

/- 消除规则： -/

#check False.elim
#check And.left
#check And.right
#check Or.elim
#check Iff.mp
#check Iff.mpr
#check Exists.elim

/- 定义 `¬` 及相关定理： -/

#print Not
#check Classical.em
#check Classical.byContradiction

/- 对于 `Not`（`¬`）没有明确的规则，因为 `¬ p` 被定义为 `p → False`。 -/

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

/- 上述证明步骤逐步展开如下：

* 假设我们已知 `a ∧ b`。
* 目标是证明 `b ∧ a`。
* 展示 `b`，如果我们能够展示一个以 `b` 为右侧的合取式，则可以完成此步骤。
* 我们可以做到，因为我们已经拥有 `a ∧ b`。
* 展示 `a`，如果我们能够展示一个以 `a` 为左侧的合取式，则可以完成此步骤。
* 我们可以做到，因为我们已经拥有 `a ∧ b`。

`{ … }` 组合器用于聚焦于特定的子目标。其中的策略必须完全证明该子目标。在下面的证明中，`{ … }` 被用于两个子目标，以赋予证明更多的结构。 -/

theorem And_swap_braces :
    ∀a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    { exact And.right hab }
    { exact And.left hab }

/- 请注意，在上述过程中，我们直接将假设 `hab` 传递给定理 `And.right` 和 `And.left`，而不是等待这些定理的假设作为新的子目标出现。这是一个在整体上以逆向推理为主的证明中的一小步正向推理。 -/

opaque f : ℕ → ℕ

theorem f5_if (h : ∀n : ℕ, f n = n) :
    f 5 = 5 :=
  by exact h 5

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  by
    intro hab
    apply Or.elim hab
    { intro ha
      exact Or.inr ha }
    { intro hb
      exact Or.inl hb }

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  by
    intro hab ha
    apply hab
    exact ha

theorem Not_Not_intro (a : Prop) :
    a → ¬¬ a :=
  by
    intro ha hna
    apply hna
    exact ha

theorem Exists_double_iden :
    ∃n : ℕ, double n = n :=
  by
    apply Exists.intro 0
    rfl


/- ## 关于等式的推理 -/

#check Eq.refl
#check Eq.symm
#check Eq.trans
#check Eq.subst

/- 上述规则可以直接使用： -/

theorem Eq_trans_symm {α : Type} (a b c : α)
      (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    apply Eq.trans
    { exact hab }
    { apply Eq.symm
      exact hcb }

/- `rw` 将单个等式从左到右应用一次，作为重写规则。若要从右到左应用等式，请在其名称前加上 `←`。 -/

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
      (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    rw [hab]
    rw [hcb]

/- `rw` 可以展开一个定义。在下面的例子中，`¬¬ a` 被展开为 `¬ a → False`，而 `¬ a` 被展开为 `a → False`。 -/

theorem a_proof_of_negation (a : Prop) :
    a → ¬¬ a :=
  by
    rw [Not]
    rw [Not]
    intro ha
    intro hna
    apply hna
    exact ha

/- `simp` 会详尽地应用一组标准的重写规则（即 __simp 集__）。该集合可以通过 `@[simp]` 属性进行扩展。定理可以通过语法 `simp [_theorem₁_, …, _theoremN_]` 临时添加到 simp 集中。 -/

theorem cong_two_args_1p1 {α : Type} (a b c d : α)
      (g : α → α → ℕ → α) (hab : a = b) (hcd : c = d) :
    g a c (1 + 1) = g b d 2 :=
  by simp [hab, hcd]

/- `ac_rfl` 类似于 `rfl`，但它能够推理出 `+`、`*` 以及其他二元运算符的结合律和交换律。 -/

theorem abc_Eq_cba (a b c : ℕ) :
    a + b + c = c + b + a :=
  by ac_rfl


/- ## 数学归纳法证明

`induction` 对指定的变量执行归纳。它为每个构造函数生成一个命名的子目标。 -/

theorem add_zero (n : ℕ) :
    add 0 n = n :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

theorem add_succ (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  by
    induction n with
    | zero       => simp [add, add_zero]
    | succ n' ih => simp [add, add_succ, ih]

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

/- `ac_rfl` 是可扩展的。我们可以通过类型类实例机制（在第5讲中已解释）将 `add` 注册为一个交换且结合的运算符。这对于下面调用的 `ac_rfl` 非常有用。 -/

instance Associative_add : Std.Associative add :=
  { assoc := add_assoc }

instance Commutative_add : Std.Commutative add :=
  { comm := add_comm }

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih =>
      simp [add, mul, ih]
      ac_rfl


/- ## 清理策略

`clear` 用于移除未使用的变量或假设。

`rename` 用于更改变量或假设的名称。 -/

theorem cleanup_example (a b c : Prop) (ha : a) (hb : b)
      (hab : a → b) (hbc : b → c) :
    c :=
  by
    clear ha hab a
    apply hbc
    clear hbc c
    rename b => h
    exact h

end BackwardProofs

end LoVe
