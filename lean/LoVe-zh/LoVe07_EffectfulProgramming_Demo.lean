/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe 演示 7：带副作用的编程

单子（Monad）是函数式编程中的一个重要抽象概念。它们通过副作用来泛化计算，使得在纯函数式编程语言中能够进行带副作用的编程。Haskell 已经证明，单子可以非常成功地用于编写命令式程序。对我们来说，单子本身具有研究价值，并且还有以下两个原因：

* 它们为公理化推理提供了一个很好的示例。

* 在 Lean 自身的编程中（元编程，第 8 讲），单子是必需的。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 入门示例

考虑以下编程任务：

    实现一个函数 `sum257 ns`，该函数对自然数列表 `ns` 中的第二、第五和第七个元素求和。使用 `Option ℕ` 作为结果类型，以便在列表元素少于七个时返回 `Option.none`。

一个直接的解决方案如下： -/

def nth {α : Type} : List α → Nat → Option α
  | [],      _     => Option.none
  | x :: _,  0     => Option.some x
  | _ :: xs, n + 1 => nth xs n

def sum257 (ns : List ℕ) : Option ℕ :=
  match nth ns 1 with
  | Option.none    => Option.none
  | Option.some n₂ =>
    match nth ns 4 with
    | Option.none    => Option.none
    | Option.some n₅ =>
      match nth ns 6 with
      | Option.none    => Option.none
      | Option.some n₇ => Option.some (n₂ + n₅ + n₇)

/- 代码显得不够优雅，主要是由于对选项（options）进行了大量的模式匹配（pattern matching）。

我们可以将所有不够优雅的部分集中到一个函数中，这个函数我们称之为 `connect`。 -/

def connect {α : Type} {β : Type} :
  Option α → (α → Option β) → Option β
  | Option.none,   _ => Option.none
  | Option.some a, f => f a

def sum257Connect (ns : List ℕ) : Option ℕ :=
  connect (nth ns 1)
    (fun n₂ ↦ connect (nth ns 4)
       (fun n₅ ↦ connect (nth ns 6)
          (fun n₇ ↦ Option.some (n₂ + n₅ + n₇))))

/- 我们可以使用 Lean 预定义的通用 `bind` 操作，而不是自己定义 `connect`。此外，我们还可以使用 `pure` 来代替 `Option.some`。 -/

#check bind

def sum257Bind (ns : List ℕ) : Option ℕ :=
  bind (nth ns 1)
    (fun n₂ ↦ bind (nth ns 4)
       (fun n₅ ↦ bind (nth ns 6)
          (fun n₇ ↦ pure (n₂ + n₅ + n₇))))

/- 通过使用 `bind` 和 `pure`，`sum257Bind` 没有引用构造函数 `Option.none` 和 `Option.some`。

语法糖：

    `ma >>= f` := `bind ma f`

翻译说明：
- `bind` 和 `pure` 是函数式编程中的常见术语，通常用于描述单子（Monad）的操作，因此保留原文。
- `Option.none` 和 `Option.some` 是特定编程语言（如 Scala 或 Haskell）中的构造函数，表示可选类型的空值和有值情况，保留原文以保持术语的准确性。
- `>>=` 是单子绑定操作的符号，通常用于表示将单子值与函数结合的操作，保留原文符号以保持其特定含义。
- `:=` 表示定义或赋值，保留原文符号以保持其数学或编程中的特定含义。 -/

def sum257Op (ns : List ℕ) : Option ℕ :=
  nth ns 1 >>=
    fun n₂ ↦ nth ns 4 >>=
      fun n₅ ↦ nth ns 6 >>=
        fun n₇ ↦ pure (n₂ + n₅ + n₇)

/- 语法糖：

```plaintext
do
  let a ← ma
  t
:=
ma >>= (fun a ↦ t)

do
  ma
  t
:=
ma >>= (fun _ ↦ t)
```

翻译为中文：

语法糖：

```plaintext
do
  let a ← ma
  t
:=
ma >>= (fun a ↦ t)

do
  ma
  t
:=
ma >>= (fun _ ↦ t)
```

解释：
- **语法糖**：指在编程语言中，为了简化代码书写而引入的语法结构，其本质可以通过更基础的语法结构来实现。
- **do**：一种语法结构，通常用于简化单子（Monad）操作的书写。
- **let a ← ma**：表示从单子操作 `ma` 中提取值并绑定到变量 `a`。
- **ma >>= (fun a ↦ t)**：表示将单子操作 `ma` 的结果传递给一个匿名函数 `(fun a ↦ t)`，其中 `a` 是 `ma` 的结果，`t` 是后续的操作。
- **ma >>= (fun _ ↦ t)**：表示忽略单子操作 `ma` 的结果，直接执行后续操作 `t`。 -/

def sum257Dos (ns : List ℕ) : Option ℕ :=
  do
    let n₂ ← nth ns 1
    do
      let n₅ ← nth ns 4
      do
        let n₇ ← nth ns 6
        pure (n₂ + n₅ + n₇)

/- `do` 语句可以组合使用： -/

def sum257Do (ns : List ℕ) : Option ℕ :=
  do
    let n₂ ← nth ns 1
    let n₅ ← nth ns 4
    let n₇ ← nth ns 6
    pure (n₂ + n₅ + n₇)

/- 尽管这种表示法带有命令式的风格，但该函数是一个纯函数式程序。

## 两种操作与三条定律

`Option` 类型构造器是单子（monad）的一个例子。

一般来说，**单子** 是一个依赖于某个类型参数 `α` 的类型构造器 `m`（即 `m α`），并配备了两个特定的操作：

    `pure {α : Type} : α → m α`
    `bind {α β : Type} : m α → (α → m β) → m β`

对于 `Option` 来说：

    `pure` := `Option.some`
    `bind` := `connect`

直观上，我们可以将单子看作一个“盒子”：

* `pure` 将数据放入盒子中。

* `bind` 允许我们访问盒子中的数据并对其进行修改（甚至可能改变其类型，因为结果是一个 `m β` 单子，而不是 `m α` 单子）。

通常没有通用的方法可以从单子中提取数据，即从 `m α` 中获取 `α`。

总结来说，`pure a` 不会产生副作用，只是提供一个包含值 `a` 的盒子，而 `bind ma f`（也可以写成 `ma >>= f`）会先执行 `ma`，然后用 `ma` 的结果 `a` 执行 `f`。

`Option` 单子只是众多单子中的一个实例。

类型                 | 效果
-------------------- | -------------------------------------------------------
`id`                 | 无副作用
`Option`             | 简单的异常处理
`fun α ↦ σ → α × σ`  | 通过类型为 `σ` 的状态进行传递
`Set`                | 返回 `α` 值的非确定性计算
`fun α ↦ t → α`      | 读取类型为 `t` 的元素（例如，配置）
`fun α ↦ ℕ × α`      | 附加运行时间（例如，用于建模时间复杂度）
`fun α ↦ String × α` | 附加文本输出（例如，用于日志记录）
`IO`                 | 与操作系统的交互
`TacticM`            | 与证明助手的交互

以上所有都是一元类型构造器 `m : Type → Type`。

某些效果可以组合（例如，`Option (t → α)`）。

某些效果是不可执行的（例如，`Set α`）。尽管如此，它们在逻辑中抽象地建模程序时仍然有用。

特定的单子可能提供一种方法，可以在不满足 `bind` 要求的情况下提取存储在单子中的值。

单子有几个优点，包括：

* 它们提供了方便且高度可读的 `do` 表示法。

* 它们支持通用操作，例如 `mmap {α β : Type} : (α → m β) → List α → m (List β)`，这些操作在所有单子中统一工作。

`bind` 和 `pure` 操作通常需要遵守三条定律。作为第一个程序的纯数据可以被简化掉：

    do
      let a' ← pure a,
      f a'
  =
    f a

作为第二个程序的纯数据可以被简化掉：

    do
      let a ← ma
      pure a
  =
    ma

嵌套的程序 `ma`、`f`、`g` 可以使用以下结合律进行扁平化：

    do
      let b ←
        do
          let a ← ma
          f a
      g b
  =
    do
      let a ← ma
      let b ← f a
      g b

## 单子的类型类

单子是一种数学结构，因此我们使用类将它们添加为类型类。我们可以将类型类视为一个由类型参数化的结构，或者在这里，由类型构造器 `m : Type → Type` 参数化的结构。 -/ype)
  extends Pure m, Bind m where
  pure_bind {α β : Type} (a : α) (f : α → m β) :
    (pure a >>= f) = f a
  bind_pure {α : Type} (ma : m α) :
    (ma >>= pure) = ma
  bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ)
      (ma : m α) :
    ((ma >>= f) >>= g) = (ma >>= (fun a ↦ f a >>= g))

/- 逐步说明：

* 我们正在创建一个由一元类型构造器 `m` 参数化的结构。

* 该结构继承了来自 `Bind` 和 `Pure` 结构的字段以及任何语法糖，这些结构提供了对 `m` 的 `bind` 和 `pure` 操作以及一些语法糖。

* 该定义在 `Bind` 和 `Pure` 已经提供的字段基础上，添加了三个字段，用于存储定律的证明。

为了用具体的单子实例化这个定义，我们必须提供类型构造器 `m`（例如，`Option`）、`bind` 和 `pure` 操作符，以及定律的证明。

## 无副作用

我们的第一个单子是平凡单子 `m := id`（即 `m := (fun α ↦ α)`）。 -/

def id.pure {α : Type} : α → id α
  | a => a

def id.bind {α β : Type} : id α → (α → id β) → id β
  | a, f => f a

instance id.LawfulMonad : LawfulMonad id :=
  { pure       := id.pure
    bind       := id.bind
    pure_bind  :=
      by
        intro α β a f
        rfl
    bind_pure  :=
      by
        intro α ma
        rfl
    bind_assoc :=
      by
        intro α β γ f g ma
        rfl }


/- ## 基本异常

正如我们在上文中所见，选项类型提供了一种基本的异常机制。 -/

def Option.pure {α : Type} : α → Option α :=
  Option.some

def Option.bind {α β : Type} :
  Option α → (α → Option β) → Option β
  | Option.none,   _ => Option.none
  | Option.some a, f => f a

instance Option.LawfulMonad : LawfulMonad Option :=
  { pure       := Option.pure
    bind       := Option.bind
    pure_bind  :=
      by
        intro α β a f
        rfl
    bind_pure  :=
      by
        intro α ma
        cases ma with
        | none   => rfl
        | some _ => rfl
    bind_assoc :=
      by
        intro α β γ f g ma
        cases ma with
        | none   => rfl
        | some _ => rfl }

def Option.throw {α : Type} : Option α :=
  Option.none

def Option.catch {α : Type} : Option α → Option α → Option α
  | Option.none,   ma' => ma'
  | Option.some a, _   => Option.some a


/- ## 可变状态

状态单子（state monad）提供了一种对应于可变状态的抽象。某些编译器能够识别状态单子，从而生成高效的命令式代码。 -/

def Action (σ α : Type) : Type :=
  σ → α × σ

def Action.read {σ : Type} : Action σ σ
  | s => (s, s)

def Action.write {σ : Type} (s : σ) : Action σ Unit
  | _ => ((), s)

def Action.pure {σ α : Type} (a : α) : Action σ α
  | s => (a, s)

def Action.bind {σ : Type} {α β : Type} (ma : Action σ α)
      (f : α → Action σ β) :
    Action σ β
  | s =>
    match ma s with
    | (a, s') => f a s'

/- `Action.pure` 类似于 `return` 语句；它不会改变状态。

`Action.bind` 类似于两个语句在状态上的顺序组合。 -/

instance Action.LawfulMonad {σ : Type} :
  LawfulMonad (Action σ) :=
  { pure       := Action.pure
    bind       := Action.bind
    pure_bind  :=
      by
        intro α β a f
        rfl
    bind_pure  :=
      by
        intro α ma
        rfl
    bind_assoc :=
      by
        intro α β γ f g ma
        rfl }

def increasingly : List ℕ → Action ℕ (List ℕ)
  | []        => pure []
  | (n :: ns) =>
    do
      let prev ← Action.read
      if n < prev then
        increasingly ns
      else
        do
          Action.write n
          let ns' ← increasingly ns
          pure (n :: ns')

#eval increasingly [1, 2, 3, 2] 0
#eval increasingly [1, 2, 3, 2, 4, 5, 2] 0


/- ## 非确定性

集合单子（set monad）存储了任意数量（可能是无限个）的 `α` 类型的值。 -/

#check Set

def Set.pure {α : Type} : α → Set α
  | a => {a}

def Set.bind {α β : Type} : Set α → (α → Set β) → Set β
  | A, f => {b | ∃a, a ∈ A ∧ b ∈ f a}

instance Set.LawfulMonad : LawfulMonad Set :=
  { pure       := Set.pure
    bind       := Set.bind
    pure_bind  :=
      by
        intro α β a f
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
    bind_pure  :=
      by
        intro α ma
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
    bind_assoc :=
      by
        intro α β γ f g ma
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
        apply Set.ext
        aesop }

/- `aesop` 是一种通用的证明搜索策略。它能够执行假设中逻辑符号 `∧`、`∨`、`↔` 和 `∃` 的消除，并在目标中引入 `∧`、`↔` 和 `∃`，同时定期调用简化器。它可能成功证明一个目标，也可能失败，或者部分成功，留下一些未完成的子目标供用户处理。

## 通用算法：列表迭代

我们考虑一个通用的带有副作用的程序 `mmap`，它遍历一个列表并对每个元素应用函数 `f`。 -/

def nthsFine {α : Type} (xss : List (List α)) (n : ℕ) :
  List (Option α) :=
  List.map (fun xs ↦ nth xs n) xss

#eval nthsFine [[11, 12, 13, 14], [21, 22, 23]] 2
#eval nthsFine [[11, 12, 13, 14], [21, 22, 23]] 3

def mmap {m : Type → Type} [LawfulMonad m] {α β : Type}
    (f : α → m β) :
  List α → m (List β)
  | []      => pure []
  | a :: as =>
    do
      let b ← f a
      let bs ← mmap f as
      pure (b :: bs)

def nthsCoarse {α : Type} (xss : List (List α)) (n : ℕ) :
  Option (List α) :=
  mmap (fun xs ↦ nth xs n) xss

#eval nthsCoarse [[11, 12, 13, 14], [21, 22, 23]] 2
#eval nthsCoarse [[11, 12, 13, 14], [21, 22, 23]] 3

theorem mmap_append {m : Type → Type} [LawfulMonad m]
      {α β : Type} (f : α → m β) :
    ∀as as' : List α, mmap f (as ++ as') =
      do
        let bs ← mmap f as
        let bs' ← mmap f as'
        pure (bs ++ bs')
  | [],      _   =>
    by simp [mmap, LawfulMonad.bind_pure, LawfulMonad.pure_bind]
  | a :: as, as' =>
    by simp [mmap, mmap_append _ as as', LawfulMonad.pure_bind,
      LawfulMonad.bind_assoc]

end LoVe
