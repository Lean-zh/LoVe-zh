/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe 演示 2：程序与定理

我们继续学习 Lean 的基础知识，重点关注程序和定理，但暂不进行任何证明。我们将回顾如何定义新类型和函数，以及如何将它们的预期性质表述为定理。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 类型定义

**归纳类型**（也称为**归纳数据类型**、**代数数据类型**，或简称为**数据类型**）是一种类型，它包含所有可以通过其**构造器**有限次应用构建的值，且仅包含这些值。

### 自然数 -/

namespace MyNat

/- 自然数类型 `Nat`（即 `ℕ`）的定义，采用一元表示法： -/

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

#check Nat
#check Nat.zero
#check Nat.succ

/- `#print` 输出其参数的定义。 -/

#print Nat

end MyNat

/- 在命名空间 `MyNat` 之外，`Nat` 指的是 Lean 核心库中定义的类型，除非它被 `MyNat` 命名空间限定。 -/

#print Nat
#print MyNat.Nat


/- ### 算术表达式 -/

inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp


/- ### 列表 -/

namespace MyList

inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α

#check List
#check List.nil
#check List.cons
#print List

end MyList

#print List
#print MyList.List


/- ## 函数定义

定义作用于归纳类型上的函数语法非常简洁：我们定义一个单一函数，并使用**模式匹配**来提取构造器的参数。 -/

def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

/- 当存在多个参数时，使用 `,` 分隔各个模式： -/

def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

/- `#eval` 和 `#reduce` 用于评估并输出一个项的值。 -/

#eval add 2 7
#reduce add 2 7

def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => Nat.zero
  | m, Nat.succ n => add m (mul m n)

#eval mul 2 7

#print mul

def power : ℕ → ℕ → ℕ
  | _, Nat.zero   => 1
  | m, Nat.succ n => mul m (power m n)

#eval power 2 5

/- `add`、`mul` 和 `power` 是人为设计的示例。这些操作在 Lean 中已经以 `+`、`*` 和 `^` 的形式提供。

如果不需要对某个参数进行模式匹配，可以将其移到 `:` 的左侧，并将其设为命名参数： -/

def powerParam (m : ℕ) : ℕ → ℕ
  | Nat.zero   => 1
  | Nat.succ n => mul m (powerParam m n)

#eval powerParam 2 5

def iter (α : Type) (z : α) (f : α → α) : ℕ → α
  | Nat.zero   => z
  | Nat.succ n => f (iter α z f n)

#check iter

def powerIter (m n : ℕ) : ℕ :=
  iter ℕ 1 (mul m) n

#eval powerIter 2 5

def append (α : Type) : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (append α xs ys)

/- 由于 `append` 必须适用于任何类型的列表，因此其元素的类型是作为参数提供的。因此，在每次调用时都必须提供类型（如果 Lean 能够推断出类型，则可以使用 `_`）。 -/

#check append
#eval append ℕ [3, 1] [4, 1, 5]
#eval append _ [3, 1] [4, 1, 5]

/- 如果类型参数被包含在 `{ }` 中而不是 `( )` 中，则该参数是隐式的，无需在每次调用时显式提供（前提是 Lean 能够推断出该参数）。 -/

def appendImplicit {α : Type} : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (appendImplicit xs ys)

#eval appendImplicit [3, 1] [4, 1, 5]

/- 在定义名称前加上 `@` 符号，可以得到一个对应的定义，其中所有隐式参数都已显式化。这在 Lean 无法确定如何实例化隐式参数的情况下非常有用。 -/

#check @appendImplicit
#eval @appendImplicit ℕ [3, 1] [4, 1, 5]
#eval @appendImplicit _ [3, 1] [4, 1, 5]

/- 别名：

    `[]`          := `List.nil`
    `x :: xs`     := `List.cons x xs`
    `[x₁, …, xN]` := `x₁ :: … :: xN :: []`

翻译为中文：

别名：

    `[]`          := `List.nil`
    `x :: xs`     := `List.cons x xs`
    `[x₁, …, xN]` := `x₁ :: … :: xN :: []`

解释：
- `[]` 表示空列表，等同于 `List.nil`。
- `x :: xs` 表示将元素 `x` 添加到列表 `xs` 的开头，等同于 `List.cons x xs`。
- `[x₁, …, xN]` 表示一个包含元素 `x₁` 到 `xN` 的列表，等同于 `x₁ :: … :: xN :: []`。 -/

def appendPretty {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: appendPretty xs ys

def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]

def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i     => i
  | AExp.var x     => env x
  | AExp.add e₁ e₂ => eval env e₁ + eval env e₂
  | AExp.sub e₁ e₂ => eval env e₁ - eval env e₂
  | AExp.mul e₁ e₂ => eval env e₁ * eval env e₂
  | AExp.div e₁ e₂ => eval env e₁ / eval env e₂

#eval eval (fun x ↦ 7) (AExp.div (AExp.var "y") (AExp.num 0))

/- Lean 仅接受那些能够证明其终止性的函数定义。特别是，它接受**结构递归**函数，这些函数每次仅剥离一个构造函数。

## 定理声明

请注意与 `def` 命令的相似性。`theorem` 类似于 `def`，不同之处在于其结果是一个命题，而不是数据或函数。 -/

namespace SorryTheorems

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  sorry

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  sorry

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
  sorry

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  sorry

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  sorry

theorem reverse_reverse {α : Type} (xs : List α) :
    reverse (reverse xs) = xs :=
  sorry

/- 公理（Axioms）类似于定理（theorems），但没有证明。不透明声明（Opaque declarations）类似于定义（definitions），但没有具体实现体。 -/

opaque a : ℤ
opaque b : ℤ

axiom a_less_b :
    a < b

end SorryTheorems

end LoVe
