/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe 前言

## 证明助手

证明助手（也称为交互式定理证明器）

* 检查并帮助开发形式化证明；
* 可用于证明大型定理，而不仅仅是逻辑谜题；
* 使用起来可能有些繁琐；
* 具有高度成瘾性（类似于电子游戏）。

以下是一些按逻辑基础分类的证明助手：

* 集合论：Isabelle/ZF、Metamath、Mizar；
* 简单类型理论：HOL4、HOL Light、Isabelle/HOL；
* **依赖类型理论**：Agda、Coq、**Lean**、Matita、PVS。

## 成功案例

数学领域：

* 四色定理（在 Coq 中证明）；
* 开普勒猜想（在 HOL Light 和 Isabelle/HOL 中证明）；
* 完美空间的定义（在 Lean 中定义）。

计算机科学领域：

* 硬件；
* 操作系统；
* 编程语言理论；
* 编译器；
* 安全性。

## Lean

Lean 是一个由 Leonardo de Moura（亚马逊网络服务）自 2012 年起主要开发的证明助手。

其数学库 `mathlib` 由一个庞大的贡献者社区开发。

我们使用 Lean 4 的社区版本。我们使用其基础库、`mathlib4` 和 `LoVelib` 等。Lean 是一个研究项目。

优势：

* 基于一种称为**归纳构造演算**的依赖类型理论，具有高度表达力的逻辑；
* 扩展了经典公理和商类型；
* 元编程框架；
* 现代用户界面；
* 文档；
* 开源；
* 无穷无尽的双关语来源（Lean Forward、Lean Together、Boolean，……）。

## 我们的目标

我们希望您能够：

* 掌握交互式定理证明中的基础理论和技术；
* 熟悉一些应用领域；
* 培养一些可以在大型项目中应用的实用技能（作为爱好、硕士或博士研究，或在工业界）；
* 准备好迁移到另一个证明助手并应用所学知识；
* 充分理解该领域，能够开始阅读科学论文。

本课程既不是纯粹的逻辑基础课程，也不是 Lean 教程。Lean 是我们的工具，而不是目的本身。

# LoVe 演示 1：类型与项

我们通过研究 Lean 的基础知识开始我们的旅程，首先从项（表达式）及其类型开始。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Lean 概述

初步来看：

    Lean = 函数式编程 + 逻辑

在今天的讲座中，我们将介绍类型和项的语法，这些语法与简单类型 λ-演算或类型化函数式编程语言（如 ML、OCaml、Haskell）中的语法相似。

## 类型

类型 `σ`、`τ`、`υ`：

* 类型变量 `α`；
* 基本类型 `T`；
* 复杂类型 `T σ1 … σN`。

某些类型构造器 `T` 是中缀形式的，例如 `→`（函数类型）。

函数箭头是右结合的：
`σ₁ → σ₂ → σ₃ → τ` = `σ₁ → (σ₂ → (σ₃ → τ))`。

多态类型也是可能的。在 Lean 中，类型变量必须使用 `∀` 绑定，例如 `∀α, α → α`。

## 项

项 `t`、`u`：

* 常量 `c`；
* 变量 `x`；
* 应用 `t u`；
* 匿名函数 `fun x ↦ t`（也称为 λ-表达式）。

__柯里化__：函数可以是

* 完全应用的（例如，如果 `f` 最多可以接受 3 个参数，则 `f x y z`）；
* 部分应用的（例如，`f x y`，`f x`）；
* 未应用的（例如，`f`）。

应用是左结合的：`f x y z` = `((f x) y) z`。

`#check` 报告其参数的类型。 -/

#check ℕ
#check ℤ

#check Empty
#check Unit
#check Bool

#check ℕ → ℤ
#check ℤ → ℕ
#check Bool → ℕ → ℤ
#check (Bool → ℕ) → ℤ
#check ℕ → (Bool → ℕ) → ℤ

#check fun x : ℕ ↦ x
#check fun f : ℕ → ℕ ↦ fun g : ℕ → ℕ ↦ fun h : ℕ → ℕ ↦
  fun x : ℕ ↦ h (g (f x))
#check fun (f g h : ℕ → ℕ) (x : ℕ) ↦ h (g (f x))

/- `opaque` 用于定义一个指定类型的任意常量。 -/

opaque a : ℤ
opaque b : ℤ
opaque f : ℤ → ℤ
opaque g : ℤ → ℤ → ℤ

#check fun x : ℤ ↦ g (f (g a x)) (g x b)
#check fun x ↦ g (f (g a x)) (g x b)

#check fun x ↦ x


/- ## 类型检查与类型推断

类型检查和类型推断是可判定的问题（尽管如果添加了诸如重载或子类型等特性，这一性质会迅速丧失）。

类型判断：`C ⊢ t : σ`，表示在局部上下文 `C` 中，`t` 具有类型 `σ`。

类型规则：

    —————————— Cst   如果 c 在全局中声明为类型 σ
    C ⊢ c : σ

    —————————— Var   如果 x : σ 是 C 中 x 的最右侧出现
    C ⊢ x : σ

    C ⊢ t : σ → τ    C ⊢ u : σ
    ——————————————————————————— App
    C ⊢ t u : τ

    C, x : σ ⊢ t : τ
    ——————————————————————————— Fun
    C ⊢ (fun x : σ ↦ t) : σ → τ

如果同一个变量 `x` 在上下文 C 中多次出现，最右侧的出现会遮蔽其他出现。

## 类型可居性

给定一个类型 `σ`，**类型可居性**问题在于找到一个具有该类型的项。类型可居性是不可判定的。

递归过程：

1. 如果 `σ` 的形式为 `τ → υ`，一个候选的可居项是一个匿名函数，形式为 `fun x ↦ _`。

2. 或者，你可以使用任何常量或变量 `x : τ₁ → ⋯ → τN → σ` 来构建项 `x _ … _`。 -/

opaque α : Type
opaque β : Type
opaque γ : Type

def someFunOfType : (α → β → γ) → ((β → α) → β) → α → γ :=
  fun f g a ↦ f a (g (fun b ↦ a))

end LoVe
