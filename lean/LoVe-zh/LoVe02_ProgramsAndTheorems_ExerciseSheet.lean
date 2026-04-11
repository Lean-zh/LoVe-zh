/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe 练习 2：程序与定理

将占位符（例如 `:= sorry`）替换为你的解答。 -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1：前驱函数

1.1. 定义一个类型为 `ℕ → ℕ` 的函数 `pred`，该函数返回其参数的前驱数，如果参数为 0，则返回 0。例如：

    `pred 7 = 6`
    `pred 0 = 0` -/

def pred : ℕ → ℕ :=
  sorry

/- 1.2. 检查您的函数是否按预期工作。 -/

#eval pred 0    -- 预期值：0#eval pred 1    -- 预期值：0#eval pred 2    -- 预期值：1#eval pred 3    -- 预期值：2#eval pred 10   -- 预期值：9#eval pred 99   -- 预期值：98

/- ## 问题2：算术表达式

考虑讲座中的类型 `AExp` 以及计算表达式值的函数 `eval`。你可以在文件 `LoVe02_ProgramsAndTheorems_Demo.lean` 中找到这些定义。快速找到它们的一种方法是：

1. 按住 Control 键（在 Linux 和 Windows 上）或 Command 键（在 macOS 上）；
2. 将光标移动到标识符 `AExp` 或 `eval` 上；
3. 点击该标识符。 -/

#check AExp
#check eval

/- 2.1. 测试 `eval` 的行为是否符合预期。确保至少对每个构造函数进行一次测试。你可以在测试中使用以下环境。如果除以零会发生什么？

请注意，`#eval`（Lean 的求值命令）和 `eval`（我们在 `AExp` 上的求值函数）是无关的。 -/

def someEnv : String → ℤ
  | "x" => 3
  | "y" => 17
  | _   => 201

#eval eval someEnv (AExp.var "x")   -- 预期值：3-- 在此处调用 `#eval`
/- 2.2. 以下函数简化了涉及加法的算术表达式。它将 `0 + e` 和 `e + 0` 简化为 `e`。请完善该函数的定义，使其也能够简化涉及其他三种二元运算符的表达式。 -/

def simplify : AExp → AExp
  | AExp.add (AExp.num 0) e₂ => simplify e₂
  | AExp.add e₁ (AExp.num 0) => simplify e₁
  -- 在此处插入缺失的案例  -- 以下是“catch-all cases”的中文翻译：

**兜底情况** 或 **通配情况**

在技术文档中，“catch-all cases”通常指一种默认或通用的处理方式，用于涵盖所有未明确指定的情况。这种设计模式常用于编程中的条件判断或异常处理，确保程序在遇到未预见的输入或状态时仍能正常运行。

例如：
- 在编程中，`switch`语句的`default`分支可以视为一种“catch-all case”。
- 在正则表达式中，`.*`可以匹配任意字符，也是一种“catch-all”的用法。

根据具体上下文，也可以翻译为 **默认情况** 或 **通用情况**。  | AExp.num i               => AExp.num i
  | AExp.var x               => AExp.var x
  | AExp.add e₁ e₂           => AExp.add (simplify e₁) (simplify e₂)
  | AExp.sub e₁ e₂           => AExp.sub (simplify e₁) (simplify e₂)
  | AExp.mul e₁ e₂           => AExp.mul (simplify e₁) (simplify e₂)
  | AExp.div e₁ e₂           => AExp.div (simplify e₁) (simplify e₂)

/- 2.3. `simplify` 函数是否正确？事实上，如何定义它的正确与否？直观上，`simplify` 要被认为是正确的，它必须返回一个算术表达式，该表达式在求值时产生的数值与原始表达式相同。

给定一个环境 `env` 和一个表达式 `e`，请陈述（无需证明）简化后的 `e` 的值与简化前的 `e` 的值相同的性质。 -/

theorem simplify_correct (env : String → ℤ) (e : AExp) :
  True :=   -- 将 `True` 替换为您的定理陈述  sorry   -- 请将以下技术文档翻译成中文，保持专业术语准确：
保留 `sorry` 不变

/- ## 问题 3（**可选**）：Map

3.1（**可选**）。定义一个通用的 `map` 函数，该函数将某个函数应用于列表中的每个元素。 -/

def map {α : Type} {β : Type} (f : α → β) : List α → List β :=
  sorry

#eval map (fun n ↦ n + 10) [1, 2, 3]   -- 预期值：[11, 12, 13]
/- 3.2 (**可选**). 陈述（无需证明）所谓的 `map` 的函子性质作为定理。示意如下：

     map (fun x ↦ x) xs = xs
     map (fun x ↦ g (f x)) xs = map g (map f xs)

尝试为这些定理赋予有意义的名称。此外，确保尽可能一般化地陈述第二个性质，适用于任意类型。

**定理命名建议：**

1. **恒等映射定理 (Identity Map Theorem):**
   ```
   map (fun x ↦ x) xs = xs
   ```
   该定理表明，对列表应用恒等函数（即不改变元素的函数）的 `map` 操作，结果与原列表相同。

2. **复合映射定理 (Composition Map Theorem):**
   ```
   map (fun x ↦ g (f x)) xs = map g (map f xs)
   ```
   该定理表明，对列表先应用函数 `f` 再应用函数 `g` 的 `map` 操作，等价于先对列表应用 `f` 的 `map`，再对结果应用 `g` 的 `map`。此性质适用于任意类型的函数 `f` 和 `g`。

通过这些定理，可以更好地理解 `map` 操作在函数式编程中的行为及其与函数复合的关系。 -/

-- 在此输入您的定理陈述
end LoVe
