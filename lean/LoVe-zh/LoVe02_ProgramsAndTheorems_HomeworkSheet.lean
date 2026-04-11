/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe 作业 2（10 分）：程序与定理

将占位符（例如，`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1（4 分）：Snoc

1.1（3 分）。定义一个函数 `snoc`，该函数将一个元素附加到列表的末尾。你的函数应通过递归定义，并且不使用 `++`（即 `List.append`）。 -/

def snoc {α : Type} : List α → α → List α :=
  sorry

/- 1.2 （1 分）。通过在一些示例上测试 `snoc` 的定义，确保其功能正确。 -/

#eval snoc [1] 2
-- 在此处调用 `#eval` 或 `#reduce`

/- ## 问题 2（6 分）：求和

2.1（3 分）。定义一个 `sum` 函数，用于计算列表中所有数字的总和。 -/

def sum : List ℕ → ℕ :=
  sorry

#eval sum [1, 12, 3]   -- 预期值：16
/- 2.2 （3分）。将以下关于 `sum` 的性质陈述为定理（无需证明）。示意如下：

     sum (snoc ms n) = n + sum ms
     sum (ms ++ ns) = sum ms + sum ns
     sum (reverse ns) = sum ns

尝试为这些定理赋予有意义的名称。使用 `sorry` 作为证明。

翻译如下：

2.2 （3分）。将以下关于 `sum` 的性质陈述为定理（无需证明）。示意如下：

     sum (snoc ms n) = n + sum ms
     sum (ms ++ ns) = sum ms + sum ns
     sum (reverse ns) = sum ns

尝试为这些定理赋予有意义的名称。使用 `sorry` 作为证明。

### 定理命名建议：
1. **`sum_snoc`**: `sum (snoc ms n) = n + sum ms`
2. **`sum_concat`**: `sum (ms ++ ns) = sum ms + sum ns`
3. **`sum_reverse`**: `sum (reverse ns) = sum ns`

### 示例：
```lean
theorem sum_snoc : sum (snoc ms n) = n + sum ms := sorry
theorem sum_concat : sum (ms ++ ns) = sum ms + sum ns := sorry
theorem sum_reverse : sum (reverse ns) = sum ns := sorry
``` -/

-- 在此输入您的定理陈述
end LoVe
