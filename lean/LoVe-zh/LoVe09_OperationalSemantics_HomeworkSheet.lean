/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe 作业 9（10 分 + 1 分附加分）：操作语义

请将以下占位符（例如，`:= sorry`）替换为您的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1（5 分）：算术表达式

回顾第一讲中的算术表达式类型及其求值函数： -/

#check AExp
#check eval

/- 让我们为将变量名映射到值的环境引入以下缩写： -/

def Envir : Type :=
  String → ℤ

/- 1.1 （2 分）。请完成以下关于算术表达式的大步语义（big-step-style semantics）的 Lean 定义。谓词 `BigStep`（`⟹`）将一个算术表达式、一个环境以及该表达式在给定环境中求值的结果值关联起来： -/

inductive BigStep : AExp × Envir → ℤ → Prop
  | num (i env) : BigStep (AExp.num i, env) i

infix:60 " ⟹ " => BigStep

/- 1.2 （1 分）。证明以下定理以验证您上面的定义。

提示：首先证明 `(AExp.add (AExp.num 2) (AExp.num 2), env) ⟹ 2 + 2` 可能会有所帮助。 -/

theorem BigStep_add_two_two (env : Envir) :
    (AExp.add (AExp.num 2) (AExp.num 2), env) ⟹ 4 :=
  sorry

/- 1.3 （2 分）。证明大步语义（big-step semantics）相对于 `eval` 函数是可靠的（sound）： -/

theorem BigStep_sound (aenv : AExp × Envir) (i : ℤ) (hstep : aenv ⟹ i) :
    eval (Prod.snd aenv) (Prod.fst aenv) = i :=
  sorry


/- ## 问题 2（5 分 + 1 附加分）：正则表达式的语义

正则表达式是软件开发中非常流行的工具。通常，当需要分析文本输入时，会将其与正则表达式进行匹配。在这个问题中，我们定义了正则表达式的语法，并解释了正则表达式匹配字符串的含义。

我们定义 `Regex` 来表示以下语法：

    R  ::=  ∅       -- `nothing`：不匹配任何内容
         |  ε       -- `empty`：匹配空字符串
         |  a       -- `atom`：匹配原子 `a`
         |  R ⬝ R    -- `concat`：匹配两个正则表达式的连接
         |  R + R   -- `alt`：匹配两个正则表达式中的任意一个
         |  R*      -- `star`：匹配正则表达式的任意多次重复

注意与 WHILE 语言的粗略对应关系：

    `empty`  ~ `skip`
    `atom`   ~ 赋值
    `concat` ~ 顺序组合
    `alt`    ~ 条件语句
    `star`   ~ while 循环 -/ex α → Regex α → Regex α
  | alt     : Regex α → Regex α → Regex α
  | star    : Regex α → Regex α

/- `Matches r s` 谓词表示正则表达式 `r` 匹配字符串 `s`（其中字符串是由原子组成的序列）。 -/

inductive Matches {α : Type} : Regex α → List α → Prop
| empty :
  Matches Regex.empty []
| atom (a : α) :
  Matches (Regex.atom a) [a]
| concat (r₁ r₂ : Regex α) (s₁ s₂ : List α) (h₁ : Matches r₁ s₁)
    (h₂ : Matches r₂ s₂) :
  Matches (Regex.concat r₁ r₂) (s₁ ++ s₂)
| alt_left (r₁ r₂ : Regex α) (s : List α) (h : Matches r₁ s) :
  Matches (Regex.alt r₁ r₂) s
| alt_right (r₁ r₂ : Regex α) (s : List α) (h : Matches r₂ s) :
  Matches (Regex.alt r₁ r₂) s
| star_base (r : Regex α) :
  Matches (Regex.star r) []
| star_step (r : Regex α) (s s' : List α) (h₁ : Matches r s)
    (h₂ : Matches (Regex.star r) s') :
  Matches (Regex.star r) (s ++ s')

/- 引入规则对应于以下情况：

* 匹配空字符串
* 匹配一个原子（例如，字符）
* 匹配两个连接的正则表达式
* 匹配左侧选项
* 匹配右侧选项
* 匹配空字符串（`R*` 的基本情况）
* 匹配 `R` 后再次匹配 `R*`（`R*` 的归纳步骤）

2.1（1 分）。解释为什么没有针对 `nothing` 的规则。 -/

-- 请将以下技术文档翻译成中文，保持专业术语准确：

**原文：**
The API provides a set of endpoints that allow developers to interact with the system programmatically. These endpoints support CRUD (Create, Read, Update, Delete) operations on various resources, such as users, products, and orders. Authentication is required for most endpoints, and it is handled via OAuth 2.0. The API also supports pagination, filtering, and sorting to efficiently manage large datasets. Error responses are standardized and include detailed error codes and messages to assist in debugging.

**翻译：**
该API提供了一组端点，允许开发者以编程方式与系统进行交互。这些端点支持对多种资源（如用户、产品和订单）执行CRUD（创建、读取、更新、删除）操作。大多数端点需要身份验证，并通过OAuth 2.0进行处理。API还支持分页、过滤和排序功能，以高效管理大型数据集。错误响应已标准化，并包含详细的错误代码和消息，以帮助调试。
/- 2.2 （4分）。证明以下反演规则。 -/

@[simp] theorem Matches_atom {α : Type} {s : List α} {a : α} :
    Matches (Regex.atom a) s ↔ s = [a] :=
  sorry

@[simp] theorem Matches_nothing {α : Type} {s : List α} :
    ¬ Matches Regex.nothing s :=
  sorry

@[simp] theorem Matches_empty {α : Type} {s : List α} :
    Matches Regex.empty s ↔ s = [] :=
  sorry

@[simp] theorem Matches_concat {α : Type} {s : List α} {r₁ r₂ : Regex α} :
    Matches (Regex.concat r₁ r₂) s
    ↔ (∃s₁ s₂, Matches r₁ s₁ ∧ Matches r₂ s₂ ∧ s = s₁ ++ s₂) :=
  sorry

@[simp] theorem Matches_alt {α : Type} {s : List α} {r₁ r₂ : Regex α} :
    Matches (Regex.alt r₁ r₂) s ↔ (Matches r₁ s ∨ Matches r₂ s) :=
  sorry

/- 2.3 （1个附加分）。证明以下反演规则。 -/

theorem Matches_star {α : Type} {s : List α} {r : Regex α} :
    Matches (Regex.star r) s ↔
    s = []
    ∨ (∃s₁ s₂, Matches r s₁ ∧ Matches (Regex.star r) s₂ ∧ s = s₁ ++ s₂) :=
  sorry

end LoVe
