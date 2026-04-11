/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe11_DenotationalSemantics_Demo


/- # LoVe 练习 11：指称语义

将占位符（例如，`:= sorry`）替换为您的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：单调性

1.1. 证明以下课堂中提到的定理。 -/

theorem Monotone_restrict {α β : Type} [PartialOrder α] (f : α → Set (β × β))
      (p : β → Prop) (hf : Monotone f) :
    Monotone (fun a ↦ f a ⇃ p) :=
  sorry

/- 1.2. 证明其同类项。 -/

theorem Monotone_comp {α β : Type} [PartialOrder α] (f g : α → Set (β × β))
      (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun a ↦ f a ◯ g a) :=
  sorry


/- ## 问题2：正则表达式

__正则表达式__（Regular expressions），简称__regexes__，是软件开发中用于分析文本输入的非常流行的工具。正则表达式由以下语法生成：

    R  ::=  ∅
         |  ε
         |  a
         |  R ⬝ R
         |  R + R
         |  R*

非正式地，正则表达式的语义如下：

* `∅` 不接受任何输入；
* `ε` 接受空字符串；
* `a` 接受原子 `a`；
* `R ⬝ R` 接受两个正则表达式的连接；
* `R + R` 接受两个正则表达式中的任意一个；
* `R*` 接受正则表达式的任意多次重复。

注意与WHILE语言的粗略对应关系：

    `∅` ~ 发散语句（例如，`while true do skip`）
    `ε` ~ `skip`
    `a` ~ `:=`
    `⬝` ~ `;`
    `+` ~ `if then else`
    `*` ~ `while` 循环 -/

inductive Regex (α : Type) : Type
  | nothing : Regex α
  | empty   : Regex α
  | atom    : α → Regex α
  | concat  : Regex α → Regex α → Regex α
  | alt     : Regex α → Regex α → Regex α
  | star    : Regex α → Regex α

/- 在本练习中，我们将探讨正则表达式的另一种语义。具体而言，我们可以将原子（atoms）视为二元关系，而不是字母或符号。连接（concatenation）对应于关系的复合（composition），而选择（alternation）则对应于并集（union）。从数学角度来看，正则表达式和二元关系都是克莱尼代数（Kleene algebras）的实例。

### 2.1 完成以下正则表达式到关系的翻译

提示：利用与WHILE语言的对应关系。 -/

def rel_of_Regex {α : Type} : Regex (Set (α × α)) → Set (α × α)
  | Regex.nothing      => ∅
  | Regex.empty        => Id
  -- 在此处输入缺失的案例
/- 2.2. 证明以下关于您定义的递归方程。 -/

theorem rel_of_Regex_Star {α : Type} (r : Regex (Set (α × α))) :
    rel_of_Regex (Regex.star r) =
    rel_of_Regex (Regex.alt (Regex.concat r (Regex.star r)) Regex.empty) :=
  sorry

end LoVe
