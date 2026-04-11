/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe 演示 13：基本数学结构

我们介绍了关于基本数学结构（如群、域和线性序）的定义和证明。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 单一二元运算符上的类型类

从数学上讲，**群**（group）是一个集合 `G` 和一个二元运算符 `⬝ : G × G → G`，并满足以下性质，称为**群公理**：

* **结合律**：对于所有 `a, b, c ∈ G`，有 `(a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)`；
* **单位元**：存在一个元素 `e ∈ G`，使得对于所有 `a ∈ G`，有 `e ⬝ a = a` 和 `a ⬝ e = a`；
* **逆元**：对于每个 `a ∈ G`，存在一个逆元 `b ∈ G`，使得 `b ⬝ a = e` 和 `a ⬝ b = e`。

群的例子包括：
* `ℤ` 与 `+`；
* `ℝ` 与 `+`；
* `ℝ \ {0}` 与 `*`。

在 Lean 中，群的类型类可以定义如下： -/

namespace MonolithicGroup

class Group (α : Type) where
  mul          : α → α → α
  one          : α
  inv          : α → α
  mul_assoc    : ∀a b c, mul (mul a b) c = mul a (mul b c)
  one_mul      : ∀a, mul one a = a
  mul_left_inv : ∀a, mul (inv a) a = one

end MonolithicGroup

/- 在 Lean 中，`group`（群）是代数结构层次体系中的一部分：

| 类型类                  | 性质                                      | 示例
|------------------------|-------------------------------------------|-------------------
| `Semigroup`（半群）     | `*` 的结合律                              | `ℝ`, `ℚ`, `ℤ`, `ℕ`
| `Monoid`（幺半群）      | 带有单位元 `1` 的 `Semigroup`             | `ℝ`, `ℚ`, `ℤ`, `ℕ`
| `LeftCancelSemigroup`（左消半群） | 满足 `c * a = c * b → a = b` 的 `Semigroup` |
| `RightCancelSemigroup`（右消半群） | 满足 `a * c = b * c → a = b` 的 `Semigroup` |
| `Group`（群）           | 带有逆元 `⁻¹` 的 `Monoid`                 |

这些结构中的大多数都有对应的交换版本：`CommSemigroup`（交换半群）、`CommMonoid`（交换幺半群）、`CommGroup`（交换群）。

**乘法**结构（基于 `*`、`1`、`⁻¹`）被复制以生成**加法**版本（基于 `+`、`0`、`-`）：

| 类型类                     | 性质                                       | 示例
|---------------------------|--------------------------------------------|-------------------
| `AddSemigroup`（加法半群） | `+` 的结合律                               | `ℝ`, `ℚ`, `ℤ`, `ℕ`
| `AddMonoid`（加法幺半群）  | 带有单位元 `0` 的 `AddSemigroup`           | `ℝ`, `ℚ`, `ℤ`, `ℕ`
| `AddLeftCancelSemigroup`（左消加法半群） | 满足 `c + a = c + b → a = b` 的 `AddSemigroup` | `ℝ`, `ℚ`, `ℤ`, `ℕ`
| `AddRightCancelSemigroup`（右消加法半群） | 满足 `a + c = b + c → a = b` 的 `AddSemigroup` | `ℝ`, `ℚ`, `ℤ`, `ℕ`
| `AddGroup`（加法群）       | 带有逆元 `-` 的 `AddMonoid`                | `ℝ`, `ℚ`, `ℤ` -/ Type
  | zero
  | one

def Int2.add : Int2 → Int2 → Int2
  | Int2.zero, a         => a
  | Int2.one,  Int2.zero => Int2.one
  | Int2.one,  Int2.one  => Int2.zero

instance Int2.AddGroup : AddGroup Int2 :=
  { add            := Int2.add
    zero           := Int2.zero
    neg            := fun a ↦ a
    add_assoc      :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          cases c <;>
          rfl
    zero_add       :=
      by
        intro a
        cases a <;>
          rfl
    add_zero       :=
      by
        intro a
        cases a <;>
          rfl
    neg_add_cancel :=
      by
        intro a
        cases a <;>
          rfl
    nsmul         :=
      @nsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)
    zsmul         :=
      @zsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)
        (Neg.mk (fun a ↦ a))
        (@nsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)) }

/- `nsmul` 和 `znmul` 是冗余的。它们的存在是由于技术原因所必需的。 -/

#reduce Int2.one + 0 - 0 - Int2.one

/- 另一个示例：列表是一个`AddMonoid`（加法幺半群）： -/

instance List.AddMonoid {α : Type} : AddMonoid (List α) :=
  { zero      := []
    add       := fun xs ys ↦ xs ++ ys
    add_assoc := List.append_assoc
    zero_add  := List.nil_append
    add_zero  := List.append_nil
    nsmul     :=
      @nsmulRec (List α) (Zero.mk [])
        (Add.mk (fun xs ys ↦ xs ++ ys))}


/- ## 具有两个二元运算符的类型类

从数学上讲，**域**（Field）是一个集合 `F`，满足以下条件：

* `F` 在运算符 `+`（称为加法）下形成一个交换群，其单位元为 `0`。
* `F \ {0}` 在运算符 `*`（称为乘法）下形成一个交换群。
* 乘法对加法满足分配律，即对于所有 `a, b, c ∈ F`，有 `a * (b + c) = a * b + a * c`。

在 Lean 中，域也是更大类型类层次结构的一部分：

类型类          |  属性                                                | 示例
----------------|-----------------------------------------------------|-------------------
`Semiring`      | `Monoid` 和 `AddCommMonoid`，且满足分配律            | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`CommSemiring`  | `Semiring`，且乘法 `*` 满足交换律                    | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`Ring`          | `Monoid` 和 `AddCommGroup`，且满足分配律             | `ℝ`, `ℚ`, `ℤ`
`CommRing`      | `Ring`，且乘法 `*` 满足交换律                        | `ℝ`, `ℚ`, `ℤ`
`DivisionRing`  | `Ring`，且具有乘法逆元 `⁻¹`                          | `ℝ`, `ℚ`
`Field`         | `DivisionRing`，且乘法 `*` 满足交换律                | `ℝ`, `ℚ` -/2.mul : Int2 → Int2 → Int2
  | Int2.one,  a => a
  | Int2.zero, _ => Int2.zero

theorem Int2.mul_assoc (a b c : Int2) :
     Int2.mul (Int2.mul a b) c = Int2.mul a (Int2.mul b c) :=
  by
    cases a <;>
      cases b <;>
      cases c <;>
      rfl

instance Int2.Field : Field Int2 :=
  { Int2.AddGroup with
    one            := Int2.one
    mul            := Int2.mul
    inv            := fun a ↦ a
    add_comm       :=
      by
        intro a b
        cases a <;>
          cases b <;>
          rfl
    exists_pair_ne :=
      by
        apply Exists.intro Int2.zero
        apply Exists.intro Int2.one
        simp
    zero_mul       :=
      by
        intro a
        rfl
    mul_zero       :=
      by
        intro a
        cases a <;>
          rfl
    one_mul        :=
      by
        intro a
        rfl
    mul_one        :=
      by
        intro a
        cases a <;>
          rfl
    mul_inv_cancel :=
      by
        intro a h
        cases a
        { apply False.elim
          apply h
          rfl }
        { rfl }
    inv_zero       := by rfl
    mul_assoc      := Int2.mul_assoc
    mul_comm       :=
      by
        intro a b
        cases a <;>
          cases b <;>
          rfl
    left_distrib   :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          rfl
    right_distrib  :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          cases c <;>
          rfl
    nnqsmul        := _
    nnqsmul_def    :=
      by
        intro a b
        rfl
    qsmul          := _
    qsmul_def :=
      by
        intro a b
        rfl
    nnratCast_def  :=
      by
        intro q
        rfl }

#reduce (1 : Int2) * 0 / (0 - 1)

#reduce (3 : Int2)

theorem ring_example (a b : Int2) :
    (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3
    :=
  by ring

/- `ring` 通过规范化表达式来证明交换环和半环上的等式。

## 强制类型转换

当组合来自 `ℕ`、`ℤ`、`ℚ` 和 `ℝ` 的数字时，我们可能希望将一种类型转换为另一种类型。Lean 提供了一种机制来自动引入强制类型转换，由 `Coe.coe`（语法糖：`↑`）表示。`Coe.coe` 可以设置为在任意类型之间提供隐式强制类型转换。

许多强制类型转换已经就位，包括以下内容：

* `Coe.coe : ℕ → α` 将 `ℕ` 转换为另一个半环 `α`；
* `Coe.coe : ℤ → α` 将 `ℤ` 转换为另一个环 `α`；
* `Coe.coe : ℚ → α` 将 `ℚ` 转换为另一个除环 `α`。

例如，即使自然数上没有定义取反操作 `- n`，以下代码仍然可以工作： -/

theorem neg_mul_neg_Nat (n : ℕ) (z : ℤ) :
    (- z) * (- n) = z * n :=
  by simp

/- 请注意 Lean 如何引入了 `↑` 强制转换： -/

#check neg_mul_neg_Nat

/- 类型注解可以记录我们的意图： -/

theorem neg_Nat_mul_neg (n : ℕ) (z : ℤ) :
    (- n : ℤ) * (- z) = n * z :=
  by simp

#print neg_Nat_mul_neg

/- 在涉及强制类型转换的证明中，`norm_cast` 策略可能会非常方便。 -/

theorem Eq_coe_int_imp_Eq_Nat (m n : ℕ)
      (h : (m : ℤ) = (n : ℤ)) :
    m = n :=
  by norm_cast at h

theorem Nat_coe_Int_add_eq_add_Nat_coe_Int (m n : ℕ) :
    (m : ℤ) + (n : ℤ) = ((m + n : ℕ) : ℤ) :=
  by norm_cast

/- `norm_cast` 将强制类型转换推向表达式的内部，作为一种简化的形式。与 `simp` 类似，它通常会产生一个子目标。

`norm_cast` 依赖于以下定理： -/

#check Nat.cast_add
#check Int.cast_add
#check Rat.cast_add


/- ### 列表、多重集与有限集

对于元素的有限集合，有以下几种不同的数据结构可供使用：

* **列表（Lists）**：顺序和重复元素均重要；
* **多重集（Multisets）**：仅重复元素重要；
* **有限集（Finsets）**：顺序和重复元素均不重要。 -/

theorem List_duplicates_example :
    [2, 3, 3, 4] ≠ [2, 3, 4] :=
  by decide

theorem List_order_example :
    [4, 3, 2] ≠ [2, 3, 4] :=
  by decide

theorem Multiset_duplicates_example :
    ({2, 3, 3, 4} : Multiset ℕ) ≠ {2, 3, 4} :=
  by decide

theorem Multiset_order_example :
    ({2, 3, 4} : Multiset ℕ) = {4, 3, 2} :=
  by decide

theorem Finset_duplicates_example :
    ({2, 3, 3, 4} : Finset ℕ) = {2, 3, 4} :=
  by decide

theorem Finset_order_example :
    ({2, 3, 4} : Finset ℕ) = {4, 3, 2} :=
  by decide

/- `decide` 是一种可用于处理真值可判定目标（例如，一个可执行的表达式为真）的策略。 -/

def List.elems : Tree ℕ → List ℕ
  | Tree.nil        => []
  | Tree.node a l r => a :: List.elems l ++ List.elems r

def Multiset.elems : Tree ℕ → Multiset ℕ
  | Tree.nil        => ∅
  | Tree.node a l r =>
    {a} ∪ Multiset.elems l ∪ Multiset.elems r

def Finset.elems : Tree ℕ → Finset ℕ
  | Tree.nil        => ∅
  | Tree.node a l r => {a} ∪ Finset.elems l ∪ Finset.elems r

#eval List.sum [2, 3, 4]
#eval Multiset.sum ({2, 3, 4} : Multiset ℕ)

#eval List.prod [2, 3, 4]
#eval Multiset.prod ({2, 3, 4} : Multiset ℕ)


/- ## 订单类型类

上述介绍的许多结构都可以进行排序。例如，自然数上的众所周知的有序关系可以定义如下： -/

inductive Nat.le : ℕ → ℕ → Prop
  | refl : ∀a : ℕ, Nat.le a a
  | step : ∀a b : ℕ, Nat.le a b → Nat.le a (b + 1)

#print Preorder

/- 这是一个线性序的例子。**线性序**（或**全序**）是一种二元关系 `≤`，对于所有的 `a`、`b`、`c`，以下性质成立：

* **自反性**：`a ≤ a`；
* **传递性**：如果 `a ≤ b` 且 `b ≤ c`，则 `a ≤ c`；
* **反对称性**：如果 `a ≤ b` 且 `b ≤ a`，则 `a = b`；
* **全序性**：`a ≤ b` 或 `b ≤ a`。

如果一个关系满足前三个性质，则它是一个**偏序**。例如，集合、有限集或多重集上的 `⊆` 关系。如果一个关系只满足前两个性质，则它是一个**预序**。例如，通过列表的长度来比较列表。

在 Lean 中，这些不同类型的序有对应的类型类：`LinearOrder`、`PartialOrder` 和 `Preorder`。 -/

#print Preorder
#print PartialOrder
#print LinearOrder

/- 我们可以声明一个列表上的预序（preorder），该预序通过列表的长度来比较列表，具体如下： -/

instance List.length.Preorder {α : Type} : Preorder (List α) :=
  { le :=
      fun xs ys ↦ List.length xs ≤ List.length ys
    lt :=
      fun xs ys ↦ List.length xs < List.length ys
    le_refl :=
      by
        intro xs
        apply Nat.le_refl
    le_trans :=
      by
        intro xs ys zs
        exact Nat.le_trans
    lt_iff_le_not_le :=
      by
        intro a b
        exact Nat.lt_iff_le_not_le }

/- 本实例介绍了中缀语法 `≤` 以及关系运算符 `≥`、`<` 和 `>`： -/

theorem list.length.Preorder_example :
    [1] > [] :=
  by decide

/- 完全格（第11讲）被形式化为另一种类型类 `CompleteLattice`，它继承自 `PartialOrder`。

结合了序和代数结构的类型类也是可用的：

    `OrderedCancelCommMonoid`（有序可消交换幺半群）
    `OrderedCommGroup`（有序交换群）
    `OrderedSemiring`（有序半环）
    `LinearOrderedSemiring`（线性有序半环）
    `LinearOrderedCommRing`（线性有序交换环）
    `LinearOrderedField`（线性有序域）

所有这些数学结构通过单调性规则（例如，`a ≤ b → c ≤ d → a + c ≤ b + d`）和消去规则（例如，`c + a ≤ c + b → a ≤ b`）将 `≤` 和 `<` 与 `0`、`1`、`+` 和 `*` 联系起来。 -/

end LoVe
