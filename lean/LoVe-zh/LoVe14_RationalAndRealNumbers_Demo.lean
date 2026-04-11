/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe 示例 14：有理数与实数

我们回顾了将 `ℚ` 和 `ℝ` 构造为商类型的过程。

我们构造具有特定属性的类型的步骤如下：

1. 创建一个新类型，该类型可以表示所有元素，但不一定以唯一的方式表示。

2. 对这个表示进行商化，将应该相等的元素等同起来。

3. 通过从基类型提升函数来定义商类型上的运算符，并证明它们与商关系兼容。

我们在第12讲中使用了这种方法来构造 `ℤ`。这种方法同样适用于 `ℚ` 和 `ℝ`。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 有理数

**步骤 1:** 有理数是指可以表示为整数 `n` 和 `d ≠ 0` 的分数 `n / d` 的数： -/

structure Fraction where
  num            : ℤ
  denom          : ℤ
  denom_Neq_zero : denom ≠ 0

/- 数字 `n` 被称为**分子**，数字 `d` 被称为**分母**。

有理数表示为分数的形式并不唯一——例如，`1 / 2 = 2 / 4 = -1 / -2`。

**步骤 2：** 如果两个分数 `n₁ / d₁` 和 `n₂ / d₂` 的分子与分母的比例相同，即 `n₁ * d₂ = n₂ * d₁`，那么它们表示的是同一个有理数。这将作为我们在分数上的等价关系 `≈`。 -/

namespace Fraction

instance Setoid : Setoid Fraction :=
  { r :=
      fun a b : Fraction ↦ num a * denom b = num b * denom a
    iseqv :=
      { refl  := by aesop
        symm  := by aesop
        trans :=
          by
            intro a b c heq_ab heq_bc
            apply Int.eq_of_mul_eq_mul_right (denom_Neq_zero b)
            calc
              num a * denom c * denom b
              = num a * denom b * denom c :=
                by ac_rfl
              _ = num b * denom a * denom c :=
                by rw [heq_ab]
              _ = num b * denom c * denom a :=
                by ac_rfl
              _ = num c * denom b * denom a :=
                by rw [heq_bc]
              _ = num c * denom a * denom b :=
                by ac_rfl
            } }

theorem Setoid_Iff (a b : Fraction) :
    a ≈ b ↔ num a * denom b = num b * denom a :=
  by rfl

/- **步骤 3:** 定义 `0 := 0 / 1`，`1 := 1 / 1`，加法、乘法等运算。

    `n₁ / d₁ + n₂ / d₂`     := `(n₁ * d₂ + n₂ * d₁) / (d₁ * d₂)`
    `(n₁ / d₁) * (n₂ / d₂)` := `(n₁ * n₂) / (d₁ * d₂)`

然后证明这些定义与等价关系 `≈` 是兼容的。 -/

def of_int (i : ℤ) : Fraction :=
  { num            := i
    denom          := 1
    denom_Neq_zero := by simp }

instance Zero : Zero Fraction :=
  { zero := of_int 0 }

instance One : One Fraction :=
  { one := of_int 1 }

instance Add : Add Fraction :=
  { add := fun a b : Fraction ↦
      { num            := num a * denom b + num b * denom a
        denom          := denom a * denom b
        denom_Neq_zero := by simp [denom_Neq_zero] } }

@[simp] theorem add_num (a b : Fraction) :
    num (a + b) = num a * denom b + num b * denom a :=
  by rfl

@[simp] theorem add_denom (a b : Fraction) :
    denom (a + b) = denom a * denom b :=
  by rfl

theorem Setoid_add {a a' b b' : Fraction} (ha : a ≈ a')
      (hb : b ≈ b') :
    a + b ≈ a' + b' :=
  by
    simp [Setoid_Iff, add_denom, add_num] at *
    calc
      (num a * denom b + num b * denom a)
          * (denom a' * denom b')
      = num a * denom a' * denom b * denom b'
        + num b * denom b' * denom a * denom a' :=
        by
          simp [add_mul, mul_add]
          ac_rfl
      _ = num a' * denom a * denom b * denom b'
            + num b' * denom b * denom a * denom a' :=
        by simp [*]
      _ = (num a' * denom b' + num b' * denom a')
            * (denom a * denom b) :=
        by
          simp [add_mul, mul_add]
          ac_rfl

instance Neg : Neg Fraction :=
  { neg := fun a : Fraction ↦
      { a with
        num := - num a } }

@[simp] theorem neg_num (a : Fraction) :
    num (- a) = - num a :=
  by rfl

@[simp] theorem neg_denom (a : Fraction) :
    denom (- a) = denom a :=
  by rfl

theorem Setoid_neg {a a' : Fraction} (hab : a ≈ a') :
    - a ≈ - a' :=
  by
    simp [Setoid_Iff] at *
    exact hab

instance Mul : Mul Fraction :=
  { mul := fun a b : Fraction ↦
      { num            := num a * num b
        denom          := denom a * denom b
        denom_Neq_zero :=
          by simp [Int.mul_eq_zero, denom_Neq_zero] } }

@[simp] theorem mul_num (a b : Fraction) :
    num (a * b) = num a * num b :=
  by rfl

@[simp] theorem mul_denom (a b : Fraction) :
    denom (a * b) = denom a * denom b :=
  by rfl

theorem Setoid_mul {a a' b b' : Fraction} (ha : a ≈ a')
      (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  by
    simp [Setoid_Iff] at *
    calc
      num a * num b * (denom a' * denom b')
      = (num a * denom a') * (num b * denom b') :=
        by ac_rfl
      _ = (num a' * denom a) * (num b' * denom b) :=
        by simp [*]
      _ = num a' * num b' * (denom a * denom b) :=
        by ac_rfl

instance Inv : Inv Fraction :=
  { inv := fun a : Fraction ↦
      if ha : num a = 0 then
        0
      else
        { num            := denom a
          denom          := num a
          denom_Neq_zero := ha } }

theorem inv_def (a : Fraction) (ha : num a ≠ 0) :
    a⁻¹ =
    { num            := denom a
      denom          := num a
      denom_Neq_zero := ha } :=
  dif_neg ha

theorem inv_zero (a : Fraction) (ha : num a = 0) :
    a⁻¹ = 0 :=
  dif_pos ha

@[simp] theorem inv_num (a : Fraction) (ha : num a ≠ 0) :
    num (a⁻¹) = denom a :=
  by rw [inv_def a ha]

@[simp] theorem inv_denom (a : Fraction) (ha : num a ≠ 0) :
    denom (a⁻¹) = num a :=
  by rw [inv_def a ha]

theorem Setoid_inv {a a' : Fraction} (ha : a ≈ a') :
    a⁻¹ ≈ a'⁻¹ :=
  by
    cases Classical.em (num a = 0) with
    | inl ha0 =>
      cases Classical.em (num a' = 0) with
      | inl ha'0 =>
        simp [ha0, ha'0, inv_zero]
      | inr ha'0 =>
        simp [ha0, ha'0, Setoid_Iff, denom_Neq_zero] at ha
    | inr ha0 =>
      cases Classical.em (num a' = 0) with
      | inl ha'0 =>
        simp [ha0, ha'0, Setoid_Iff, denom_Neq_zero] at ha
      | inr ha'0 =>
        simp [Setoid_Iff, ha0, ha'0] at *
        linarith

end Fraction

def Rat : Type :=
  Quotient Fraction.Setoid

namespace Rat

def mk : Fraction → Rat :=
  Quotient.mk Fraction.Setoid

instance Zero : Zero Rat :=
  { zero := mk 0 }

instance One : One Rat :=
  { one := mk 1 }

instance Add : Add Rat :=
  { add := Quotient.lift₂ (fun a b : Fraction ↦ mk (a + b))
      (by
         intro a b a' b' ha hb
         apply Quotient.sound
         exact Fraction.Setoid_add ha hb) }

instance Neg : Neg Rat :=
  { neg := Quotient.lift (fun a : Fraction ↦ mk (- a))
      (by
         intro a a' ha
         apply Quotient.sound
         exact Fraction.Setoid_neg ha) }

instance Mul : Mul Rat :=
  { mul := Quotient.lift₂ (fun a b : Fraction ↦ mk (a * b))
      (by
         intro a b a' b' ha hb
         apply Quotient.sound
         exact Fraction.Setoid_mul ha hb) }

instance Inv : Inv Rat :=
  { inv := Quotient.lift (fun a : Fraction ↦ mk (a⁻¹))
      (by
         intro a a' ha
         apply Quotient.sound
         exact Fraction.Setoid_inv ha) }

end Rat


/- ### `ℚ` 的替代定义

将 `ℚ` 定义为 `fraction` 的子类型，要求分母为正数，且分子和分母除了 `1` 和 `-1` 之外没有其他公约数： -/

namespace Alternative

def Rat.IsCanonical (a : Fraction) : Prop :=
  Fraction.denom a > 0
  ∧ Nat.Coprime (Int.natAbs (Fraction.num a))
      (Int.natAbs (Fraction.denom a))

def Rat : Type :=
  {a : Fraction // Rat.IsCanonical a}

end Alternative

/- 这大致是 `mathlib` 的定义。

优点：

* 不需要商集（quotient）；
* 计算效率更高；
* 更多性质在计算上是语法等价的。

缺点：

* 函数定义更为复杂。

### 实数

一些有理数序列看起来是收敛的，因为序列中的数越来越接近，但它们并不收敛到一个有理数。

示例：

    `a₀ = 1`
    `a₁ = 1.4`
    `a₂ = 1.41`
    `a₃ = 1.414`
    `a₄ = 1.4142`
    `a₅ = 1.41421`
    `a₆ = 1.414213`
    `a₇ = 1.4142135`
       ⋮

这个序列看起来是收敛的，因为每个 `aₙ` 与后续数的差距最多为 `10^-n`。但极限是 `√2`，它不是一个有理数。

有理数是不完备的，而实数是它们的**完备化**。

为了构造实数，我们需要填补这些看起来收敛但实际上不收敛的序列所揭示的“空隙”。

从数学上讲，一个有理数序列 `a₀, a₁, …` 是**柯西序列**（Cauchy），如果对于任意 `ε > 0`，存在一个 `N ∈ ℕ`，使得对于所有 `m ≥ N`，都有 `|a_N - a_m| < ε`。

换句话说，无论我们选择的 `ε` 有多小，我们总能找到序列中的一个点，使得从该点开始的所有后续数与它的偏差都小于 `ε`。 -/

def IsCauchySeq (f : ℕ → ℚ) : Prop :=
  ∀ε > 0, ∃N, ∀m ≥ N, abs (f N - f m) < ε

/- 并非每个序列都是柯西序列： -/

theorem id_Not_CauchySeq :
    ¬ IsCauchySeq (fun n : ℕ ↦ (n : ℚ)) :=
  by
    rw [IsCauchySeq]
    intro h
    cases h 1 zero_lt_one with
    | intro i hi =>
      have hi_succi :=
        hi (i + 1) (by simp)
      simp [←sub_sub] at hi_succi

/- 我们将一种柯西序列定义为子类型： -/

def CauchySeq : Type :=
  {f : ℕ → ℚ // IsCauchySeq f}

def seqOf (f : CauchySeq) : ℕ → ℚ :=
  Subtype.val f

/- 柯西序列表示实数：

* `a_n = 1 / n` 表示实数 `0`；
* `1, 1.4, 1.41, …` 表示实数 `√2`；
* `a_n = 0` 也表示实数 `0`。

由于不同的柯西序列可以表示相同的实数，我们需要进行等价类的划分。形式上，当两个序列的差收敛于零时，它们表示相同的实数： -/

namespace CauchySeq

instance Setoid : Setoid CauchySeq :=
{ r :=
    fun f g : CauchySeq ↦
      ∀ε > 0, ∃N, ∀m ≥ N, abs (seqOf f m - seqOf g m) < ε
  iseqv :=
    { refl :=
        by
          intro f ε hε
          apply Exists.intro 0
          aesop
      symm :=
        by
          intro f g hfg ε hε
          cases hfg ε hε with
          | intro N hN =>
            apply Exists.intro N
            intro m hm
            rw [abs_sub_comm]
            apply hN m hm
      trans :=
        by
          intro f g h hfg hgh ε hε
          cases hfg (ε / 2) (by linarith) with
          | intro N₁ hN₁ =>
            cases hgh (ε / 2) (by linarith) with
            | intro N₂ hN₂ =>
              apply Exists.intro (max N₁ N₂)
              intro m hm
              calc
                abs (seqOf f m - seqOf h m)
                ≤ abs (seqOf f m - seqOf g m)
                  + abs (seqOf g m - seqOf h m) :=
                  by apply abs_sub_le
              _ < ε / 2 + ε / 2 :=
                add_lt_add (hN₁ m (le_of_max_le_left hm))
                  (hN₂ m (le_of_max_le_right hm))
              _ = ε :=
                by simp } }

theorem Setoid_iff (f g : CauchySeq) :
    f ≈ g ↔
    ∀ε > 0, ∃N, ∀m ≥ N, abs (seqOf f m - seqOf g m) < ε :=
  by rfl

/- 我们可以将诸如 `0` 和 `1` 这样的常量定义为常量序列。任何常量序列都是柯西序列： -/

def const (q : ℚ) : CauchySeq :=
  Subtype.mk (fun _ : ℕ ↦ q)
    (by
       rw [IsCauchySeq]
       intro ε hε
       aesop)

/- 定义实数的加法需要稍多一些步骤。我们将柯西序列的加法定义为逐项相加： -/

instance Add : Add CauchySeq :=
  { add := fun f g : CauchySeq ↦
      Subtype.mk (fun n : ℕ ↦ seqOf f n + seqOf g n) sorry }

/- 在上文中，我们省略了两个柯西序列相加仍为柯西序列的证明。

接下来，我们需要证明这种加法与`≈`是兼容的。 -/

theorem Setoid_add {f f' g g' : CauchySeq} (hf : f ≈ f')
      (hg : g ≈ g') :
    f + g ≈ f' + g' :=
  by
    intro ε₀ hε₀
    simp [Setoid_iff]
    cases hf (ε₀ / 2) (by linarith) with
    | intro Nf hNf =>
      cases hg (ε₀ / 2) (by linarith) with
      | intro Ng hNg =>
        apply Exists.intro (max Nf Ng)
        intro m hm
        calc
          abs (seqOf (f + g) m - seqOf (f' + g') m)
          = abs ((seqOf f m + seqOf g m)
            - (seqOf f' m + seqOf g' m)) :=
            by rfl
          _ = abs ((seqOf f m - seqOf f' m)
              + (seqOf g m - seqOf g' m)) :=
            by
              have arg_eq :
                seqOf f m + seqOf g m
                  - (seqOf f' m + seqOf g' m) =
                seqOf f m - seqOf f' m
                  + (seqOf g m - seqOf g' m) :=
                by linarith
              rw [arg_eq]
          _ ≤ abs (seqOf f m - seqOf f' m)
              + abs (seqOf g m - seqOf g' m) :=
            by apply abs_add
          _ < ε₀ / 2 + ε₀ / 2 :=
            add_lt_add (hNf m (le_of_max_le_left hm))
              (hNg m (le_of_max_le_right hm))
          _ = ε₀ :=
            by simp

end CauchySeq

/- 实数是通过商（quotient）的方式定义的。 -/

def Real : Type :=
  Quotient CauchySeq.Setoid

namespace Real

instance Zero : Zero Real :=
  { zero := ⟦CauchySeq.const 0⟧ }

instance One : One Real :=
  { one := ⟦CauchySeq.const 1⟧ }

instance Add : Add Real :=
{ add := Quotient.lift₂ (fun a b : CauchySeq ↦ ⟦a + b⟧)
    (by
       intro a b a' b' ha hb
       apply Quotient.sound
       exact CauchySeq.Setoid_add ha hb) }

end Real


/- ### `ℝ` 的替代定义

* **戴德金分割**：`r : ℝ` 本质上表示为 `{x : ℚ | x < r}`。

* **二进制序列**：`ℕ → Bool` 可以表示区间 `[0, 1]`。这可以用于构建 `ℝ`。 -/

end LoVe
