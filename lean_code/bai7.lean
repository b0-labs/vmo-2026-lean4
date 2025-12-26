/-
We prove that for non-negative real numbers $a, b, c$ with $a+b+c=3$, the sum of square roots $\sqrt{3a^3+4bc+b+c} + \sqrt{3b^3+4ca+c+a} + \sqrt{3c^3+4ab+a+b} \ge 9$. The proof uses a rational lower bound for the square root, Titu's lemma, and Schur's inequality.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Schur's inequality for degree 3.
-/
def X (a b c : ℝ) : ℝ := 3 * a^3 + 4 * b * c + b + c

lemma schur_inequality (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
  a^3 + b^3 + c^3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) := by
    cases le_total a b <;> cases le_total a c <;> cases le_total b c <;> nlinarith [ sq_nonneg ( a - b ), sq_nonneg ( a - c ), sq_nonneg ( b - c ) ]

/-
If $a+b+c=3$, then $\sum X \ge 27$.
-/
lemma sum_X_ge_27 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h_sum : a + b + c = 3) :
  X a b c + X b c a + X c a b ≥ 27 := by
    revert h_sum;
    -- We compute the sum:
    -- $$
    -- X_a+X_b+X_c=3(a^3+b^3+c^3)+4(ab+bc+ca)+[(b+c)+(c+a)+(a+b)]
    -- $$
    intros h_sum
    simp [X];
    have := eq_sub_of_add_eq' h_sum;
    subst this; nlinarith [ sq_nonneg ( a - b ), sq_nonneg ( b - ( 3 - ( a + b ) ) ), sq_nonneg ( a - ( 3 - ( a + b ) ) ) ] ;

/-
X is non-negative for non-negative inputs.
-/
lemma X_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 0 ≤ X a b c := by
  exact add_nonneg ( by positivity ) ( by positivity )

/-
Prove the main inequality by squaring both sides.
-/
theorem problem_7 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h_sum : a + b + c = 3) :
  Real.sqrt (X a b c) + Real.sqrt (X b c a) + Real.sqrt (X c a b) ≥ 9 := by
    -- By AM-GM inequality, we know that $\sum \sqrt{X_a X_b} \geq 3 \sqrt[3]{\prod X_a}$.
    have h_am_gm_sqrt : Real.sqrt (X a b c * X b c a) + Real.sqrt (X b c a * X c a b) + Real.sqrt (X c a b * X a b c) ≥ 3 * Real.rpow (X a b c * X b c a * X c a b) (1/3 : ℝ) := by
      have h_am_gm_sqrt : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → Real.sqrt (x * y) + Real.sqrt (y * z) + Real.sqrt (z * x) ≥ 3 * Real.rpow (x * y * z) (1/3 : ℝ) := by
        -- By AM-GM inequality, we know that $\sqrt{xy} + \sqrt{yz} + \sqrt{zx} \geq 3 \sqrt[3]{\sqrt{xy} \cdot \sqrt{yz} \cdot \sqrt{zx}}$.
        intros x y z hx hy hz
        have h_am_gm_step : Real.sqrt (x * y) + Real.sqrt (y * z) + Real.sqrt (z * x) ≥ 3 * Real.rpow ((Real.sqrt (x * y)) * (Real.sqrt (y * z)) * (Real.sqrt (z * x))) (1/3 : ℝ) := by
          exact le_trans ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow ( by positivity ) ( show Real.sqrt ( x * y ) * Real.sqrt ( y * z ) * Real.sqrt ( z * x ) ≤ ( ( Real.sqrt ( x * y ) + Real.sqrt ( y * z ) + Real.sqrt ( z * x ) ) / 3 ) ^ 3 by nlinarith only [ sq_nonneg ( Real.sqrt ( x * y ) - Real.sqrt ( y * z ) ), sq_nonneg ( Real.sqrt ( y * z ) - Real.sqrt ( z * x ) ), sq_nonneg ( Real.sqrt ( z * x ) - Real.sqrt ( x * y ) ), Real.sqrt_nonneg ( x * y ), Real.sqrt_nonneg ( y * z ), Real.sqrt_nonneg ( z * x ) ] ) ( by positivity ) ) <| by positivity ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ; linarith );
        convert h_am_gm_step using 2 ; repeat ring <;> norm_num [ hx, hy, hz ] ;
      exact h_am_gm_sqrt _ _ _ ( X_nonneg _ _ _ ha hb hc ) ( X_nonneg _ _ _ hb hc ha ) ( X_nonneg _ _ _ hc ha hb );
    -- Therefore, it suffices to show that $3 \sqrt[3]{\prod X_a} \geq \frac{81 - \sum X_a}{2}$.
    suffices h_suff : 3 * Real.rpow (X a b c * X b c a * X c a b) (1/3 : ℝ) ≥ (81 - (X a b c + X b c a + X c a b)) / 2 by
      rw [ Real.sqrt_mul', Real.sqrt_mul', Real.sqrt_mul' ] at h_am_gm_sqrt <;> try exact X_nonneg _ _ _ ( by positivity ) ( by positivity ) ( by positivity ) ;
      nlinarith [ Real.sqrt_nonneg ( X a b c ), Real.sqrt_nonneg ( X b c a ), Real.sqrt_nonneg ( X c a b ), Real.mul_self_sqrt ( show 0 ≤ X a b c by exact X_nonneg a b c ha hb hc ), Real.mul_self_sqrt ( show 0 ≤ X b c a by exact X_nonneg b c a hb hc ha ), Real.mul_self_sqrt ( show 0 ≤ X c a b by exact X_nonneg c a b hc ha hb ) ];
    -- Cube both sides of the inequality to eliminate the cube root.
    suffices h_cube : 27 * (X a b c * X b c a * X c a b) ≥ ((81 - (X a b c + X b c a + X c a b)) / 2) ^ 3 by
      contrapose! h_cube;
      convert pow_lt_pow_left₀ h_cube ( mul_nonneg zero_le_three <| Real.rpow_nonneg ( mul_nonneg ( mul_nonneg ( show 0 ≤ X a b c from _ ) ( show 0 ≤ X b c a from _ ) ) ( show 0 ≤ X c a b from _ ) ) _ ) three_ne_zero using 1 <;> ring;
      · erw [ ← Real.rpow_natCast _ 3, ← Real.rpow_mul ( mul_nonneg ( mul_nonneg ( show 0 ≤ X a b c from _ ) ( show 0 ≤ X b c a from _ ) ) ( show 0 ≤ X c a b from _ ) ) ] ; norm_num;
        · exact X_nonneg a b c ha hb hc;
        · exact X_nonneg _ _ _ hb hc ha;
        · exact X_nonneg _ _ _ hc ha hb;
      · exact X_nonneg a b c ha hb hc;
      · exact X_nonneg _ _ _ hb hc ha;
      · exact X_nonneg _ _ _ hc ha hb;
    unfold X;
    obtain rfl := eq_sub_of_add_eq' h_sum;
    -- By Schur's inequality, we know that $a^3 + b^3 + c^3 + 3abc \geq a^2(b+c) + b^2(c+a) + c^2(a+b)$.
    have h_schur : a^3 + b^3 + (3 - a - b)^3 + 3 * a * b * (3 - a - b) ≥ a^2 * (b + (3 - a - b)) + b^2 * ((3 - a - b) + a) + (3 - a - b)^2 * (a + b) := by
      nlinarith only [ mul_nonneg ha ( sq_nonneg ( b - ( 3 - a - b ) ) ), mul_nonneg ha ( sq_nonneg ( ( 3 - a - b ) - a ) ), mul_nonneg ha ( sq_nonneg ( a - b ) ), mul_nonneg hb ( sq_nonneg ( ( 3 - a - b ) - a ) ), mul_nonneg hb ( sq_nonneg ( a - b ) ), mul_nonneg hb ( sq_nonneg ( b - ( 3 - a - b ) ) ), mul_nonneg hc ( sq_nonneg ( a - b ) ), mul_nonneg hc ( sq_nonneg ( b - ( 3 - a - b ) ) ), mul_nonneg hc ( sq_nonneg ( ( 3 - a - b ) - a ) ) ];
    have := mul_nonneg ha hb;
    have := mul_nonneg this hc;
    nlinarith only [ this, h_schur, sq_nonneg ( a * b * ( 3 - ( a + b ) ) - 1 ), sq_nonneg ( a * b - 1 ), sq_nonneg ( a * ( 3 - ( a + b ) ) - 1 ), sq_nonneg ( b * ( 3 - ( a + b ) ) - 1 ), sq_nonneg ( a - b ), sq_nonneg ( a - ( 3 - ( a + b ) ) ), sq_nonneg ( b - ( 3 - ( a + b ) ) ), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc ]
