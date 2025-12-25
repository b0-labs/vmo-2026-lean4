/-
We define the polynomial $P_n(x)$ and prove it has a unique positive root $a_n$.
We then define the sequence $b_n = (2-a_n)/n$ and the partial sums $c_n$.
We prove that the series $\sum b_n$ converges by comparing it to $\sum 1/n^2$,
and thus the sequence $(c_n)$ has a finite limit.
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
Definition of the polynomial P_n(x) = x^{3n} - 3 * 4^{n-1} * x^n - 2^{3n-3}
-/
noncomputable def P (n : ℕ) (x : ℝ) : ℝ := x^(3*n) - 3 * 4^(n-1) * x^n - 2^(3*n-3)

/-
Definition of the polynomial Q(t) = 8t^3 - 6t - 1
-/
def Q (t : ℝ) : ℝ := 8 * t^3 - 6 * t - 1

/-
The polynomial Q(t) = 8t^3 - 6t - 1 has exactly one positive root.
-/
theorem Q_has_unique_pos_root : ∃! t, 0 < t ∧ Q t = 0 := by
  unfold Q;
  apply_rules [ existsUnique_of_exists_of_unique ];
  · -- By Intermediate Value Theorem, since $Q(1/2) < 0$ and $Q(1) > 0$, there exists $t \in (1/2, 1)$ such that $Q(t) = 0$.
    have h_ivt : ∃ t ∈ Set.Ioo (1 / 2 : ℝ) 1, 8 * t^3 - 6 * t - 1 = 0 := by
      apply_rules [ intermediate_value_Ioo ] <;> norm_num;
      exact Continuous.continuousOn ( by continuity );
    exact h_ivt.imp fun x hx => ⟨ by linarith [ hx.1.1 ], hx.2 ⟩;
  · intros y₁ y₂ hy₁ hy₂;
    nlinarith [ mul_pos hy₁.1 hy₂.1, mul_pow y₁ y₂ 2 ]

/-
Algebraic identity relating P_n(x) and Q((x/2)^n).
-/
lemma P_eq_Q_scaled (n : ℕ) (hn : 0 < n) (x : ℝ) :
  P n x = 2^(3*n-3) * Q ((x/2)^n) := by
    -- Let's set $t = \frac{x}{2}$ and rewrite $P_n(x)$ in terms of $t$.
    set t : ℝ := x / 2;
    unfold P Q; ring;
    rcases n with ( _ | _ | n ) <;> norm_num [ Nat.mul_succ, pow_succ ] at * ; ring_nf at *;
    · ring;
    · norm_num [ Nat.succ_eq_add_one, add_mul, pow_add ] ; ring;
      simpa [ pow_mul', mul_assoc, ← mul_pow ] using by ring;

/-
For any positive integer n, P_n(x) has exactly one positive real root.
-/
theorem P_has_unique_pos_root (n : ℕ) (hn : 0 < n) : ∃! x, 0 < x ∧ P n x = 0 := by
  -- Since 2^(3n-3) is never zero for n > 0, the unique positive root of P_n will correspond to that root of Q(t).
  have h_unique_root : ∃! t : ℝ, 0 < t ∧ Q t = 0 := by
    exact?;
  -- Since $f$ is a strictly increasing bijection from $(0, \infty)$ to $(0, \infty)$, we know there is exactly one $x > 0$ such that $f(x) = t$.
  obtain ⟨t, ht₀, ht₁⟩ : ∃! t : ℝ, 0 < t ∧ Q t = 0 := h_unique_root
  have h_unique_x : ∃! x : ℝ, 0 < x ∧ (x / 2)^n = t := by
    refine' ⟨ 2 * Real.rpow t ( 1 / n ), _, _ ⟩ <;> norm_num [ hn.ne', ht₀.1.ne' ];
    · exact ⟨ Real.rpow_pos_of_pos ht₀.1 _, by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ht₀.1.le, inv_mul_cancel₀ ( by positivity ), Real.rpow_one ] ⟩;
    · intro y hy₁ hy₂; rw [ ← hy₂, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_inv_cancel₀ ( by positivity ), Real.rpow_one ] ; ring;
  convert h_unique_x using 2;
  norm_num [ P_eq_Q_scaled n hn, ht₀ ];
  bound

/-
Definition of a_n as the unique positive root of P_n(x), and a lemma stating its property.
-/
noncomputable def a (n : ℕ) : ℝ :=
  if h : 0 < n then Classical.choose (P_has_unique_pos_root n h).exists else 0

lemma a_spec (n : ℕ) (h : 0 < n) : 0 < a n ∧ P n (a n) = 0 := by
  have := @Q_has_unique_pos_root;
  cases' this with t ht;
  unfold a;
  have := Classical.choose_spec ( P_has_unique_pos_root n h );
  grind +ring

/-
Definition of b_n = (2 - a_n) / n and c_n = sum_{k=1}^n b_k.
-/
noncomputable def b (n : ℕ) : ℝ := (2 - a n) / n

noncomputable def c (n : ℕ) : ℝ := Finset.sum (Finset.range n) (fun k => b (k + 1))

/-
a_n is equal to 2 * t0^(1/n).
-/
noncomputable def t0 : ℝ := Classical.choose Q_has_unique_pos_root.exists

lemma t0_spec : 0 < t0 ∧ Q t0 = 0 := Classical.choose_spec Q_has_unique_pos_root.exists

lemma a_eq_t0_pow (n : ℕ) (h : 0 < n) : a n = 2 * t0 ^ (1 / n : ℝ) := by
  -- From the uniqueness part of the lemma, we know that $(a_n / 2)^n = t0$.
  have h_eq : ((a n) / 2) ^ n = t0 := by
    -- By definition of $a_n$, we know that $(a_n/2)^n$ is a root of $Q(t)$.
    have h_root_Q : Q ((a n / 2) ^ n) = 0 := by
      have := a_spec n h;
      rw [ P_eq_Q_scaled ] at this <;> aesop;
    -- By definition of $t0$, $t0$ is the unique positive root of $Q(t)$.
    have h_unique_root_Q : ∀ t : ℝ, 0 < t ∧ Q t = 0 → t = t0 := by
      exact fun t ht => ( Q_has_unique_pos_root.unique ht ( Classical.choose_spec ( Q_has_unique_pos_root.exists ) ) );
    exact h_unique_root_Q _ ⟨ pow_pos ( div_pos ( a_spec n h |>.1 ) zero_lt_two ) _, h_root_Q ⟩;
  rw [ ← h_eq, ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith [ a_spec n h ] ), mul_one_div_cancel ( by positivity ), Real.rpow_one, mul_div_cancel₀ _ ( by positivity ) ]

/-
Definition of s = -ln(t0) and proof that s > 0.
-/
noncomputable def s : ℝ := -Real.log t0

lemma s_pos : 0 < s := by
  unfold s;
  norm_num;
  refine' Real.log_neg _ _;
  · exact t0_spec.1;
  · -- By definition of $t0$, we know that $t0$ is the unique positive root of $Q(t) = 8t^3 - 6t - 1$.
    have ht0_root : Q t0 = 0 := by
      exact Classical.choose_spec Q_has_unique_pos_root.exists |>.2;
    unfold Q at ht0_root ; nlinarith [ sq_nonneg ( t0^2 ) ]

/-
b_n is bounded above by 2s/n^2.
-/
lemma b_le_bound (n : ℕ) (h : 0 < n) : b n ≤ 2 * s / n^2 := by
  -- We have $b_n = \frac{2 - a_n}{n}$, and $a_n = 2 t_0^{1/n}$.
  have h_b_eq : b n = (2 - 2 * t0^(1/n : ℝ)) / n := by
    exact a_eq_t0_pow n h ▸ rfl;
  -- Using the inequality $e^x \ge 1+x$ with $x = -s/n$, we get $e^{-s/n} \ge 1 - s/n$.
  have h_exp_ineq : t0^(1/n : ℝ) ≥ 1 - s / n := by
    rw [ Real.rpow_def_of_pos ] <;> norm_num [ s ];
    · ring_nf;
      linarith [ Real.add_one_le_exp ( Real.log t0 * ( n : ℝ ) ⁻¹ ) ];
    · exact t0_spec.1;
  ring_nf at *;
  nlinarith [ inv_pos.mpr ( by positivity : 0 < ( n : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ) ]

/-
The series sum(b_n) is summable.
-/
theorem b_summable : Summable (fun n => b (n + 1)) := by
  -- We have shown that $b_n \le \frac{2s}{n^2}$ for all $n \ge 1$. The series $\sum \frac{1}{n^2}$ converges (it is the Basel problem, or p-series with p=2).
  have h_summable : Summable (fun n : ℕ => 2 * s / n^2) := by
    exact Summable.mul_left _ <| Real.summable_nat_pow_inv.2 one_lt_two;
  refine' .of_nonneg_of_le ( fun n => _ ) ( fun n => _ ) ( h_summable.comp_injective Nat.succ_injective );
  · -- Since $a_n = 2 * t0^(1/(n+1))$ and $t0^(1/(n+1)) < 1$, we have $a_n < 2$. Therefore, $2 - a_n > 0$.
    have h_pos : 0 < 2 - a (n + 1) := by
      -- By definition of $a$, we know that $a (n + 1) = 2 * t0^(1/(n + 1))$.
      have h_a_def : a (n + 1) = 2 * t0^(1/(n + 1) : ℝ) := by
        exact_mod_cast a_eq_t0_pow _ n.succ_pos;
      norm_num [ h_a_def ];
      exact Real.rpow_lt_one ( by linarith [ t0_spec ] ) ( by linarith [ show t0 < 1 from by have := t0_spec; norm_num [ Q ] at *; nlinarith [ sq_nonneg ( t0^2 ) ] ] ) ( by positivity );
    exact div_nonneg h_pos.le ( Nat.cast_nonneg _ );
  · exact b_le_bound _ n.succ_pos

/-
The sequence (c_n) has a finite limit.
-/
theorem c_converges : ∃ L, Filter.Tendsto c Filter.atTop (nhds L) := by
  use ∑' k, b ( k + 1 );
  convert Summable.hasSum _ |> HasSum.tendsto_sum_nat using 1;
  exact?
