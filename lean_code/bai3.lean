/-
We define `divisors_in_interval` as the set of divisors of `a * b` strictly between `n^2` and `n^2 + n + 3`.
We prove `divisors_in_interval_eq`, stating that for positive integers `n, a, b` satisfying `1 < n^2 < a < b < n^2 + n + 3`,
this set is exactly `{a, b}`.
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

def divisors_in_interval (n a b : ℕ) : Set ℕ :=
  {d | d ∣ a * b ∧ n^2 < d ∧ d < n^2 + n + 3}

theorem divisors_in_interval_eq (n a b : ℕ) (h_n : 1 < n^2) (h_a : n^2 < a) (h_b : a < b) (h_upper : b < n^2 + n + 3) :
    divisors_in_interval n a b = {a, b} := by
  -- Assume there exists $c$ such that $c \in \text{divisors_in_interval } n a b$ and $c \notin \{a, b\}$.
  by_contra h_contra;
  -- Then there exists a divisor $d$ of $ab$ such that $d \in (n^2, n^2 + n + 3)$ and $d \notin \{a, b\}$.
  obtain ⟨d, hd₁, hd₂⟩ : ∃ d, d ∈ (Nat.divisors (a * b)) ∧ n^2 < d ∧ d < n^2 + n + 3 ∧ d ≠ a ∧ d ≠ b := by
    unfold divisors_in_interval at h_contra; simp_all +decide [ Finset.ext_iff ] ;
    simp_all +decide [ Set.ext_iff ];
    rcases h_contra with ⟨ x, hx ⟩ ; use x; by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all +decide ;
    push_neg at hx; aesop;
    · linarith;
    · linarith [ left ( by linarith ) ];
  -- Since $d \mid ab$, we have $n^2 + z \mid (n^2 + x)(n^2 + y)$.
  have h_div : ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y ≤ n + 2 ∧ 1 ≤ z ∧ z ≤ n + 2 ∧ d = n^2 + z ∧ a = n^2 + x ∧ b = n^2 + y := by
    exact ⟨ a - n ^ 2, b - n ^ 2, d - n ^ 2, Nat.sub_pos_of_lt <| by linarith, by omega, by omega, Nat.sub_pos_of_lt <| by linarith, by omega, by omega, by omega, by omega ⟩;
  -- Taking modulo $n^2 + z$, we have $n^2 \equiv -z$, therefore $(n^2 + x)(n^2 + y) \equiv (x - z)(y - z) \pmod{n^2 + z}$.
  obtain ⟨x, y, z, hx₁, hx₂, hy₁, hy₂, hz₁, hz₂, hd, ha, hb⟩ := h_div
  have h_mod : (x - z : ℤ) * (y - z : ℤ) ≡ 0 [ZMOD (n^2 + z : ℤ)] := by
    have h_mod : (n^2 + x) * (n^2 + y) ≡ (x - z) * (y - z) [ZMOD (n^2 + z : ℤ)] := by
      exact Int.ModEq.mul ( Int.modEq_iff_dvd.mpr ⟨ -1, by ring ⟩ ) ( Int.modEq_iff_dvd.mpr ⟨ -1, by ring ⟩ );
    exact h_mod.symm.trans ( Int.modEq_zero_iff_dvd.mpr <| mod_cast hz₂ ▸ Nat.dvd_of_mem_divisors hd₁ |> fun h => by aesop );
  -- Since $|(x - z)(y - z)| < 2(n^2 + z)$, we have $(x - z)(y - z) = 0$ or $(x - z)(y - z) = \pm(n^2 + z)$.
  have h_cases : (x - z : ℤ) * (y - z : ℤ) = 0 ∨ (x - z : ℤ) * (y - z : ℤ) = (n^2 + z : ℤ) ∨ (x - z : ℤ) * (y - z : ℤ) = -(n^2 + z : ℤ) := by
    have h_cases : |(x - z : ℤ) * (y - z : ℤ)| < 2 * (n^2 + z : ℤ) := by
      rw [ abs_mul ];
      exact lt_of_le_of_lt ( mul_le_mul ( show |( x : ℤ ) - z| ≤ n + 1 by exact abs_le.mpr ⟨ by linarith, by linarith ⟩ ) ( show |( y : ℤ ) - z| ≤ n + 1 by exact abs_le.mpr ⟨ by linarith, by linarith ⟩ ) ( by positivity ) ( by positivity ) ) ( by nlinarith only [ h_n, hy₂ ] );
    obtain ⟨ k, hk ⟩ := Int.modEq_zero_iff_dvd.mp h_mod;
    have : k ≤ 1 := Int.le_of_lt_add_one ( by nlinarith only [ abs_lt.mp h_cases, hk ] ) ; ( have : k ≥ -1 := Int.le_of_lt_add_one ( by nlinarith only [ abs_lt.mp h_cases, hk ] ) ; interval_cases k <;> simp_all +decide ; );
  rcases h_cases with h | h | h <;> simp_all +decide [ sub_eq_iff_eq_add ];
  · aesop;
  · -- If $(x - z)(y - z) = n^2 + z$, then $n + 1 \mid (n^2 + z)$.
    have h_div_n1 : (n + 1 : ℤ) ∣ (n^2 + z : ℤ) := by
      -- Since $|(x - z)(y - z)| < 2(n^2 + z)$, we have $(x - z)(y - z) = \pm(n^2 + z)$.
      have h_cases : (x - z : ℤ) = n + 1 ∨ (y - z : ℤ) = n + 1 ∨ (x - z : ℤ) = -(n + 1) ∨ (y - z : ℤ) = -(n + 1) := by
        by_cases h_cases : (x - z : ℤ) ≤ n ∧ (y - z : ℤ) ≤ n;
        · nlinarith only [ h, h_cases, hx₁, hx₂, hy₁, hy₂, hz₁, hz₂ ];
        · by_cases h_cases : (x - z : ℤ) > n ∨ (y - z : ℤ) > n;
          · bound;
          · push_neg at h_cases; aesop;
      rcases h_cases with h_cases | h_cases | h_cases | h_cases <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · exact dvd_of_mul_right_eq _ h;
      · exact dvd_of_mul_left_eq _ h;
      · exact ⟨ - ( y - z ), by linarith ⟩;
      · exact ⟨ - ( x - z ), by linarith ⟩;
    -- Since $n + 1 \mid (n^2 + z)$, we have $z \equiv -1 \pmod{n + 1}$.
    have h_z_mod : z ≡ -1 [ZMOD (n + 1 : ℤ)] := by
      exact Int.modEq_iff_dvd.mpr ( by obtain ⟨ k, hk ⟩ := h_div_n1; exact ⟨ -k + n - 1, by linarith ⟩ );
    -- Since $1 \leq z \leq n + 2$, the unique solution is $z = n$.
    have h_z_eq_n : z = n := by
      obtain ⟨ k, hk ⟩ := h_z_mod.symm.dvd;
      nlinarith only [ hk, show k = 1 by nlinarith only [ hk, hy₂, hz₁, h_n ] ];
    simp_all +decide [ Int.modEq_iff_dvd ];
    nlinarith only [ hx₁, hx₂, hy₁, h, h_n ];
  · -- If $u \leq n$ and $v \leq n$, then $uv \leq n^2$, contradicting $uv = n^2 + z$. Thus at least one of $u, v$ equals $n+1$.
    have huv_eq_n1 : (Int.natAbs (x - z)) = n + 1 ∨ (Int.natAbs (y - z)) = n + 1 := by
      by_cases hu : Int.natAbs (x - z) ≤ n;
      · by_cases hv : Int.natAbs (y - z) ≤ n;
        · nlinarith only [ abs_le.mp ( show |( x : ℤ ) - z| ≤ n by linarith ), abs_le.mp ( show |( y : ℤ ) - z| ≤ n by linarith ), h, hd₂ ];
        · exact Or.inr ( by cases abs_cases ( y - z : ℤ ) <;> linarith );
      · exact Or.inl ( by cases abs_cases ( x - z : ℤ ) <;> linarith );
    cases huv_eq_n1 <;> simp_all +decide [ Int.natAbs_eq_iff ];
    · cases ‹_› <;> nlinarith only [ h, hx₁, hx₂, hy₁, hy₂, ‹_› ];
    · cases ‹_› <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · nlinarith only [ h, hx₁, hx₂, hy₁, hy₂, hz₁, hz₂, ‹_› ];
      · grind
