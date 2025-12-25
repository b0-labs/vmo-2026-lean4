/-
Formalization of a math problem about operations on triples. Proves that 4 turns are needed to reach a triple with z=6, and 12 turns are needed to reach a triple with z=129.
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
Operation (i): Erase the triple (x, y, z) and write the triple (y, z, x+z).
-/
def opA (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let (x, y, z) := t
  (y, z, x + z)

/-
Operation (ii): Erase the triple (x, y, z) and write the triple (x+z+1, x+y+z+1, x+y+2z+1).
-/
def opB (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let (x, y, z) := t
  (x + z + 1, x + y + z + 1, x + y + 2 * z + 1)

/-
Reachable k t means the triple t can be reached in exactly k turns.
-/
inductive Reachable : ℕ → ℕ × ℕ × ℕ → Prop
| base : Reachable 0 (1, 1, 1)
| opA {k t} : Reachable k t → Reachable (k + 1) (opA t)
| opB {k t} : Reachable k t → Reachable (k + 1) (opB t)

/-
Define the sequence u_n where u_n is the third coordinate after applying operation (i) n times to (1,1,1).
Recurrence: u_{n+3} = u_{n+2} + u_n.
Base cases: u_0=1, u_1=2, u_2=3.
-/
def u : ℕ → ℕ
| 0 => 1
| 1 => 2
| 2 => 3
| (n + 3) => u (n + 2) + u n

/-
ReachableZ k z means there exists a triple (x, y, z) reachable in exactly k turns.
-/
def ReachableZ (k : ℕ) (z : ℕ) : Prop :=
  ∃ x y, Reachable k (x, y, z)

/-
An needs exactly 4 turns to be able to write a triple of the form (a, b, 6).
-/
theorem part_a : ReachableZ 4 6 ∧ ∀ k < 4, ¬ ReachableZ k 6 := by
  constructor;
  · -- Apply operation (i) four times to get from (1,1,1) to (3,4,6).
    have h1 : Reachable 4 (3, 4, 6) := by
      exact Reachable.opA (Reachable.opA (Reachable.opA (Reachable.opA (Reachable.base))));
    exact ⟨ _, _, h1 ⟩;
  · intro k hk_lt hk_reachable
    obtain ⟨x, y, h_reachable_k⟩ := hk_reachable
    have hk_le_3 : k ≤ 3 := by
      linarith;
    -- If $k \leq 3$, then by examining all possible sequences of operations, we can show that it's impossible to reach a triple with $z = 6$.
    have h_impossible : ∀ t : ℕ × ℕ × ℕ, Reachable k t → t.2.2 ≠ 6 := by
      interval_cases k <;> intro t ht <;> rcases ht with ( _ | ⟨ t, ht ⟩ | ⟨ t, ht ⟩ ) <;> simp_all +arith +decide;
      all_goals rename_i t ht; rcases ht with ( _ | ⟨ t, ht ⟩ | ⟨ t, ht ⟩ ) <;> simp_all +arith +decide;
    exact h_impossible _ h_reachable_k rfl

/-
Component-wise addition of triples.
-/
def add_triples (t1 t2 : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (t1.1 + t2.1, t1.2.1 + t2.2.1, t1.2.2 + t2.2.2)

/-
Linearity of operation A with respect to component-wise addition.
-/
lemma opA_linear (t1 t2 : ℕ × ℕ × ℕ) : opA (add_triples t1 t2) = add_triples (opA t1) (opA t2) := by
  unfold opA add_triples; ring;

/-
Relation B = A^3 + (1,1,1).
-/
lemma opB_eq_opA3_plus_ones (t : ℕ × ℕ × ℕ) : opB t = add_triples (opA (opA (opA t))) (1, 1, 1) := by
  unfold add_triples opA opB; ring;

/-
ReachableWithB k m t means the triple t can be reached in exactly k turns using operation (ii) exactly m times.
-/
inductive ReachableWithB : ℕ → ℕ → ℕ × ℕ × ℕ → Prop
| base : ReachableWithB 0 0 (1, 1, 1)
| opA {k m t} : ReachableWithB k m t → ReachableWithB (k + 1) m (opA t)
| opB {k m t} : ReachableWithB k m t → ReachableWithB (k + 1) (m + 1) (opB t)

/-
A list of exponents t_1, ..., t_m satisfies the spacing condition if t_j >= t_{j+1} + 3.
-/
inductive ValidExponents : List ℕ → Prop
| nil : ValidExponents []
| single {x} : ValidExponents [x]
| cons {x y rest} : x ≥ y + 3 → ValidExponents (y :: rest) → ValidExponents (x :: y :: rest)

/-
Sum of u_{t_j} for a list of exponents.
-/
def sum_u (ts : List ℕ) : ℕ :=
  ts.foldl (λ acc t => acc + u t) 0

/-
Iterated application of operation A. opA_n n t is the result of applying A n times to t.
-/
def opA_n (n : ℕ) (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  match n with
  | 0 => t
  | n + 1 => opA (opA_n n t)

/-
Linearity of iterated application of A. opA_n n (t1 + t2) = opA_n n t1 + opA_n n t2.
-/
lemma opA_n_add (n : ℕ) (t1 t2 : ℕ × ℕ × ℕ) :
  opA_n n (add_triples t1 t2) = add_triples (opA_n n t1) (opA_n n t2) := by
    induction' n with n ih generalizing t1 t2;
    · rfl;
    · -- By definition of `opA_n`, we have `opA_n (n + 1) t = opA (opA_n n t)`.
      have h_opA_n_succ : ∀ (n : ℕ) (t : ℕ × ℕ × ℕ), opA_n (n + 1) t = opA (opA_n n t) := by
        exact?;
      exact h_opA_n_succ n _ ▸ h_opA_n_succ n _ ▸ h_opA_n_succ n _ ▸ ih _ _ ▸ opA_linear _ _

/-
The third coordinate of A^n(1,1,1) is u_n.
-/
lemma opA_n_u (n : ℕ) : (opA_n n (1, 1, 1)).2.2 = u n := by
  -- By definition of $u$, we know that $u$ satisfies the recurrence $u_{n+3} = u_{n+2} + u_n$.
  have hu_rec : ∀ n, u (n + 3) = u (n + 2) + u n := by
    exact?;
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | _ | n ) <;> simp +arith +decide [ * ];
  rw [ add_comm, ← ih ];
  · rw [ Nat.add_comm, ← ih ];
    · unfold opA_n; aesop;
    · linarith;
  · grind

/-
Sum of A^{t_j}(1,1,1) for a list of exponents.
-/
def sum_opA_n (ts : List ℕ) : ℕ × ℕ × ℕ :=
  ts.foldl (λ acc t => add_triples acc (opA_n t (1, 1, 1))) (0, 0, 0)

/-
If a list of exponents satisfies the spacing condition, then adding 1 to each element preserves the condition.
-/
lemma valid_map_succ (ts : List ℕ) : ValidExponents ts → ValidExponents (ts.map (· + 1)) := by
  intro hts
  induction' hts with x xs hxs hxs';
  · constructor;
  · constructor;
  · norm_num +zetaDelta at *;
    exact ValidExponents.cons ( by linarith ) ‹_›

/-
If ts is a valid list of exponents, then appending 0 to the list obtained by adding 3 to each element of ts results in a valid list of exponents. This corresponds to the effect of operation B on the exponents.
-/
lemma valid_append_zero_map_add_three (ts : List ℕ) : ValidExponents ts → ValidExponents (ts.map (· + 3) ++ [0]) := by
  induction' ts with t ts ih;
  · tauto;
  · intro h;
    rcases h with ( _ | ⟨ _, _, _ ⟩ );
    · constructor;
      · linarith;
      · constructor;
    · exact ValidExponents.cons ( by linarith ) ( ih ‹_› )

/-
The z-coordinate of the sum of A^{t_j}(1,1,1) is the sum of u_{t_j}.
-/
lemma sum_opA_n_z (ts : List ℕ) : (sum_opA_n ts).2.2 = sum_u ts := by
  unfold sum_opA_n sum_u;
  induction' ts using List.reverseRecOn with t ts ih <;> simp_all +decide [ add_triples ];
  exact?

/-
The sum of the first and third coordinates of A^n(1,1,1) is u_{n+1}.
-/
lemma lemma_x_plus_z_eq_u_succ (n : ℕ) : (opA_n n (1, 1, 1)).1 + (opA_n n (1, 1, 1)).2.2 = u (n + 1) := by
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | _ | n ) <;> simp +arith +decide [ * ];
  have := ih ( n + 2 ) ( by linarith ) ; have := ih ( n + 1 ) ( by linarith ) ; have := ih n ( by linarith ) ; simp_all +arith +decide [ opA_n ] ;
  unfold opA at * ; simp_all +arith +decide [ u ] ;

/-
Applying A to the sum of A^{t_j}(1,1,1) is equivalent to summing A^{t_j+1}(1,1,1).
-/
lemma sum_opA_n_map_succ (ts : List ℕ) : sum_opA_n (ts.map (· + 1)) = opA (sum_opA_n ts) := by
  induction' ts using List.reverseRecOn with t ts ih <;> simp_all! +arith +decide [ sum_opA_n ];
  unfold add_triples; ring;

/-
Associativity of component-wise addition of triples.
-/
lemma add_triples_assoc (t1 t2 t3 : ℕ × ℕ × ℕ) :
  add_triples (add_triples t1 t2) t3 = add_triples t1 (add_triples t2 t3) := by
    exact Prod.ext ( add_assoc _ _ _ ) ( Prod.ext ( add_assoc _ _ _ ) ( add_assoc _ _ _ ) )

/-
Algebraic step for operation A in the structure lemma.
-/
lemma structure_step_opA (k m : ℕ) (ts : List ℕ) :
  opA (add_triples (opA_n (k + 2 * m) (1, 1, 1)) (sum_opA_n ts)) =
  add_triples (opA_n (k + 1 + 2 * m) (1, 1, 1)) (sum_opA_n (ts.map (· + 1))) := by
    -- Applying the linearity of `opA` and the fact that `opA_n` is well-defined.
    have h_linear : opA (add_triples (opA_n (k + 2 * m) (1, 1, 1)) (sum_opA_n ts)) = add_triples (opA (opA_n (k + 2 * m) (1, 1, 1))) (opA (sum_opA_n ts)) := by
      exact?;
    convert h_linear using 2;
    · exact Eq.symm ( by rw [ Nat.succ_add ] ; rfl );
    · exact?

/-
Algebraic step for operation B in the structure lemma.
-/
lemma structure_step_opB (k m : ℕ) (ts : List ℕ) :
  opB (add_triples (opA_n (k + 2 * m) (1, 1, 1)) (sum_opA_n ts)) =
  add_triples (opA_n (k + 1 + 2 * (m + 1)) (1, 1, 1)) (sum_opA_n (ts.map (· + 3) ++ [0])) := by
    unfold opB;
    induction' ts using List.reverseRecOn with t ts ih <;> simp_all +arith +decide [ sum_opA_n, opA_n ];
    · unfold opA; simp +arith +decide [ add_triples ] ;
    · unfold add_triples at * ; simp_all +arith +decide;
      unfold opA at * ; simp_all +arith +decide

/-
Stronger structure lemma: t is exactly A^{k+2m}(1,1,1) + sum A^{t_j}(1,1,1).
-/
theorem structure_lemma_strong {k m : ℕ} {t : ℕ × ℕ × ℕ} (h : ReachableWithB k m t) :
  ∃ ts : List ℕ, ValidExponents ts ∧ ts.length = m ∧ t = add_triples (opA_n (k + 2 * m) (1, 1, 1)) (sum_opA_n ts) ∧ (∀ x ∈ ts, x ≤ k + 2 * m - 3) := by
    revert h m t k;
    -- We proceed by induction on the structure of ReachableWithB.
    intro k m t h_reachable
    induction' h_reachable with k m t h_reachable ih;
    · exists [ ];
      exact ⟨ ValidExponents.nil, rfl, rfl, by norm_num ⟩;
    · obtain ⟨ts, hts_valid, hts_length, hts_eq, hts_bounds⟩ := ih
      use ts.map (· + 1);
      refine' ⟨ valid_map_succ ts hts_valid, _, _, _ ⟩ <;> simp_all +arith +decide;
      · convert structure_step_opA k m ts using 1;
        ac_rfl;
      · exact fun x hx => Nat.succ_le_of_lt ( lt_tsub_iff_right.mpr ( by linarith [ hts_bounds x hx, Nat.sub_add_cancel ( show 3 ≤ k + 2 * m from by linarith [ show k + 2 * m ≥ 3 by
                                                                                                                                                                  rcases m with ( _ | _ | m ) <;> simp_all +arith +decide;
                                                                                                                                                                  rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
                                                                                                                                                                  cases h_reachable ] ) ] ) );
    · obtain ⟨ ts, hts₁, hts₂, rfl, hts₃ ⟩ := ‹_›;
      rename_i hk;
      rename_i k' m' hk';
      refine' ⟨ ts.map ( · + 3 ) ++ [ 0 ], _, _, _, _ ⟩ <;> norm_num;
      · exact?;
      · exact hts₂;
      · convert structure_step_opB k' m' ts using 1;
      · rintro x ( ⟨ a, ha, rfl ⟩ | rfl ) <;> norm_num;
        exact le_tsub_of_add_le_left ( by linarith [ hts₃ a ha, Nat.sub_add_cancel ( show 3 ≤ k' + 2 * m' from by
                                                                                      contrapose! hts₃; interval_cases _ : k' + 2 * m' <;> simp_all +decide ;
                                                                                      · rcases m' with ( _ | _ | m' ) <;> simp_all +arith +decide;
                                                                                      · rcases m' with ( _ | _ | m' ) <;> simp_all +arith +decide;
                                                                                        cases hk' ) ] )

/-
u_12 is 129.
-/
lemma u_12_eq_129 : u 12 = 129 := by
  rfl

/-
It is possible to reach a triple with z=129 in 12 moves.
-/
theorem part_b_existence : ReachableZ 12 129 := by
  use (opA_n 12 (1, 1, 1)).1, (opA_n 12 (1, 1, 1)).2.1;
  convert Reachable.opA ( Reachable.opA ( Reachable.opA ( Reachable.opA ( Reachable.opA ( Reachable.opA ( Reachable.opA ( Reachable.opA ( Reachable.opA ( Reachable.opA ( Reachable.opA ( Reachable.opA Reachable.base ) ) ) ) ) ) ) ) ) ) ) using 1

/-
The sum of u_{t_j} for valid exponents bounded by 8 is at most 40.
-/
lemma sum_u_le_40_of_bound_8 (ts : List ℕ) (h_valid : ValidExponents ts) (h_bound : ∀ x ∈ ts, x ≤ 8) : sum_u ts ≤ 40 := by
  rcases ts with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | ⟨ w, _ | ts ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide;
  · interval_cases x <;> trivial;
  · rcases h_bound with ⟨ hx, hy ⟩ ; interval_cases x <;> interval_cases y <;> trivial;
  · rcases h_valid with ( _ | _ | h_valid ) <;> simp_all +arith +decide [ ValidExponents ];
    rcases h_bound with ⟨ hx, hy, hz ⟩ ; interval_cases x <;> interval_cases y <;> interval_cases z <;> trivial;
  · rcases h_valid with ⟨ ⟩;
    rcases ‹ValidExponents [ y, z, w ] › with ⟨ ⟩;
    rcases ‹ValidExponents [ z, w ] › with ⟨ ⟩ ; norm_num at * ; omega;
  · cases h_valid;
    cases ‹ValidExponents ( y :: z :: w :: ts :: _ ) ›;
    cases ‹ValidExponents ( z :: w :: ts :: _ ) › ; linarith

/-
If a triple is reachable in k steps, there exists some number m of operation B uses such that it is reachable with B.
-/
lemma reachable_implies_reachable_with_b {k : ℕ} {t : ℕ × ℕ × ℕ} (h : Reachable k t) :
  ∃ m, ReachableWithB k m t := by
    induction' k with k ih generalizing t;
    · cases h ; tauto;
    · rcases h with ( _ | _ | _ );
      · exact Exists.elim ( ih ‹_› ) fun m hm => ⟨ m, ReachableWithB.opA hm ⟩;
      · obtain ⟨ m, hm ⟩ := ih ‹_›; exact ⟨ m + 1, ReachableWithB.opB hm ⟩ ;

/-
u_n is always at least 1.
-/
lemma u_pos (n : ℕ) : u n ≥ 1 := by
  -- We'll use induction on $n$ to show that $u_n \geq 1$ for all $n$.
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | _ | n ) <;> simp +arith +decide [ *, u ];
  linarith [ ih n ( by linarith ), ih ( n + 1 ) ( by linarith ), ih ( n + 2 ) ( by linarith ) ]

/-
u_n is strictly increasing.
-/
lemma u_strict_mono (n : ℕ) : u n < u (n + 1) := by
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | _ | n ) <;> simp +arith +decide [ * ];
  -- By definition of $u$, we have $u (n + 4) = u (n + 3) + u (n + 1)$.
  have h_def : u (n + 4) = u (n + 3) + u (n + 1) := by
    rfl;
  linarith [ ih n ( by linarith ), ih ( n + 1 ) ( by linarith ), ih ( n + 2 ) ( by linarith ) ]

/-
It is impossible to reach a triple with z=129 in fewer than 12 moves.
-/
theorem part_b_impossibility (k : ℕ) (hk : k < 12) : ¬ ReachableZ k 129 := by
  -- AssumeReachableZ k 129. This means there exists m such that ReachableWithB k m (x, y, 129) for some x and y.
  by_contra h;
  -- Let's obtain the triple (x, y, 129) that is reachable in exactly k moves.
  obtain ⟨x, y, h_reachable⟩ : ∃ x y, Reachable k (x, y, 129) := by
    exact h;
  -- By the structure lemma, there exists a list of exponents ts such that ts.length = m and ts is valid, and 129 = u (k + 2 * m) + sum_u ts.
  obtain ⟨m, ts, h_valid, h_length, h_eq⟩ : ∃ m : ℕ, ∃ ts : List ℕ, ValidExponents ts ∧ ts.length = m ∧ 129 = u (k + 2 * m) + sum_u ts ∧ (∀ x ∈ ts, x ≤ k + 2 * m - 3) := by
    obtain ⟨m, h_reachable_with_b⟩ : ∃ m : ℕ, ReachableWithB k m (x, y, 129) := by
      exact?;
    have := structure_lemma_strong h_reachable_with_b;
    obtain ⟨ ts, hts₁, hts₂, hts₃, hts₄ ⟩ := this;
    refine' ⟨ m, ts, hts₁, hts₂, _, hts₄ ⟩;
    exact Eq.symm ( by { have := sum_opA_n_z ts; ( have := opA_n_u ( k + 2 * m ) ; ( unfold add_triples at *; aesop ) ) } );
  -- Let's consider the two cases: $k + 2m \geq 12$ and $k + 2m < 12$.
  by_cases h_case : k + 2 * m ≥ 12;
  · -- Since $k + 2m \geq 12$, we have $u (k + 2m) \geq u 12 = 129$.
    have h_u_ge_129 : u (k + 2 * m) ≥ 129 := by
      exact le_trans ( by native_decide ) ( monotone_nat_of_le_succ ( fun n => Nat.le_of_lt ( u_strict_mono n ) ) h_case );
    rcases m with ( _ | _ | m ) <;> simp +arith +decide at *;
    · interval_cases k;
    · interval_cases k <;> norm_num at *;
      · rcases ts with ( _ | ⟨ x, _ | ⟨ y, _ | ts ⟩ ⟩ ) <;> simp +arith +decide at *;
        rcases h_eq with ⟨ h_eq₁, h_eq₂ ⟩ ; interval_cases x <;> simp +decide at h_eq₁ h_eq₂ ⊢;
      · rcases ts with ( _ | ⟨ x, _ | ⟨ y, ts ⟩ ⟩ ) <;> simp +arith +decide at *;
        rcases h_eq with ⟨ h₁, h₂ ⟩ ; interval_cases x <;> exact absurd h₁ ( by native_decide );
    · -- Since $m \geq 1$, we have $sum_u ts \geq u 0 = 1$.
      have h_sum_u_ge_1 : sum_u ts ≥ 1 := by
        rcases ts with ( _ | ⟨ x, _ | ⟨ y, ts ⟩ ⟩ ) <;> simp +arith +decide at *;
        unfold sum_u; simp +arith +decide;
        induction' ts using List.reverseRecOn with ts ih <;> simp +arith +decide at *;
        · linarith [ u_pos x, u_pos y ];
        · exact le_add_of_le_of_nonneg ( u_pos _ ) ( Nat.zero_le _ );
      linarith;
  · have h_sum_u_le_40 : sum_u ts ≤ 40 := by
      apply sum_u_le_40_of_bound_8;
      · assumption;
      · exact fun x hx => le_trans ( h_eq.2 x hx ) ( by omega );
    interval_cases _ : k + 2 * m <;> simp_all ( config := { decide := Bool.true } ) only;
    all_goals norm_num [ show u 0 = 1 by rfl, show u 1 = 2 by rfl, show u 2 = 3 by rfl, show u 3 = 4 by rfl, show u 4 = 6 by rfl, show u 5 = 9 by rfl, show u 6 = 13 by rfl, show u 7 = 19 by rfl, show u 8 = 28 by rfl, show u 9 = 41 by rfl, show u 10 = 60 by rfl, show u 11 = 88 by rfl ] at * ; omega;

/-
12 is the smallest number of turns to reach 129.
-/
def MinReachableZ (k : ℕ) (z : ℕ) : Prop := ReachableZ k z ∧ ∀ j < k, ¬ ReachableZ j z

theorem part_b : MinReachableZ 12 129 := by
  -- Combine the existence and impossibility results to conclude the proof.
  constructor;
  · exact?;
  · exact?
