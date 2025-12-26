/-
For part (a), we proved `part_a` which states that for k=1, there are exactly 9 valid placements of 4 marbles.

For part (b), we determined that the largest number N is 3k-1.
We defined `can_avoid_marked k N` as the property that for any set of N marked cells, there exists a valid placement avoiding them.
We proved `part_b_upper_bound`: `¬ can_avoid_marked k (3 * k)`, showing that N cannot be 3k or larger (since we can mark a full row).
We proved `part_b_lower_bound`: `can_avoid_marked k (3 * k - 1)`, showing that N = 3k-1 is achievable.
The proof of the lower bound uses Hall's Marriage Theorem (via `exists_double_covering_matching`) to construct the placement in two blocks, based on a "good" set of rows and columns with few marked cells.
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
Definitions for the problem. Grid is 3k x 3k. Valid placement conditions: row/col coverage and no isolated marbles.
-/
open Finset

/-- The grid is a set of coordinates (col, row). -/
def Grid (k : ℕ) := Fin (3 * k) × Fin (3 * k)

/-- A placement is valid if every row and column has a marble, and every marble shares a row or column with another marble. -/
def is_valid_placement (k : ℕ) (M : Finset (Grid k)) : Prop :=
  (∀ r : Fin (3 * k), ∃ c, (c, r) ∈ M) ∧
  (∀ c : Fin (3 * k), ∃ r, (c, r) ∈ M) ∧
  (∀ p ∈ M, ∃ p' ∈ M, p' ≠ p ∧ (p'.1 = p.1 ∨ p'.2 = p.2))

/-
Instances for Fintype and DecidableEq for Grid k, necessary for Finset operations.
-/
instance (k : ℕ) : Fintype (Grid k) := by unfold Grid; infer_instance
instance (k : ℕ) : DecidableEq (Grid k) := by unfold Grid; infer_instance

/-
For k=1, there are exactly 9 ways to place 4 marbles satisfying the conditions.
-/
theorem part_a : ((Finset.univ : Finset (Grid 1)).powerset.filter (fun M => M.card = 4 ∧ is_valid_placement 1 M)).card = 9 := by
  unfold is_valid_placement;
  rw [ Finset.card_filter ];
  rw [ Finset.sum_congr rfl ];
  rotate_right;
  exact fun x => if x.card = 4 ∧ ( ∀ r : Fin 3, ∃ c : Fin 3, ( c, r ) ∈ x ) ∧ ( ∀ c : Fin 3, ∃ r : Fin 3, ( c, r ) ∈ x ) ∧ ∀ p ∈ x, ∃ p' ∈ x, p' ≠ p ∧ ( p'.1 = p.1 ∨ p'.2 = p.2 ) then 1 else 0;
  · native_decide;
  · aesop

/-
Definition of the property that we can avoid any set of N marked cells.
-/
/-- Property: For any set of `N` marked cells, there exists a valid placement of `4k` marbles avoiding them. -/
def can_avoid_marked (k : ℕ) (N : ℕ) : Prop :=
  ∀ (Marked : Finset (Grid k)), Marked.card = N →
    ∃ M : Finset (Grid k), M.card = 4 * k ∧ is_valid_placement k M ∧ Disjoint M Marked

/-
The number of marked cells cannot be 3k (or more), because we can mark an entire row, forcing a collision.
-/
def N_max (k : ℕ) : ℕ := 3 * k - 1

theorem part_b_upper_bound (k : ℕ) (hk : k ≥ 1) : ¬ can_avoid_marked k (3 * k) := by
  simp +zetaDelta at *;
  -- Let's choose any set of marked cells of size $3k$.
  intro h
  have h_marked : ∃ Marked : Finset (Grid k), Marked.card = 3 * k ∧ ∃ r : Fin (3 * k), ∀ c : Fin (3 * k), (c, r) ∈ Marked := by
    use Finset.univ.image (fun c => (c, ⟨0, by linarith⟩));
    rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    · exact ⟨ _, fun _ => rfl ⟩;
    · grind;
  obtain ⟨ Marked, hMarked₁, r, hr ⟩ := h_marked;
  obtain ⟨ M, hM₁, hM₂, hM₃ ⟩ := h Marked hMarked₁;
  have := hM₂.1 r;
  exact Finset.disjoint_left.mp hM₃ this.choose_spec ( hr _ )

/-
In a balanced bipartite graph K_{m,m}, if we remove fewer than m edges, a perfect matching still exists.
-/
theorem exists_matching_avoiding_bad_edges {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  (hUV : Fintype.card U = Fintype.card V)
  (Bad : Finset (U × V)) (hBad : Bad.card < Fintype.card U) :
  ∃ f : U → V, Function.Bijective f ∧ ∀ u, (u, f u) ∉ Bad := by
    obtain ⟨f, hf⟩ : ∃ (f : U → V), Function.Injective f ∧ ∀ u, (u, f u) ∉ Bad := by
      -- By Hall's Marriage Theorem, a perfect matching exists in the bipartite graph where edges are pairs $(u, v) \notin Bad$.
      have hall_theorem : ∀ S : Finset U, S.card ≤ (Finset.biUnion S (fun u => Finset.filter (fun v => (u, v) ∉ Bad) (Finset.univ : Finset V))).card := by
        -- Let $S$ be a subset of $U$ and $T$ be the set of vertices in $V$ adjacent to at least one vertex in $S$.
        intro S
        set T := Finset.biUnion S (fun u => Finset.univ.filter (fun v => (u, v) ∉ Bad)) with hT;
        -- The number of edges between $S$ and $V \setminus T$ is at least $|S| \cdot |V \setminus T|$.
        have h_edges : Finset.card (Finset.filter (fun e => e.1 ∈ S ∧ e.2 ∉ T) Bad) ≥ Finset.card S * (Fintype.card V - Finset.card T) := by
          have h_edges : ∀ u ∈ S, Finset.card (Finset.filter (fun v => (u, v) ∈ Bad) (Finset.univ \ T)) ≥ Fintype.card V - Finset.card T := by
            intro u hu
            have h_edges_u : Finset.card (Finset.filter (fun v => (u, v) ∈ Bad) (Finset.univ \ T)) = Finset.card (Finset.univ \ T) := by
              refine' congr_arg Finset.card ( Finset.ext fun v => _ );
              aesop;
            simp_all +decide [ Finset.card_sdiff ];
          have h_edges : Finset.card (Finset.filter (fun e => e.1 ∈ S ∧ e.2 ∉ T) Bad) = Finset.sum S (fun u => Finset.card (Finset.filter (fun v => (u, v) ∈ Bad) (Finset.univ \ T))) := by
            have h_edges : Finset.filter (fun e => e.1 ∈ S ∧ e.2 ∉ T) Bad = Finset.biUnion S (fun u => Finset.image (fun v => (u, v)) (Finset.filter (fun v => (u, v) ∈ Bad) (Finset.univ \ T))) := by
              grind;
            rw [ h_edges, Finset.card_biUnion ];
            · exact Finset.sum_congr rfl fun u hu => by rw [ Finset.card_image_of_injective ] ; aesop_cat;
            · exact fun u hu v hv huv => Finset.disjoint_left.mpr fun x hx₁ hx₂ => huv <| by aesop;
          exact h_edges.symm ▸ le_trans ( by simp +decide ) ( Finset.sum_le_sum ‹∀ u ∈ S, Fintype.card V - #T ≤ # ( Finset.filter ( fun v => ( u, v ) ∈ Bad ) ( Finset.univ \ T ) ) › );
        -- Since $|Bad| < |U|$, we have $|S| \cdot |V \setminus T| < |U|$.
        have h_card_bad : Finset.card (Finset.filter (fun e => e.1 ∈ S ∧ e.2 ∉ T) Bad) ≤ Finset.card Bad := by
          exact Finset.card_filter_le _ _;
        contrapose! h_edges;
        refine' lt_of_le_of_lt h_card_bad ( lt_of_lt_of_le hBad _ );
        rw [ hUV, mul_tsub ];
        exact le_tsub_of_add_le_left ( by nlinarith [ show Finset.card T < Finset.card S from h_edges, show Finset.card S ≤ Fintype.card U from le_trans ( Finset.card_le_univ _ ) ( by simp +decide [ hUV ] ) ] );
      have := @Finset.all_card_le_biUnion_card_iff_exists_injective U V; aesop;
    have := Fintype.bijective_iff_injective_and_card f; aesop;

/-
Given a function f on 3k elements with sum <= 3k-1, there exists a subset of size k with sum <= k-1.
-/
lemma exists_small_sum_subset (k : ℕ) (hk : k ≥ 1) (f : Fin (3 * k) → ℕ) (hf : Finset.univ.sum f ≤ 3 * k - 1) :
  ∃ S : Finset (Fin (3 * k)), S.card = k ∧ S.sum f ≤ k - 1 := by
    -- Assume for contradiction that no subset of size $k$ has a sum less than $k$.
    by_contra h_contra
    push_neg at h_contra
    have h_all_ge_k : ∀ S : Finset (Fin (3 * k)), S.card = k → ∑ x ∈ S, f x ≥ k := by
      exact fun S hS => Nat.le_of_pred_lt ( h_contra S hS );
    -- By the pigeonhole principle, if we consider all possible subsets of size $k$, there must be at least one subset where the sum of $f$ is strictly less than $k$.
    obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (3 * k)), S.card = 2 * k ∧ ∑ x ∈ S, f x ≥ 2 * k := by
      -- Choose any $k$ rows and calculate the sum of the marked cells in those rows.
      obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Finset (Fin (3 * k)), S₁.card = k ∧ ∑ x ∈ S₁, f x ≥ k := by
        exact ⟨ Finset.Ico ⟨ 0, by linarith ⟩ ⟨ k, by linarith ⟩, by simp +decide, h_all_ge_k _ <| by simp +decide ⟩;
      -- Choose any $k$ rows from the remaining $2k$ rows and calculate the sum of the marked cells in those rows.
      obtain ⟨S₂, hS₂⟩ : ∃ S₂ : Finset (Fin (3 * k)), S₂.card = k ∧ ∑ x ∈ S₂, f x ≥ k ∧ Disjoint S₁ S₂ := by
        have h_remaining : ∃ S₂ : Finset (Fin (3 * k)), S₂ ⊆ Finset.univ \ S₁ ∧ S₂.card = k := by
          have h_remaining : (Finset.univ \ S₁).card ≥ k := by
            simp +decide [ Finset.card_sdiff, * ];
            omega;
          exact?;
        exact ⟨ h_remaining.choose, h_remaining.choose_spec.2, h_all_ge_k _ h_remaining.choose_spec.2, Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp ( h_remaining.choose_spec.1 hx₂ ) |>.2 hx₁ ⟩;
      exact ⟨ S₁ ∪ S₂, by rw [ Finset.card_union_of_disjoint hS₂.2.2, hS₁.1, hS₂.1 ] ; ring, by rw [ Finset.sum_union hS₂.2.2 ] ; linarith ⟩;
    -- The complement of $S$ in the universal set has size $k$ and its sum of $f$ is at most $3k-1 - 2k = k-1$.
    have h_complement : ∑ x ∈ Finset.univ \ S, f x ≤ 3 * k - 1 - 2 * k := by
      exact le_tsub_of_add_le_left ( by rw [ ← Finset.sum_sdiff ( Finset.subset_univ S ) ] at *; linarith );
    have h_complement_card : (Finset.univ \ S).card = k := by
      simp +decide [ Finset.card_sdiff, * ] ; omega;
    grind

/-
Given C and R with |C| = 2|R|, and a small set of bad pairs, we can cover C such that each element of C is used once and each element of R is used twice.
-/
lemma exists_double_covering_matching {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
  (hRC : Fintype.card C = 2 * Fintype.card R)
  (Bad : Finset (C × R))
  (hBad : Bad.card < Fintype.card R) :
  ∃ M : Finset (C × R),
    (∀ p ∈ M, p ∉ Bad) ∧
    (∀ c : C, ∃! r : R, (c, r) ∈ M) ∧
    (∀ r : R, (M.filter (fun p => p.2 = r)).card = 2) := by
      -- Let's define the bad edges and apply the matching lemma.
      set Bad_edges : Finset (C × (R × Fin 2)) := Finset.image (fun p => (p.1, (p.2, 0))) Bad ∪ Finset.image (fun p => (p.1, (p.2, 1))) Bad;
      -- Apply the matching lemma to find a bijection $f : C \to R \times \{0, 1\}$ that avoids $Bad_edges$.
      obtain ⟨f, hf_bij, hf_bad⟩ : ∃ f : C → R × Fin 2, Function.Bijective f ∧ ∀ c, (c, f c) ∉ Bad_edges := by
        have := exists_matching_avoiding_bad_edges ( show Fintype.card C = Fintype.card ( R × Fin 2 ) by simp +decide [ hRC, mul_comm ] ) Bad_edges ?_;
        · exact this;
        · grind;
      refine' ⟨ Finset.image ( fun c => ( c, f c |>.1 ) ) Finset.univ, _, _, _ ⟩;
      · simp +zetaDelta at *;
        intro c hc; specialize hf_bad c; rcases h : f c with ⟨ r, i ⟩ ; fin_cases i <;> aesop;
      · intro c; use ( f c |>.1 ) ; aesop;
      · intro r
        have h_card : Finset.card (Finset.filter (fun c => (f c).1 = r) Finset.univ) = 2 := by
          have h_card : Finset.card (Finset.filter (fun c => (f c).1 = r) Finset.univ) = Finset.card (Finset.filter (fun p => p.1 = r) (Finset.image f Finset.univ)) := by
            rw [ Finset.card_filter, Finset.card_filter ];
            rw [ Finset.sum_image <| by intro c hc c' hc' h; exact hf_bij.injective h ];
          rw [ h_card, Finset.card_filter ];
          rw [ show ( Finset.image f Finset.univ : Finset ( R × Fin 2 ) ) = Finset.univ from Finset.eq_univ_of_forall fun x => Finset.mem_image.mpr ⟨ Classical.choose ( hf_bij.2 x ), Finset.mem_univ _, Classical.choose_spec ( hf_bij.2 x ) ⟩ ] ; simp +decide [ Finset.sum_product ];
          rw [ show ( Finset.filter ( fun x : R × Fin 2 => x.1 = r ) Finset.univ : Finset ( R × Fin 2 ) ) = Finset.image ( fun x : Fin 2 => ( r, x ) ) Finset.univ by ext ⟨ x, y ⟩ ; aesop ] ; simp +decide [ Finset.card_image_of_injective, Function.Injective ] ;
        rw [ Finset.card_filter ] at *;
        rw [ Finset.sum_image ] <;> aesop

/-
Definition of row_marked_count and lemma stating the sum of row counts equals total marked cells.
-/
def row_marked_count (k : ℕ) (Marked : Finset (Grid k)) (r : Fin (3 * k)) : ℕ :=
  (Marked.filter (fun p => p.2 = r)).card

lemma sum_row_marked_count (k : ℕ) (Marked : Finset (Grid k)) :
  Finset.univ.sum (row_marked_count k Marked) = Marked.card := by
    unfold row_marked_count;
    simp +decide only [card_eq_sum_ones, sum_filter];
    rw [ Finset.sum_comm ] ; aesop

/-
Definition of col_marked_count and lemma stating the sum of column counts equals total marked cells.
-/
def col_marked_count (k : ℕ) (Marked : Finset (Grid k)) (c : Fin (3 * k)) : ℕ :=
  (Marked.filter (fun p => p.1 = c)).card

lemma sum_col_marked_count (k : ℕ) (Marked : Finset (Grid k)) :
  Finset.univ.sum (col_marked_count k Marked) = Marked.card := by
    unfold col_marked_count;
    simp +decide only [card_eq_sum_ones, sum_filter];
    rw [ Finset.sum_comm ] ; aesop

/-
Definition of a 'good' set of rows (small number of marked cells) and proof of its existence.
-/
def is_good_row_set (k : ℕ) (Marked : Finset (Grid k)) (A : Finset (Fin (3 * k))) : Prop :=
  A.card = k ∧ (A.sum (row_marked_count k Marked)) ≤ k - 1

lemma exists_good_row_set (k : ℕ) (hk : k ≥ 1) (Marked : Finset (Grid k)) (hMarked : Marked.card = 3 * k - 1) :
  ∃ A, is_good_row_set k Marked A := by
    apply exists_small_sum_subset k hk;
    rw [ ← hMarked, sum_row_marked_count ]

/-
Definition of a 'good' set of columns and proof of its existence.
-/
def is_good_col_set (k : ℕ) (Marked : Finset (Grid k)) (B : Finset (Fin (3 * k))) : Prop :=
  B.card = k ∧ (B.sum (col_marked_count k Marked)) ≤ k - 1

lemma exists_good_col_set (k : ℕ) (hk : k ≥ 1) (Marked : Finset (Grid k)) (hMarked : Marked.card = 3 * k - 1) :
  ∃ B, is_good_col_set k Marked B := by
    apply exists_small_sum_subset k hk;
    rw [ ← hMarked, sum_col_marked_count ]

/-
Lemma stating that we can cover the columns in B_compl using rows in A, avoiding marked cells, if A is a good row set.
-/
lemma exists_block_I_matching (k : ℕ) (hk : k ≥ 1) (Marked : Finset (Grid k))
  (A : Finset (Fin (3 * k))) (B_compl : Finset (Fin (3 * k)))
  (hA : is_good_row_set k Marked A) (hB_compl : B_compl.card = 2 * k) :
  ∃ M1 : Finset (Grid k),
    M1 ⊆ B_compl ×ˢ A ∧
    (∀ p ∈ M1, p ∉ Marked) ∧
    (∀ c ∈ B_compl, ∃! r ∈ A, (c, r) ∈ M1) ∧
    (∀ r ∈ A, (M1.filter (fun p => p.2 = r)).card = 2) := by
      -- Let's consider the set of bad edges between $B_compl$ and $A$.
      set Bad := Marked.filter (fun p => p.1 ∈ B_compl ∧ p.2 ∈ A) with hBad_def;
      -- We apply `exists_double_covering_matching` to the types corresponding to `B_compl` and `A`.
      have h_bad_edges : Bad.card < A.card := by
        have h_double_covering : Finset.card Bad ≤ Finset.sum A (row_marked_count k Marked) := by
          have hBad_card_le : Bad ⊆ Finset.biUnion A (fun r => Marked.filter (fun p => p.2 = r)) := by
            intro p hp; aesop;
          exact le_trans ( Finset.card_le_card hBad_card_le ) ( Finset.card_biUnion_le );
        exact lt_of_le_of_lt h_double_covering ( by linarith [ hA.1, hA.2, Nat.sub_add_cancel ( by linarith : 1 ≤ k ) ] );
      -- We apply `exists_double_covering_matching` to the types corresponding to `B_compl` and `A`, with the bad edges defined as above.
      obtain ⟨M, hM⟩ : ∃ M : Finset (B_compl × A), (∀ p ∈ M, (p.1.val, p.2.val) ∉ Bad) ∧ (∀ c : B_compl, ∃! r : A, (c, r) ∈ M) ∧ (∀ r : A, (M.filter (fun p => p.2 = r)).card = 2) := by
        convert exists_double_covering_matching _ _ _;
        any_goals exact Finset.univ.filter fun p : B_compl × A => ( p.1.val, p.2.val ) ∈ Bad;
        all_goals try infer_instance;
        · aesop;
        · rw [ Fintype.card_coe, Fintype.card_coe ] ; linarith [ hA.1 ];
        · convert h_bad_edges using 1;
          · fapply Finset.card_bij;
            use fun p hp => ( p.1.val, p.2.val );
            · aesop;
            · grind;
            · aesop;
          · rw [ Fintype.card_coe ];
      use M.image (fun p => (p.1.val, p.2.val));
      simp +zetaDelta at *;
      refine' ⟨ _, _, _, _ ⟩;
      · exact Finset.image_subset_iff.mpr fun p hp => Finset.mem_product.mpr ⟨ p.1.2, p.2.2 ⟩;
      · aesop;
      · intro c hc; specialize hM; have := hM.2.1 c hc; cases' this with r hr; use r; aesop;
      · intro r hr; specialize hM; have := hM.2.2 r hr; simp_all +decide [ Finset.filter_image ] ;
        rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
        · convert hM.2.2 r hr using 2 ; ext ; aesop;
        · grind

/-
Lemma stating that we can cover the rows in A_compl using columns in B, avoiding marked cells, if B is a good col set.
-/
lemma exists_block_II_matching (k : ℕ) (hk : k ≥ 1) (Marked : Finset (Grid k))
  (B : Finset (Fin (3 * k))) (A_compl : Finset (Fin (3 * k)))
  (hB : is_good_col_set k Marked B) (hA_compl : A_compl.card = 2 * k) :
  ∃ M2 : Finset (Grid k),
    M2 ⊆ B ×ˢ A_compl ∧
    (∀ p ∈ M2, p ∉ Marked) ∧
    (∀ r ∈ A_compl, ∃! c ∈ B, (c, r) ∈ M2) ∧
    (∀ c ∈ B, (M2.filter (fun p => p.1 = c)).card = 2) := by
      -- Apply `exists_double_covering_matching` with `R = B` and `C = A_compl`.
      obtain ⟨M2, hM2⟩ : ∃ M2 : Finset (Fin (3 * k) × Fin (3 * k)),
          ((∀ p ∈ M2, p ∈ B ×ˢ A_compl) ∧ (∀ p ∈ M2, p ∉ Marked) ∧
            (∀ r ∈ A_compl, ∃! c ∈ B, (c, r) ∈ M2) ∧ (∀ c ∈ B, (M2.filter (fun p => p.1 = c)).card = 2)) := by
              have := exists_double_covering_matching ( show Fintype.card A_compl = 2 * Fintype.card B from ?_ );
              · specialize this ( Finset.filter ( fun p => ( p.2.val, p.1.val ) ∈ Marked ) ( Finset.univ : Finset ( { x : Fin ( 3 * k ) // x ∈ A_compl } × { x : Fin ( 3 * k ) // x ∈ B } ) ) ) ?_;
                · have h_bad_edges : Finset.card (Finset.filter (fun p : Fin (3 * k) × Fin (3 * k) => p ∈ Marked) (B ×ˢ A_compl)) ≤ k - 1 := by
                    have h_bad_edges : Finset.card (Finset.filter (fun p : Fin (3 * k) × Fin (3 * k) => p ∈ Marked) (B ×ˢ A_compl)) ≤ Finset.sum B (fun c => col_marked_count k Marked c) := by
                      have h_bad_edges : Finset.card (Finset.filter (fun p : Fin (3 * k) × Fin (3 * k) => p ∈ Marked) (B ×ˢ A_compl)) ≤ Finset.sum B (fun c => Finset.card (Finset.filter (fun p : Fin (3 * k) × Fin (3 * k) => p.1 = c ∧ p ∈ Marked) (B ×ˢ A_compl))) := by
                        rw [ ← Finset.card_biUnion ];
                        · exact Finset.card_le_card fun x hx => by aesop;
                        · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun p hp hp' => hxy <| by aesop;
                      refine le_trans h_bad_edges <| Finset.sum_le_sum fun c hc => ?_;
                      exact Finset.card_le_card fun x hx => by aesop;
                    exact h_bad_edges.trans hB.2;
                  convert h_bad_edges.trans_lt ( Nat.sub_lt hk zero_lt_one ) using 1;
                  · refine' Finset.card_bij ( fun p hp => ( p.2.val, p.1.val ) ) _ _ _ <;> simp +decide;
                    · aesop;
                    · tauto;
                  · rw [ Fintype.card_coe, hB.1 ];
                · obtain ⟨ M, hM₁, hM₂, hM₃ ⟩ := this;
                  use M.image ( fun p => ( p.2.val, p.1.val ) );
                  simp +zetaDelta at *;
                  refine' ⟨ _, _, _, _ ⟩;
                  · grind;
                  · grind;
                  · intro r hr; specialize hM₂ r hr; cases' hM₂ with c hc; use c; aesop;
                  · intro c hc; specialize hM₃ c hc; simp_all +decide [ Finset.filter_image ] ;
                    rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
                    · convert hM₃ using 2 ; ext ; aesop;
                    · aesop;
              · have := hB.1; aesop;
      exact ⟨ M2, hM2 ⟩

/-
The main theorem for part b: we can always avoid 3k-1 marked cells.
-/
theorem part_b_lower_bound (k : ℕ) (hk : k ≥ 1) : can_avoid_marked k (3 * k - 1) := by
  intro Marked hMarked_card;
  -- Use `exists_good_row_set` to find A. Let A_compl = univ \ A.
  obtain ⟨A, hA⟩ : ∃ A : Finset (Fin (3 * k)), is_good_row_set k Marked A := exists_good_row_set k hk Marked hMarked_card
  set A_compl := Finset.univ \ A with hA_compl_def
  have hA_compl_card : A_compl.card = 2 * k := by
    rw [ Finset.card_sdiff ] ; norm_num [ hA.1 ] ; omega;
  -- Use `exists_good_col_set` to find B. Let B_compl = univ \ B.
  obtain ⟨B, hB⟩ : ∃ B : Finset (Fin (3 * k)), is_good_col_set k Marked B := exists_good_col_set k hk Marked hMarked_card
  set B_compl := Finset.univ \ B with hB_compl_def
  have hB_compl_card : B_compl.card = 2 * k := by
    simp_all +decide [ Finset.card_sdiff ];
    exact Nat.sub_eq_of_eq_add <| by linarith [ hB.1, Nat.sub_add_cancel <| show 1 ≤ 3 * k from by linarith ] ;
  -- Use `exists_block_I_matching` to find M1.
  obtain ⟨M1, hM1⟩ : ∃ M1 : Finset (Grid k),
    M1 ⊆ B_compl ×ˢ A ∧
    (∀ p ∈ M1, p∉ Marked) ∧
    (∀ c ∈ B_compl, ∃! r ∈ A, (c, r) ∈ M1) ∧
    (∀ r ∈ A, (M1.filter (fun p => p.2 = r)).card = 2) := exists_block_I_matching k hk Marked A B_compl hA hB_compl_card;
  -- Use `exists_block_II_matching` to find M2.
  obtain ⟨M2, hM2⟩ : ∃ M2 : Finset (Grid k), M2 ⊆ B ×ˢ A_compl ∧ (∀ p ∈ M2, p ∉ Marked) ∧ (∀ r ∈ A_compl, ∃! c ∈ B, (c, r) ∈ M2) ∧ (∀ c ∈ B, (M2.filter (fun p => p.1 = c)).card = 2) := by
    convert exists_block_II_matching k hk Marked B A_compl hB hA_compl_card using 1;
  refine' ⟨ M1 ∪ M2, _, _, _ ⟩;
  · rw [ Finset.card_union_of_disjoint ];
    · have hM1_card : M1.card = 2 * k := by
        have hM1_card : M1.card = ∑ r ∈ A, (M1.filter (fun p => p.2 = r)).card := by
          rw [ ← Finset.card_eq_sum_card_fiberwise ];
          exact fun x hx => Finset.mem_product.mp ( hM1.1 hx ) |>.2;
        rw [ hM1_card, Finset.sum_congr rfl fun x hx => hM1.2.2.2 x hx ] ; simp +decide [ mul_comm, hA.1 ]
      have hM2_card : M2.card = 2 * k := by
        have hM2_card : M2.card = ∑ c ∈ B, (M2.filter (fun p => p.1 = c)).card := by
          rw [ ← Finset.card_eq_sum_card_fiberwise ];
          exact fun x hx => Finset.mem_product.mp ( hM2.1 hx ) |>.1;
        rw [ hM2_card, Finset.sum_congr rfl hM2.2.2.2 ] ; simp +decide [ mul_comm, hB.1 ]
      linarith;
    · rw [ Finset.disjoint_left ];
      intro p hp1 hp2; have := hM1.1 hp1; have := hM2.1 hp2; simp_all +decide [ Finset.mem_product ] ;
      rw [ Finset.mem_product ] at * ; aesop;
  · refine' ⟨ _, _, _ ⟩;
    · intro r;
      by_cases hr : r ∈ A_compl;
      · exact ExistsUnique.exists ( hM2.2.2.1 r hr ) |> fun ⟨ c, hc ⟩ => ⟨ c, Finset.mem_union_right _ <| by aesop ⟩;
      · simp +zetaDelta at *;
        have := hM1.2.2.2 r hr; obtain ⟨ c, hc ⟩ := Finset.card_pos.mp ( by linarith ) ; aesop;
    · intro c; by_cases hc : c ∈ B_compl <;> simp_all +decide [ Finset.subset_iff ] ;
      · exact ExistsUnique.exists ( hM1.2.2.1 c hc ) |> fun ⟨ r, hr ⟩ => ⟨ r, Or.inl hr.2 ⟩;
      · have := hM2.2.2.2 c hc;
        obtain ⟨ p, hp ⟩ := Finset.card_pos.mp ( by linarith ) ; use p.2; aesop;
    · intro p hp
      by_cases hp1 : p ∈ M1;
      · have := hM1.2.2.2 p.2 ( hM1.1 hp1 |> Finset.mem_product.mp |> And.right );
        obtain ⟨ q, hq ⟩ := Finset.exists_mem_ne ( by linarith ) p; use q; aesop;
      · -- Since $p \in M2$, we know that $p.1 \in B$ and $p.2 \in A_compl$.
        obtain ⟨hp1B, hp2A_compl⟩ : p.1 ∈ B ∧ p.2 ∈ A_compl := by
          exact Finset.mem_product.mp ( hM2.1 ( Finset.mem_union.mp hp |> Or.resolve_left <| hp1 ) );
        obtain ⟨ q, hq ⟩ := Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.filter ( fun q => q.1 = p.1 ) M2 ) from by linarith [ hM2.2.2.2 p.1 hp1B ] ) p;
        exact ⟨ q, Finset.mem_union_right _ ( Finset.mem_filter.mp hq.1 |>.1 ), hq.2, Or.inl ( Finset.mem_filter.mp hq.1 |>.2 ) ⟩;
  · rw [ Finset.disjoint_left ] ; aesop

/-
Definitions for Block I and Block II properties.
-/
def is_block_I (k : ℕ) (M1 : Finset (Grid k)) (A : Finset (Fin (3 * k))) (B_compl : Finset (Fin (3 * k))) : Prop :=
  M1 ⊆ B_compl ×ˢ A ∧
  (∀ c ∈ B_compl, ∃! r ∈ A, (c, r) ∈ M1) ∧
  (∀ r ∈ A, (M1.filter (fun p => p.2 = r)).card = 2)

def is_block_II (k : ℕ) (M2 : Finset (Grid k)) (B : Finset (Fin (3 * k))) (A_compl : Finset (Fin (3 * k))) : Prop :=
  M2 ⊆ B ×ˢ A_compl ∧
  (∀ r ∈ A_compl, ∃! c ∈ B, (c, r) ∈ M2) ∧
  (∀ c ∈ B, (M2.filter (fun p => p.1 = c)).card = 2)

/-
Lemma: If M1 and M2 satisfy the block properties, their union is a valid placement of size 4k.
-/
lemma valid_placement_from_blocks (k : ℕ) (hk : k ≥ 1)
  (A : Finset (Fin (3 * k))) (B : Finset (Fin (3 * k)))
  (M1 M2 : Finset (Grid k))
  (hA_card : A.card = k)
  (hB_card : B.card = k)
  (hM1 : is_block_I k M1 A (Finset.univ \ B))
  (hM2 : is_block_II k M2 B (Finset.univ \ A)) :
  (M1 ∪ M2).card = 4 * k ∧ is_valid_placement k (M1 ∪ M2) ∧ Disjoint M1 M2 := by
    -- We'll use the fact that if the conditions hold, then the union of $M1$ and $M2$ is a valid placement.
    have h_union_valid : is_valid_placement k (M1 ∪ M2) := by
      constructor;
      · intro r;
        by_cases hr : r ∈ A;
        · have := hM1.2.2 r hr;
          obtain ⟨ p, hp ⟩ := Finset.card_pos.mp ( by linarith ) ; use p.1; aesop;
        · have := hM2.2.1 r ( Finset.mem_sdiff.mpr ⟨ Finset.mem_univ _, hr ⟩ );
          exact ⟨ this.exists.choose, Finset.mem_union_right _ this.exists.choose_spec.2 ⟩;
      · constructor;
        · intro c;
          by_cases hc : c ∈ B <;> simp_all +decide [ is_block_I, is_block_II ];
          · have := hM2.2.2 c hc; obtain ⟨ p, hp ⟩ := Finset.card_pos.mp ( by linarith ) ; aesop;
          · exact ExistsUnique.exists ( hM1.2.1 c hc ) |> fun ⟨ r, hr ⟩ => ⟨ r, Or.inl hr.2 ⟩;
        · intro p hp;
          cases Finset.mem_union.mp hp <;> simp_all +decide [ is_block_I, is_block_II ];
          · have := hM1.2.2 p.2 ( Finset.mem_product.mp ( hM1.1 ‹_› ) |>.2 );
            obtain ⟨ q, hq ⟩ := Finset.exists_mem_ne ( by linarith ) p; use q; aesop;
          · have := hM2.2.2 p.1 ( Finset.mem_product.mp ( hM2.1 ‹_› ) |>.1 );
            obtain ⟨ q, hq ⟩ := Finset.exists_mem_ne ( by linarith ) p; use q; aesop;
    have h_card : M1.card = 2 * k ∧ M2.card = 2 * k := by
      unfold is_block_I is_block_II at *;
      have h_card_M1 : M1.card = ∑ r ∈ A, (M1.filter (fun p => p.2 = r)).card := by
        rw [ ← Finset.card_eq_sum_card_fiberwise ];
        exact fun x hx => Finset.mem_product.mp ( hM1.1 hx ) |>.2
      have h_card_M2 : M2.card = ∑ c ∈ B, (M2.filter (fun p => p.1 = c)).card := by
        rw [ ← Finset.card_eq_sum_card_fiberwise ];
        exact fun x hx => Finset.mem_product.mp ( hM2.1 hx ) |>.1;
      simp_all +decide [ mul_comm ];
    have h_disjoint : M1 ∩ M2 = ∅ := by
      ext ⟨c, r⟩
      simp [hM1, hM2];
      intro hc hr; have := hM1.1 hc; have := hM2.1 hr; simp_all +decide [ Finset.subset_iff ] ;
      rw [ Finset.mem_product ] at * ; aesop;
    simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ] ; omega
