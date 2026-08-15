import Mathlib

open Set Real Metric

/-- Parameters for Schmidt's (α, β)-game on a metric space. -/
structure SchmidtParams where
  α : ℝ
  β : ℝ
  hα_pos : 0 < α
  hα_lt  : α < 1
  hβ_pos : 0 < β
  hβ_lt  : β < 1

variable {X : Type*} [MetricSpace X]

/-- A move in Schmidt's game consists of a center point in space X and a positive radius. -/
structure GameBall (X : Type*) [MetricSpace X] where
  center : X
  radius : ℝ
  r_pos  : 0 < radius

/-- Convert a GameBall object into an actual set of points in the metric space. -/
def GameBall.toSet (b : GameBall X) : Set X :=
  Metric.closedBall b.center b.radius

/-- Ball inclusion proposition: b2 is completely contained in b1 -/
def IsSubBall (b2 b1 : GameBall X) : Prop :=
  b2.toSet ⊆ b1.toSet

/-- Alice's Move Rule: Given Bob's ball B, Alice must choose A such that:
    1. A ⊆ B (Inclusion constraint)
    2. radius(A) = α * radius(B) (Scaling constraint) -/
structure AliceMove (params : SchmidtParams) (B : GameBall X) where
  A : GameBall X
  sub : IsSubBall A B
  r_eq : A.radius = params.α * B.radius

/-- Bob's Move Rule: Given Alice's ball A, Bob must choose B' such that:
    1. B' ⊆ A (Inclusion constraint)
    2. radius(B') = β * radius(A) (Scaling constraint) -/
structure BobMove (params : SchmidtParams) (A : GameBall X) where
  B' : GameBall X
  sub : IsSubBall B' A
  r_eq : B'.radius = params.β * A.radius

/-- A strategy for Alice is a function that provides a valid AliceMove
    for any possible ball B chosen by Bob. -/
def AliceStrategy (params : SchmidtParams) :=
  (n : ℕ) → (B : GameBall X) → AliceMove params B

/-- A sequence of Bob's balls constitutes a valid play against Alice's strategy if
    every subsequent ball B_{n+1} is a valid BobMove inside Alice's response to B_n. -/
def isValidPlay {X : Type*} [MetricSpace X] (params : SchmidtParams) (fA : AliceStrategy (X := X) params)
    (B_seq : ℕ → GameBall X) : Prop :=
  ∀ n, ∃ (moveB : BobMove params (fA n (B_seq n)).A), moveB.B' = B_seq (n + 1)

/-- Alice's strategy is winning if every valid sequence of plays against it
    results in the limit point being in the target set S. -/
def isWinningStrategy {X : Type*} [MetricSpace X] (params : SchmidtParams) (S : Set X)
    (fA : AliceStrategy (X := X) params) : Prop :=
  ∀ (B_seq : ℕ → GameBall X),
    isValidPlay params fA B_seq →
    ∀ (x : X), (∀ n, x ∈ (B_seq n).toSet) → x ∈ S

/-- A target set S is winning if Alice possesses a winning strategy for it. -/
def IsWinningSet (params : SchmidtParams) (S : Set X) : Prop :=
  ∃ fA : AliceStrategy (X := X) params, isWinningStrategy params S fA

def IsAlphaWinning (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1) (S : Set X) : Prop :=
  ∀ (β : ℝ) (hβ_pos : 0 < β) (hβ_lt : β < 1),
    IsWinningSet ⟨α, β, hα_pos, hα_lt, hβ_pos, hβ_lt⟩ S

/-- The set of all valid α values for which S is α-winning. -/
def winningAlphas (S : Set X) : Set ℝ :=
  { α | ∃ (hα_pos : 0 < α) (hα_lt : α < 1), IsAlphaWinning α hα_pos hα_lt S }

/-- The winning dimension of a set S is the supremum of its winning α values. -/
noncomputable def windim (S : Set X) : ℝ :=
  sSup (winningAlphas S)

/-! 1. Digit Expansion and Target Set S_g -/

noncomputable def alpha_g (g : ℕ) : ℝ :=
  1 / (((g : ℝ) - 1)^2 + 1)

noncomputable def I_int (g : ℕ) (k : ℕ) (n : ℤ) : Set ℝ :=
  Set.Icc 
    ((n : ℝ) / (g : ℝ)^k) 
    ((n : ℝ) / (g : ℝ)^k + 1 / (((g : ℝ) - 1) * (g : ℝ)^k))

noncomputable def K (g : ℕ) (k : ℕ) : Set ℝ :=
  ⋃ (n : ℤ), I_int g k n

/-- The k-th base-g digit after the radix point of a real number x (1-indexed). -/
noncomputable def baseDigit (g : ℕ) (k : ℕ) (x : ℝ) : ℤ :=
  ⌊x * (g : ℝ)^k⌋ - (g : ℤ) * ⌊x * (g : ℝ)^(k - 1)⌋

/-- S_g is the set of real numbers having infinitely many zeros in their base-g expansion. -/
def S_g (g : ℕ) : Set ℝ :=
  { x : ℝ | ∀ N : ℕ, ∃ k : ℕ, k ≥ N ∧ baseDigit g k x = 0 }

/-! 2. Algebraic Identities for α_g and Gap Sizing -/

lemma g_real_gt_two (g : ℕ) (hg : 2 < g) : 2 < (g : ℝ) := by
  exact_mod_cast hg

lemma g_minus_one_pos (g : ℕ) (hg : 2 < g) : 0 < (g : ℝ) - 1 := by
  have : 2 < (g : ℝ) := g_real_gt_two g hg
  linarith

lemma g_minus_two_pos (g : ℕ) (hg : 2 < g) : 0 < (g : ℝ) - 2 := by
  have : 2 < (g : ℝ) := g_real_gt_two g hg
  linarith

lemma alpha_g_pos (g : ℕ) : 0 < alpha_g g := by
  unfold alpha_g
  have : 0 < ((g : ℝ) - 1)^2 + 1 := by positivity
  positivity

lemma alpha_g_lt_one (g : ℕ) (hg : 2 < g) : alpha_g g < 1 := by
  unfold alpha_g
  have hg_real : 2 < (g : ℝ) := g_real_gt_two g hg
  have h : 1 < ((g : ℝ) - 1)^2 + 1 := by nlinarith
  exact (div_lt_one₀ (by positivity)).mpr h

/-- Key identity: 1/2 - α_g = (1/2) * g * (g - 2) * α_g -/
lemma half_sub_alpha_g (g : ℕ) :
    (1 : ℝ) / 2 - alpha_g g = (1 / 2) * (g : ℝ) * ((g : ℝ) - 2) * alpha_g g := by
  unfold alpha_g
  have h_denom_pos : 0 < ((g : ℝ) - 1)^2 + 1 := by positivity
  have h_denom_ne : ((g : ℝ) - 1)^2 + 1 ≠ 0 := ne_of_gt h_denom_pos
  apply mul_right_cancel₀ h_denom_ne
  field_simp
  ring

/-! 3. Interval Length and Scale Choice -/

lemma exists_k_scale (g : ℕ) (hg : 2 < g) (L : ℝ) (hL_pos : 0 < L)
    (hL_ub : L ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ)))) :
    ∃ (k : ℕ) (_hk : 1 ≤ k),
      1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(k + 1)) < L ∧
      L ≤ 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^k) := by
  have hg_gt1 : 1 < (g : ℝ) := by
    have := g_real_gt_two g hg; linarith
  have h_scale1 : alpha_g g * ((g : ℝ)^2 - (g : ℝ)) = alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^1 := by
    ring
  have hL_ub' : L ≤ 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^1) := by
    rwa [← h_scale1]
  have h_tendsto : Filter.Tendsto (fun k : ℕ => 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^k))
      Filter.atTop (nhds 0) := by
    have h_coeff : 0 < alpha_g g * ((g : ℝ) - 1) := by
      have := alpha_g_pos g
      have := g_minus_one_pos g hg
      positivity
    simp_rw [one_div]
    exact tendsto_inv_atTop_zero.comp
      (Filter.Tendsto.const_mul_atTop h_coeff (tendsto_pow_atTop_atTop_of_one_lt hg_gt1))
  
  have h_ev := h_tendsto (isOpen_Iio.mem_nhds hL_pos)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h_ev
  have h_ex : ∃ n : ℕ, 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(n + 1)) < L :=
    ⟨N, hN (N + 1) (by omega)⟩

  classical
  let k := Nat.find h_ex
  have hk_spec : 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(k + 1)) < L :=
    Nat.find_spec h_ex
  have hk_min : ∀ m < k, ¬ (1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(m + 1)) < L) :=
    fun m hm => Nat.find_min h_ex hm

  have hk_pos : 1 ≤ k := by
    by_contra! h_lt
    have hk0 : k = 0 := by omega
    have h_spec0 := hk_spec
    rw [hk0] at h_spec0
    have : (0 + 1 : ℕ) = 1 := rfl
    rw [this] at h_spec0
    linarith

  have hk_ub : L ≤ 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^k) := by
    have h_lt : k - 1 < k := by omega
    have h_not := hk_min (k - 1) h_lt
    have h_sub : (k - 1) + 1 = k := Nat.sub_add_cancel hk_pos
    rw [h_sub] at h_not
    linarith

  exact ⟨k, hk_pos, hk_spec, hk_ub⟩

/-! 4. Inclusion into K_k and Lemma 16 -/

lemma I_int_subset_K (g : ℕ) (k : ℕ) (n : ℤ) :
    I_int g k n ⊆ K g k := by
  unfold K
  exact Set.subset_iUnion (fun i => I_int g k i) n

theorem schmidt_lemma_16 (g : ℕ) (hg : 2 < g) (a b : ℝ) (hab : a < b)
    (h_len : b - a ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ)))) :
    ∃ (k : ℕ) (_hk : 1 ≤ k) (c d : ℝ) (_hcd : c < d),
      Set.Icc c d ⊆ Set.Icc a b ∧
      d - c = alpha_g g * (b - a) ∧
      Set.Icc c d ⊆ K g k := by
  set L := b - a
  have hL_pos : 0 < L := sub_pos.mpr hab
  obtain ⟨k, hk, h_lower, h_upper⟩ := exists_k_scale g hg L hL_pos h_len
  
  set α := alpha_g g
  have hα_pos : 0 < α := alpha_g_pos g
  set period := 1 / (g : ℝ)^k
  set w := 1 / (((g : ℝ) - 1) * (g : ℝ)^k)
  set gap := ((g : ℝ) - 2) / (((g : ℝ) - 1) * (g : ℝ)^k)
  set m := (a + b) / 2
  
  have h_overlap : ∃ (n : ℤ) (c : ℝ),
      a ≤ c ∧ c + α * L ≤ b ∧ Set.Icc c (c + α * L) ⊆ I_int g k n := by
    have h_min_bound : α * L ≤ min ((1 / 2) * L - (1 / 2) * gap) w := by
      apply le_min
      · have h_id := half_sub_alpha_g g
        have h_gap_eq : (1 / 2) * gap =
            ((1 / 2) * (g : ℝ) * ((g : ℝ) - 2) * α) *
            (1 / (α * ((g : ℝ) - 1) * (g : ℝ)^(k + 1))) := by
          dsimp [gap, α]
          have hg_ne : (g : ℝ) ≠ 0 := by positivity
          have hgm1_ne : (g : ℝ) - 1 ≠ 0 := ne_of_gt (g_minus_one_pos g hg)
          have hgk_ne : (g : ℝ)^k ≠ 0 := by positivity
          have hα_ne : alpha_g g ≠ 0 := ne_of_gt (alpha_g_pos g)
          have h_pow : (g : ℝ)^(k + 1) = (g : ℝ)^k * (g : ℝ) := by rw [pow_succ]
          rw [h_pow]
          field_simp
        have h_factor_pos : 0 ≤ (1 / 2) * (g : ℝ) * ((g : ℝ) - 2) * α := by
          have : 0 < (g : ℝ) - 2 := g_minus_two_pos g hg
          positivity
        have h_gap_le : (1 / 2) * gap ≤ ((1 / 2) * (g : ℝ) * ((g : ℝ) - 2) * α) * L := by
          rw [h_gap_eq]
          exact mul_le_mul_of_nonneg_left (le_of_lt h_lower) h_factor_pos
        rw [ ← h_id] at h_gap_le
        linarith
      · have h_w_eq : 1 / (α * ((g : ℝ) - 1) * (g : ℝ)^k) = w / α := by
          dsimp [w]
          have hα_ne : α ≠ 0 := ne_of_gt hα_pos
          have hgm1_ne : (g : ℝ) - 1 ≠ 0 := ne_of_gt (g_minus_one_pos g hg)
          have hgk_ne : (g : ℝ)^k ≠ 0 := by positivity
          field_simp
        have h_bound : L ≤ w / α := by
          rwa [h_w_eq] at h_upper
        have h_mul := (le_div_iff₀ hα_pos).mp h_bound
        linarith

    have ⟨h_min1, h_min2⟩ := le_min_iff.mp h_min_bound
    have h_period_pos : 0 < period := by dsimp [period]; positivity
    have h_gap_nonneg : 0 ≤ gap := by
      dsimp [gap]
      have : 0 < (g : ℝ) - 2 := g_minus_two_pos g hg
      have : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
      positivity
    have h_w_gap : w + gap = period := by
      dsimp [w, gap, period]
      have hgm1_ne : (g : ℝ) - 1 ≠ 0 := ne_of_gt (g_minus_one_pos g hg)
      have hgk_ne : (g : ℝ)^k ≠ 0 := by positivity
      field_simp
      ring
    have ha_eq : a = m - (1 / 2) * L := by dsimp [m, L]; ring
    have hb_eq : b = m + (1 / 2) * L := by dsimp [m, L]; ring
    have h_alpha_L_le_L : α * L ≤ L := by
      have : α < 1 := alpha_g_lt_one g hg
      nlinarith

    set y := m / period
    set n := ⌊y⌋
    have hn_le_y : (n : ℝ) ≤ y := Int.floor_le y
    have hn_le : (n : ℝ) * period ≤ m := (le_div_iff₀ h_period_pos).mp hn_le_y
    have hy_lt_n1 : y < (n : ℝ) + 1 := Int.lt_floor_add_one y
    have h_lt_n1 : m < ((n : ℝ) + 1) * period := (div_lt_iff₀ h_period_pos).mp hy_lt_n1
    have h_xn_period : (n : ℝ) / (g : ℝ)^k = (n : ℝ) * period := by
      dsimp [period]; ring

    by_cases h_case : m ≤ (n : ℝ) * period + w + (1 / 2) * gap
    · set c := max a ((n : ℝ) * period)
      have hac : a ≤ c := le_max_left a _
      have hnc : (n : ℝ) * period ≤ c := le_max_right a _
      have hc_le_b : c ≤ b - α * L :=
        max_le (by linarith) (by linarith [h_min1, hn_le, hb_eq, h_gap_nonneg])
      have hcb : c + α * L ≤ b := by linarith
      have hc_le_w : c ≤ (n : ℝ) * period + w - α * L :=
        max_le (by linarith [h_min1, h_case, ha_eq]) (by linarith [h_min2])
      have h_sub : Set.Icc c (c + α * L) ⊆ I_int g k n := by
        unfold I_int
        rw [h_xn_period]
        exact Set.Icc_subset_Icc hnc (by linarith)
      exact ⟨n, c, hac, hcb, h_sub⟩
    · have h_case2 : (n : ℝ) * period + w + (1 / 2) * gap < m := by linarith
      have hn1_period : ((n + 1 : ℤ) : ℝ) * period = (n : ℝ) * period + w + gap := by
        push_cast
        rw [← h_w_gap]
        ring
      have hn1_period_div : ((n + 1 : ℤ) : ℝ) / (g : ℝ)^k = ((n + 1 : ℤ) : ℝ) * period := by
        dsimp [period]; ring
      have h_lt_n1' : m < ((n + 1 : ℤ) : ℝ) * period := by
        push_cast; exact h_lt_n1
      set c := max a (((n + 1 : ℤ) : ℝ) * period)
      have hac : a ≤ c := le_max_left a _
      have hnc : ((n + 1 : ℤ) : ℝ) * period ≤ c := le_max_right a _
      have hc_le_b : c ≤ b - α * L :=
        max_le (by linarith) (by linarith [hn1_period, h_case2, hb_eq, h_min1])
      have hcb : c + α * L ≤ b := by linarith
      have hc_le_w : c ≤ ((n + 1 : ℤ) : ℝ) * period + w - α * L :=
        max_le (by linarith [h_alpha_L_le_L, hL_pos, ha_eq, h_lt_n1', h_min2]) (by linarith [h_min2])
      have h_sub : Set.Icc c (c + α * L) ⊆ I_int g k (n + 1) := by
        unfold I_int
        rw [hn1_period_div]
        exact Set.Icc_subset_Icc hnc (by linarith)
      exact ⟨n + 1, c, hac, hcb, h_sub⟩

  obtain ⟨n, c, hac, hdb, h_sub⟩ := h_overlap
  refine ⟨k, hk, c, c + α * L, ?_, ?_, ?_, ?_⟩
  · linarith [mul_pos hα_pos hL_pos]
  · exact Set.Icc_subset_Icc hac hdb
  · ring
  · exact Set.Subset.trans h_sub (I_int_subset_K g k n)

/-! 5. Geometric Bridge: GameBall ℝ to Closed Intervals -/

lemma gameBall_toSet_real (B : GameBall ℝ) :
    B.toSet = Set.Icc (B.center - B.radius) (B.center + B.radius) := by
  ext x
  simp only [GameBall.toSet, Metric.mem_closedBall, Real.dist_eq]
  rw [abs_le]
  constructor
  · intro h; constructor <;> linarith
  · intro ⟨h1, h2⟩; constructor <;> linarith

lemma gameBall_length (B : GameBall ℝ) :
    (B.center + B.radius) - (B.center - B.radius) = 2 * B.radius := by
  ring

/-- Constructing a GameBall ℝ from interval endpoints [a, b]. -/
noncomputable def gameBallOfIcc (a b : ℝ) (hab : a < b) : GameBall ℝ where
  center := (a + b) / 2
  radius := (b - a) / 2
  r_pos  := by linarith

lemma gameBallOfIcc_toSet (a b : ℝ) (hab : a < b) :
    (gameBallOfIcc a b hab).toSet = Set.Icc a b := by
  rw [gameBall_toSet_real]
  dsimp [gameBallOfIcc]
  have h1 : (a + b) / 2 - (b - a) / 2 = a := by ring
  have h2 : (a + b) / 2 + (b - a) / 2 = b := by ring
  rw [h1, h2]

/-! 6. Digit-Forcing Property of the Interior of I_k(n) -/

/-- Interior of the interval I_k(n). -/
def I_int_interior (g : ℕ) (k : ℕ) (n : ℤ) : Set ℝ :=
  Set.Ioo 
    ((n : ℝ) / (g : ℝ)^k) 
    ((n : ℝ) / (g : ℝ)^k + 1 / (((g : ℝ) - 1) * (g : ℝ)^k))

/-- Points strictly in the interior of I_k(n) must have at least one zero digit 
    at or beyond position k + 1. -/
lemma zero_digit_of_mem_interior (g : ℕ) (hg : 2 < g) (k : ℕ) (n : ℤ) {x : ℝ}
    (hx : x ∈ I_int_interior g k n) :
    ∃ (m : ℕ), m ≥ k + 1 ∧ baseDigit g m x = 0 := by
  sorry

/-- Compact sub-intervals of the interior guarantee a zero digit within a bounded range. -/
lemma zero_digit_of_compact_interior (g : ℕ) (hg : 2 < g) (k : ℕ) (n : ℤ) (c d : ℝ)
    (hcd : Set.Icc c d ⊆ I_int_interior g k n) (h_nonempty : c < d) :
    ∃ (m_bound : ℕ), ∀ x ∈ Set.Icc c d, ∃ m : ℕ, k + 1 ≤ m ∧ m ≤ m_bound ∧ baseDigit g m x = 0 := by
  sorry

/-! 7. Alice's Inductive Response: Schmidt's Lemma 16 Step -/

/-- Given Bob's ball B of sufficiently small radius, Alice can choose a sub-ball A ⊆ B 
    of radius α_g * r(B) entirely contained in K_k. -/
lemma alice_move_from_lemma_16 (g : ℕ) (hg : 2 < g) (params : SchmidtParams)
    (hα_eq : params.α = alpha_g g) (B : GameBall ℝ)
    (hB_radius : 2 * B.radius ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ)))) :
    ∃ (k : ℕ) (hk : 1 ≤ k) (A : GameBall ℝ),
      A.toSet ⊆ B.toSet ∧
      A.radius = params.α * B.radius ∧
      A.toSet ⊆ K g k := by
  set a := B.center - B.radius
  set b := B.center + B.radius
  have hab : a < b := by
    have := B.r_pos
    linarith
  have h_len : b - a ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ))) := by
    rw [gameBall_length]
    exact hB_radius
  obtain ⟨k, hk, c, d, hcd, h_sub, h_len_eq, h_K⟩ := schmidt_lemma_16 g hg a b hab h_len
  have h_rad : (d - c) / 2 = params.α * B.radius := by
    rw [h_len_eq, hα_eq, gameBall_length]
    ring
  set A := gameBallOfIcc c d hcd
  refine ⟨k, hk, A, ?_, ?_, ?_⟩
  · rw [gameBallOfIcc_toSet, gameBall_toSet_real]
    exact h_sub
  · dsimp [A, gameBallOfIcc]
    exact h_rad
  · rw [gameBallOfIcc_toSet]
    exact h_K

/-! 8. Theorem 5: S_g Winning Strategy & Winning Dimension -/

theorem schmidt_theorem_5_winning (g : ℕ) (hg : 2 < g) :
    IsAlphaWinning (alpha_g g) (alpha_g_pos g) (alpha_g_lt_one g hg) (S_g g) := by
  intro β hβ_pos hβ_lt
  sorry

/-- For α > α_g, choosing β = α⁻¹ * g^(-m) allows Bob to force every point 
    in the game intersection to avoid zero digits. -/
theorem schmidt_theorem_5_losing (g : ℕ) (hg : 2 < g) (α : ℝ) (hα_gt : alpha_g g < α)
    (hα_lt : α < 1) :
    ¬ IsAlphaWinning α (by linarith [alpha_g_pos g]) hα_lt (S_g g) := by
  intro h_win
  sorry

/-- Full Theorem 5: The winning dimension of S_g equals α_g = ((g - 1)² + 1)⁻¹. -/
theorem schmidt_theorem_5_windim (g : ℕ) (hg : 2 < g) :
    windim (S_g g) = alpha_g g := by
  unfold windim
  apply le_antisymm
  · -- Upper bound: no α > α_g is in winningAlphas (S_g g)
    apply csSup_le
    · refine ⟨alpha_g g, ?_⟩
      exact ⟨alpha_g_pos g, alpha_g_lt_one g hg, schmidt_theorem_5_winning g hg⟩
    · rintro α ⟨hα_pos, hα_lt, hα_win⟩
      by_contra! h_gt
      exact (schmidt_theorem_5_losing g hg α h_gt hα_lt) hα_win
  · -- Lower bound: α_g is a winning parameter
    apply le_csSup
    · -- winningAlphas is bounded above by 1
      refine ⟨1, ?_⟩
      rintro a ⟨ha_pos, ha_lt, -⟩
      exact le_of_lt ha_lt
    · exact ⟨alpha_g_pos g, alpha_g_lt_one g hg, schmidt_theorem_5_winning g hg⟩
