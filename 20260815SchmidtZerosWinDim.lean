import Mathlib

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

-- A sequence of Bob's balls constitutes a valid play against Alice's strategy if
--    every subsequent ball B_{n+1} is a valid BobMove inside Alice's response to B_n. -/
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

/-- The winning dimension of a set S is the supremum of its winning α values. 
    By definition in Mathlib, sSup ∅ = 0, which perfectly matches Schmidt's edge case. -/
noncomputable def windim (S : Set X) : ℝ :=
  sSup (winningAlphas S)

/-! 1. Parameter Definitions and Structural Setup -/

noncomputable def alpha_g (g : ℕ) : ℝ :=
  1 / (((g : ℝ) - 1)^2 + 1)

noncomputable def I_int (g : ℕ) (k : ℕ) (n : ℤ) : Set ℝ :=
  Set.Icc 
    ((n : ℝ) / (g : ℝ)^k) 
    ((n : ℝ) / (g : ℝ)^k + 1 / (((g : ℝ) - 1) * (g : ℝ)^k))

noncomputable def K (g : ℕ) (k : ℕ) : Set ℝ :=
  ⋃ (n : ℤ), I_int g k n

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
  
  -- 1. Extract an index where the sequence drops below L
  have h_ev := h_tendsto (isOpen_Iio.mem_nhds hL_pos)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h_ev
  have h_ex : ∃ n : ℕ, 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(n + 1)) < L :=
    ⟨N, hN (N + 1) (by omega)⟩

  -- 2. Pick the minimal such index k
  classical
  let k := Nat.find h_ex
  have hk_spec : 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(k + 1)) < L :=
    Nat.find_spec h_ex
  have hk_min : ∀ m < k, ¬ (1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(m + 1)) < L) :=
    fun m hm => Nat.find_min h_ex hm

  -- 3. Show 1 ≤ k (k = 0 contradicts hL_ub')
  have hk_pos : 1 ≤ k := by
    by_contra! h_lt
    have hk0 : k = 0 := by omega
    have h_spec0 := hk_spec
    rw [hk0] at h_spec0
    have : (0 + 1 : ℕ) = 1 := rfl
    rw [this] at h_spec0
    linarith

  -- 4. Show L ≤ f(k) by minimality at k - 1
  have hk_ub : L ≤ 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^k) := by
    have h_lt : k - 1 < k := by omega
    have h_not := hk_min (k - 1) h_lt
    have h_sub : (k - 1) + 1 = k := Nat.sub_add_cancel hk_pos
    rw [h_sub] at h_not
    linarith

  exact ⟨k, hk_pos, hk_spec, hk_ub⟩

/-! 4. Inclusion into K_k -/

lemma I_int_subset_K (g : ℕ) (k : ℕ) (n : ℤ) :
    I_int g k n ⊆ K g k := by
  unfold K
  exact Set.subset_iUnion (fun i => I_int g k i) n

lemma subinterval_in_Icc {c d a b : ℝ} (_hcd : c < d) (hac : a ≤ c) (hdb : d ≤ b) :
    Set.Icc c d ⊆ Set.Icc a b :=
  Set.Icc_subset_Icc hac hdb

/-! 5. Proof of Lemma 16 -/

theorem schmidt_lemma_16 (g : ℕ) (hg : 2 < g) (a b : ℝ) (hab : a < b)
    (h_len : b - a ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ)))) :
    ∃ (k : ℕ) (hk : 1 ≤ k) (c d : ℝ) (hcd : c < d),
      Set.Icc c d ⊆ Set.Icc a b ∧
      d - c = alpha_g g * (b - a) ∧
      Set.Icc c d ⊆ K g k := by
  set L := b - a
  have hL_pos : 0 < L := sub_pos.mpr hab
  
  -- Obtain scale k ≥ 1 satisfying equation (20)
  obtain ⟨k, hk, h_lower, h_upper⟩ := exists_k_scale g hg L hL_pos h_len
  
  set α := alpha_g g
  have hα_pos : 0 < α := alpha_g_pos g
  set period := 1 / (g : ℝ)^k
  set w := 1 / (((g : ℝ) - 1) * (g : ℝ)^k)
  set gap := ((g : ℝ) - 2) / (((g : ℝ) - 1) * (g : ℝ)^k)
  set m := (a + b) / 2
  
  -- Symmetrized midpoint analysis:
  -- Find integer n such that the chosen interval I_int g k n overlaps [a, b] by at least α * L
  have h_overlap : ∃ (n : ℤ) (c : ℝ),
      a ≤ c ∧ c + α * L ≤ b ∧ Set.Icc c (c + α * L) ⊆ I_int g k n := by
    -- Evaluate worst-case midpoint alignment
    have h_min_bound : α * L ≤ min ((1 / 2) * L - (1 / 2) * gap) w := by
      apply le_min
      · -- (1/2)*L - (1/2)*gap - α*L ≥ 0 from equation (20) lower bound
        have h_id := half_sub_alpha_g g
        sorry
      · -- α*L ≤ w from equation (20) upper bound
        sorry
    sorry

  obtain ⟨n, c, hac, hdb, h_sub⟩ := h_overlap
  refine ⟨k, hk, c, c + α * L, ?_, ?_, ?_, ?_⟩
  · linarith [mul_pos hα_pos hL_pos]
  · exact Set.Icc_subset_Icc hac hdb
  · ring
  · exact Set.Subset.trans h_sub (I_int_subset_K g k n)
