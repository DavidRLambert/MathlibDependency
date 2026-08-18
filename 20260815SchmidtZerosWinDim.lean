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

/-- The combined contraction parameter q = α * β -/
def contractionParam (params : SchmidtParams) : ℝ :=
  params.α * params.β

/-- Proof that 0 < α * β < 1 -/
lemma contraction_in_bounds (params : SchmidtParams) :
    0 < contractionParam params ∧ contractionParam params < 1 := by
  constructor
  · unfold contractionParam
    nlinarith [params.hα_pos, params.hβ_pos]
  · unfold contractionParam
    nlinarith [params.hα_pos, params.hα_lt, params.hβ_pos, params.hβ_lt]

/-- Main Convergence Theorem: The sequence of radii r_0 * (α * β)^n tends to 0 as n -> ∞ -/
theorem radius_sequence_tendsto_zero (params : SchmidtParams) (r0 : ℝ) :
    Filter.Tendsto (fun (n : ℕ) => r0 * (contractionParam params) ^ n)
    Filter.atTop (nhds 0) := by
  have h_bounds := contraction_in_bounds params
  have h_pow : Filter.Tendsto (fun (n : ℕ) => (contractionParam params) ^ n) Filter.atTop (nhds 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · linarith [h_bounds.1]
    · exact h_bounds.2
  simpa using Filter.Tendsto.const_mul r0 h_pow

/-- A valid infinite nested sequence of closed balls whose radii decay to zero. -/
structure NestedBallSeq (X : Type*) [MetricSpace X] where
  ball : ℕ → GameBall X
  nested : ∀ n, (ball (n + 1)).toSet ⊆ (ball n).toSet
  radii_tendsto : Filter.Tendsto (fun n => (ball n).radius) Filter.atTop (nhds 0)

/-- Cantor's Intersection Theorem for closed balls:
    An infinite sequence of nested closed balls with vanishing radii
    has a UNIQUE point of intersection x*. -/
theorem nested_balls_intersection_unique [CompleteSpace X] (seq : NestedBallSeq X) :
    ∃! x : X, ∀ n : ℕ, x ∈ (seq.ball n).toSet := by
  let c := fun n => (seq.ball n).center
  let r := fun n => (seq.ball n).radius

  have hCauchy : CauchySeq c := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    have h_tendsto := Metric.tendsto_atTop.mp seq.radii_tendsto ε hε
    rcases h_tendsto with ⟨N, hN⟩
    use N
    intro m hm
    have h_subset : (seq.ball m).toSet ⊆ (seq.ball N).toSet := by
      induction hm with
      | refl => exact subset_rfl
      | step hm' ih => exact Set.Subset.trans (seq.nested _) ih

    have h_cm_in_Bm : c m ∈ (seq.ball m).toSet :=
      Metric.mem_closedBall_self (le_of_lt (seq.ball m).r_pos)
    have h_cm_in_BN : c m ∈ (seq.ball N).toSet := h_subset h_cm_in_Bm
    have h_dist_centers : dist (c m) (c N) ≤ r N := h_cm_in_BN
    have h_limit_N : dist (r N) 0 < ε := hN N (le_refl N)

    have h_rN_lt_ε : r N < ε := by
      calc
        r N ≤ |r N| := le_abs_self (r N)
        _ = |r N - 0| := by rw [sub_zero]
        _ = dist (r N) 0 := (Real.dist_eq (r N) 0).symm
        _ < ε := h_limit_N
    exact lt_of_le_of_lt h_dist_centers h_rN_lt_ε

  rcases cauchySeq_tendsto_of_complete hCauchy with ⟨x_star, hx_lim⟩
  use x_star

  have hx_star_in : ∀ n, x_star ∈ (seq.ball n).toSet := by
    intro n
    have h_closed : IsClosed ((seq.ball n).toSet) := Metric.isClosed_closedBall
    have h_subset : ∀ m, n ≤ m → (seq.ball m).toSet ⊆ (seq.ball n).toSet := by
      intro m hm
      induction hm with
      | refl => exact subset_rfl
      | step hm' ih => exact Set.Subset.trans (seq.nested _) ih
    have h_in_eventually : ∀ᶠ m in Filter.atTop, c m ∈ (seq.ball n).toSet := by
      filter_upwards [Filter.eventually_ge_atTop n] with m hm
      exact h_subset m hm (Metric.mem_closedBall_self (le_of_lt (seq.ball m).r_pos))
    exact h_closed.mem_of_tendsto hx_lim h_in_eventually

  constructor
  · exact hx_star_in
  · intro y hy
    apply dist_eq_zero.mp
    have h_dist_bound : ∀ n, dist x_star y ≤ 2 * r n := by
      intro n
      have hx : dist x_star (c n) ≤ r n := hx_star_in n
      have hy_dist : dist y (c n) ≤ r n := hy n
      calc
        dist x_star y ≤ dist x_star (c n) + dist (c n) y := dist_triangle x_star (c n) y
        _ = dist x_star (c n) + dist y (c n) := by rw [dist_comm (c n) y]
        _ ≤ r n + r n := add_le_add hx hy_dist
        _ = 2 * r n := by ring

    have h_tendsto : Filter.Tendsto (fun n => 2 * r n) Filter.atTop (nhds 0) := by
      simpa using Filter.Tendsto.const_mul 2 seq.radii_tendsto

    have h_le_zero : dist x_star y ≤ 0 :=
      ge_of_tendsto h_tendsto (Filter.Eventually.of_forall h_dist_bound)

    rw [dist_comm] at h_le_zero
    exact le_antisymm h_le_zero dist_nonneg

/-- A strategy for Alice is a function that provides a valid AliceMove
    for any possible ball B chosen by Bob. -/
def AliceStrategy (params : SchmidtParams) :=
  (n : ℕ) → (B : GameBall X) → AliceMove params B

/-- A sequence of Bob's balls constitutes a valid play against Alice's strategy if
    every subsequent ball B_{n+1} is a valid BobMove inside Alice's response to B_n. -/
def isValidPlay {X : Type*} [MetricSpace X] (params : SchmidtParams) (fA : AliceStrategy (X := X) params)
    (B_seq : ℕ → GameBall X) : Prop :=
  ∀ n, ∃ (moveB : BobMove params (fA n (B_seq n)).A), moveB.B' = B_seq (n + 1)

/-- Radius step along a valid game sequence. -/
lemma valid_play_radius_step {params : SchmidtParams} {fA : AliceStrategy params}
    {B_seq : ℕ → GameBall X} (h_valid : isValidPlay params fA B_seq) (n : ℕ) :
    (B_seq (n + 1)).radius = contractionParam params * (B_seq n).radius := by
  obtain ⟨moveB, hB_eq⟩ := h_valid n
  calc
    (B_seq (n + 1)).radius = moveB.B'.radius := by rw [← hB_eq]
    _ = params.β * (fA n (B_seq n)).A.radius := moveB.r_eq
    _ = params.β * (params.α * (B_seq n).radius) := by rw [(fA n (B_seq n)).r_eq]
    _ = (params.α * params.β) * (B_seq n).radius := by ring
    _ = contractionParam params * (B_seq n).radius := rfl

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

/-- A valid sequence of plays guarantees the creation of a NestedBallSeq. -/
noncomputable def valid_play_is_nested_seq {X : Type*} [MetricSpace X] (params : SchmidtParams) 
    (fA : AliceStrategy params) (B_seq : ℕ → GameBall X) 
    (h_valid : isValidPlay params fA B_seq) :
    NestedBallSeq X where
  ball := B_seq
  nested := by
    intro n
    obtain ⟨moveB, hB_eq⟩ := h_valid n
    rw [← hB_eq]
    exact Set.Subset.trans moveB.sub (fA n (B_seq n)).sub
  radii_tendsto := by
    have h_radius_step : ∀ n, (B_seq (n + 1)).radius = (contractionParam params) * (B_seq n).radius :=
      valid_play_radius_step h_valid
    have h_radius_eq : ∀ n, (B_seq n).radius = (B_seq 0).radius * contractionParam params ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc
          (B_seq (n + 1)).radius = contractionParam params * (B_seq n).radius := h_radius_step n
          _ = contractionParam params * ((B_seq 0).radius * contractionParam params ^ n) := by rw [ih]
          _ = (B_seq 0).radius * contractionParam params ^ (n + 1) := by ring
    have h_eq : (fun n => (B_seq n).radius) = (fun n => (B_seq 0).radius * contractionParam params ^ n) := by
      ext n
      exact h_radius_eq n
    rw [h_eq]
    exact radius_sequence_tendsto_zero params ((B_seq 0).radius)

def IsAlphaWinning (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1) (S : Set X) : Prop :=
  ∀ (β : ℝ) (hβ_pos : 0 < β) (hβ_lt : β < 1),
    IsWinningSet ⟨α, β, hα_pos, hα_lt, hβ_pos, hβ_lt⟩ S

/-- Map a turn number n to (i, k), where i is the strategy index 
    and k is the turn number for that strategy. -/
def turnToStrategy (n : ℕ) : ℕ × ℕ :=
  let m := n + 1
  let i := padicValNat 2 m
  let k := ((m / 2^i) - 1) / 2
  (i, k)

/-- Combine heterogeneous sub-game strategies where α is constant across all games. -/
def interleavedStrategy {X : Type*} [MetricSpace X] (params : SchmidtParams)
    (sub_params : ℕ → SchmidtParams) (hα : ∀ i, (sub_params i).α = params.α)
    (strats : (i : ℕ) → AliceStrategy (X:=X) (sub_params i)) : AliceStrategy (X:=X) params :=
  fun n B =>
    let (i, k) := turnToStrategy n
    let move := strats i k B
    { A := move.A
      sub := move.sub
      r_eq := by rw [move.r_eq, hα i] }

/-- The tailored contraction parameter β_i for the i-th interleaved sub-game. -/
def schmidtBeta (α β : ℝ) (i : ℕ) : ℝ :=
  α ^ (2^(i + 1) - 1) * β ^ (2^(i + 1))

lemma schmidtBeta_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (i : ℕ) :
    0 < schmidtBeta α β i := by
  unfold schmidtBeta
  positivity

lemma schmidtBeta_lt {α β : ℝ} (hα_pos : 0 < α) (hα_lt : α < 1)
    (hβ_pos : 0 < β) (hβ_lt : β < 1) (i : ℕ) :
    schmidtBeta α β i < 1 := by
  unfold schmidtBeta
  have hα : α ^ (2^(i + 1) - 1) ≤ 1 := pow_le_one₀ hα_pos.le hα_lt.le
  have hβ : β ^ (2^(i + 1)) < 1 := pow_lt_one₀ hβ_pos.le hβ_lt (by positivity)
  have : 0 ≤ α ^ (2^(i + 1) - 1) := by positivity
  have : 0 ≤ β ^ (2^(i + 1)) := by positivity
  nlinarith

def turnIdx (i k : ℕ) : ℕ :=
  2^(i + 1) * k + 2^i - 1

def subBallSeq (i : ℕ) (B_seq : ℕ → GameBall X) : ℕ → GameBall X :=
  fun k => B_seq (turnIdx i k)

lemma play_nesting_step {params : SchmidtParams} {fA : AliceStrategy (X := X) params}
    {B_seq : ℕ → GameBall X} (h_valid : isValidPlay params fA B_seq) (n : ℕ) :
    (B_seq (n + 1)).toSet ⊆ (fA n (B_seq n)).A.toSet ∧
    (fA n (B_seq n)).A.toSet ⊆ (B_seq n).toSet :=
    let ⟨moveB, hB_eq⟩ := h_valid n
    ⟨hB_eq ▸ moveB.sub, (fA n (B_seq n)).sub⟩

lemma turnIdx_succ_gap (i k : ℕ) :
    turnIdx i (k + 1) = turnIdx i k + 2^(i + 1) := by
  unfold turnIdx
  have : 1 ≤ 2^i := Nat.one_le_two_pow
  rw [mul_add, mul_one]
  omega

lemma turnToStrategy_turnIdx (i k : ℕ) :
    turnToStrategy (turnIdx i k) = (i, k) := by
  unfold turnToStrategy turnIdx
  have h_eq : 2^(i + 1) * k + 2^i - 1 + 1 = 2^i * (2 * k + 1) := by
    have h_pos : 1 ≤ 2^(i + 1) * k + 2^i := by
      have : 1 ≤ 2^i := Nat.one_le_two_pow
      omega
    rw [Nat.sub_add_cancel h_pos, pow_succ]
    ring
  dsimp only
  rw [h_eq]
  have h_odd : ¬ 2 ∣ 2 * k + 1 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_padic : padicValNat 2 (2^i * (2 * k + 1)) = i := by
    rw [padicValNat.mul (by positivity) (by omega)]
    rw [padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd h_odd, add_zero]
  have h_div : 2^i * (2 * k + 1) / 2^i = 2 * k + 1 :=
    Nat.mul_div_cancel_left _ (by positivity)
  ext
  · exact h_padic
  · dsimp
    rw [h_padic, h_div]
    omega

lemma play_subset_step {params : SchmidtParams} {fA : AliceStrategy params}
    {B_seq : ℕ → GameBall X} (h_valid : isValidPlay params fA B_seq) (n : ℕ) :
    ∀ m ≥ 1, (B_seq (n + m)).toSet ⊆ (fA n (B_seq n)).A.toSet
  | 1, _ => (play_nesting_step h_valid n).1
  | m + 2, _ => by
    have ih := play_subset_step h_valid n (m + 1) (by omega)
    have step := (play_nesting_step h_valid (n + m + 1)).1
    have step_sub := (play_nesting_step h_valid (n + m + 1)).2
    exact step.trans (step_sub.trans ih)

lemma play_radius_step {params : SchmidtParams} {fA : AliceStrategy params}
    {B_seq : ℕ → GameBall X} (h_valid : isValidPlay params fA B_seq) (n : ℕ) :
    ∀ m ≥ 1, (B_seq (n + m)).radius =
      (params.α ^ (m - 1) * params.β ^ m) * (fA n (B_seq n)).A.radius
  | 1, _ => by
    obtain ⟨moveB, hB⟩ := h_valid n
    have h0 : 1 - 1 = 0 := rfl
    rw [← hB, moveB.r_eq, h0, pow_zero, pow_one]
    ring
  | m + 2, _ => by
    have ih := play_radius_step h_valid n (m + 1) (by omega)
    obtain ⟨moveB, hB⟩ := h_valid (n + m + 1)
    have hA_rad := (fA (n + m + 1) (B_seq (n + m + 1))).r_eq
    have h_idx1 : n + (m + 2) = (n + m + 1) + 1 := by omega
    have h_idx2 : n + m + 1 = n + (m + 1) := by omega
    have h1 : m + 1 - 1 = m := by omega
    have h2 : m + 2 - 1 = m + 1 := by omega
    have h3 : m + 2 = m + 1 + 1 := by omega
    rw [h_idx1, ← hB, moveB.r_eq, hA_rad, h_idx2, ih]
    rw [h1, h2, h3, pow_succ params.α m, pow_succ params.β (m + 1)]
    ring

theorem countable_intersection_alpha [CompleteSpace X]
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (S : ℕ → Set X) (h_win : ∀ i, IsAlphaWinning α hα_pos hα_lt (S i)) :
    IsAlphaWinning α hα_pos hα_lt (⋂ i, S i) := by
  intro β hβ_pos hβ_lt

  let params : SchmidtParams := ⟨α, β, hα_pos, hα_lt, hβ_pos, hβ_lt⟩

  let sub_params : ℕ → SchmidtParams := fun i => {
    α := α
    β := schmidtBeta α β i
    hα_pos := hα_pos
    hα_lt  := hα_lt
    hβ_pos := schmidtBeta_pos hα_pos hβ_pos i
    hβ_lt  := schmidtBeta_lt hα_pos hα_lt hβ_pos hβ_lt i
  }

  have hα_eq : ∀ i, (sub_params i).α = params.α := fun _ => rfl

  have h_sub_win : ∀ i, IsWinningSet (sub_params i) (S i) := by
    intro i
    exact h_win i (schmidtBeta α β i)
      (schmidtBeta_pos hα_pos hβ_pos i)
      (schmidtBeta_lt hα_pos hα_lt hβ_pos hβ_lt i)

  choose strats h_strats using h_sub_win

  use interleavedStrategy params sub_params hα_eq strats
  intro B_seq h_valid x hx

  rw [Set.mem_iInter]
  intro i

  have h_sub_valid : isValidPlay (sub_params i) (strats i) (subBallSeq i B_seq) := by
    intro k
    let n := turnIdx i k
    let m := 2^(i + 1)
    have hm : 1 ≤ m := Nat.one_le_two_pow
    have h_gap : turnIdx i (k + 1) = n + m := turnIdx_succ_gap i k
    
    have h_strat_eval :
        (interleavedStrategy params sub_params hα_eq strats n (B_seq n)).A =
        (strats i k (subBallSeq i B_seq k)).A := by
      dsimp [interleavedStrategy, subBallSeq, n]
      rw [turnToStrategy_turnIdx]

    have h_sub := play_subset_step h_valid n m hm
    have h_rad := play_radius_step h_valid n m hm
    rw [h_strat_eval] at h_sub h_rad

    let moveB : BobMove (sub_params i) (strats i k (subBallSeq i B_seq k)).A := {
      B'   := subBallSeq i B_seq (k + 1)
      sub  := by
        dsimp [subBallSeq]
        rw [h_gap]
        exact h_sub
      r_eq := by
        dsimp [subBallSeq, sub_params, schmidtBeta]
        rw [h_gap]
        exact h_rad
    }
    exact ⟨moveB, rfl⟩

  have h_x_in_sub : ∀ k, x ∈ (subBallSeq i B_seq k).toSet := by
    intro k
    exact hx (turnIdx i k)

  exact h_strats i (subBallSeq i B_seq) h_sub_valid x h_x_in_sub

def winningAlphas (S : Set X) : Set ℝ :=
  { α | ∃ (hα_pos : 0 < α) (hα_lt : α < 1), IsAlphaWinning α hα_pos hα_lt S }

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

noncomputable def baseDigit (g : ℕ) (k : ℕ) (x : ℝ) : ℤ :=
  ⌊x * (g : ℝ)^k⌋ - (g : ℤ) * ⌊x * (g : ℝ)^(k - 1)⌋

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
    ∃ (k : ℕ) (_hk : 1 ≤ k) (n : ℤ) (c d : ℝ) (_hcd : c < d),
      1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(k + 1)) < b - a ∧
      Set.Icc c d ⊆ Set.Icc a b ∧
      d - c = alpha_g g * (b - a) ∧
      Set.Icc c d ⊆ I_int g k n := by
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
        max_le (by linarith only [ha_eq, hb_eq, h_alpha_L_le_L])
               (by linarith only [h_min1, hn_le, hb_eq, h_gap_nonneg])
      have hcb : c + α * L ≤ b := by linarith only [hc_le_b]
      have hc_le_w : c ≤ (n : ℝ) * period + w - α * L :=
        max_le (by linarith only [ha_eq, h_case, h_min1])
               (by linarith only [h_min2])
      have h_sub : Set.Icc c (c + α * L) ⊆ I_int g k n := by
        unfold I_int
        rw [h_xn_period]
        exact Set.Icc_subset_Icc hnc (by linarith only [hc_le_w])
      exact ⟨n, c, hac, hcb, h_sub⟩
    · have h_case2 : (n : ℝ) * period + w + (1 / 2) * gap < m := not_le.mp h_case
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
        max_le (by linarith only [ha_eq, hb_eq, h_alpha_L_le_L])
               (by linarith only [hn1_period, h_case2, hb_eq, h_min1])
      have hcb : c + α * L ≤ b := by linarith only [hc_le_b]
      have hc_le_w : c ≤ ((n + 1 : ℤ) : ℝ) * period + w - α * L :=
        max_le (by linarith only [ha_eq, h_lt_n1', h_min2, hL_pos])
               (by linarith only [h_min2])
      have h_sub : Set.Icc c (c + α * L) ⊆ I_int g k (n + 1) := by
        unfold I_int
        rw [hn1_period_div]
        exact Set.Icc_subset_Icc hnc (by linarith only [hc_le_w])
      exact ⟨n + 1, c, hac, hcb, h_sub⟩

  obtain ⟨n, c, hac, hdb, h_sub⟩ := h_overlap
  refine ⟨k, hk, n, c, c + α * L, ?_, h_lower, ?_, ?_, h_sub⟩
  · linarith [mul_pos hα_pos hL_pos]
  · exact Set.Icc_subset_Icc hac hdb
  · ring

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

def I_int_interior (g : ℕ) (k : ℕ) (n : ℤ) : Set ℝ :=
  Set.Ioo 
    ((n : ℝ) / (g : ℝ)^k) 
    ((n : ℝ) / (g : ℝ)^k + 1 / (((g : ℝ) - 1) * (g : ℝ)^k))

lemma baseDigit_shift (g : ℕ) (k j : ℕ) (n : ℤ) (x y : ℝ) (hy : y = x * (g : ℝ)^k - (n : ℝ)) :
    baseDigit g (k + j + 1) x = ⌊y * (g : ℝ)^(j + 1)⌋ - (g : ℤ) * ⌊y * (g : ℝ)^j⌋ := by
  dsimp [baseDigit]
  have h1 : x * (g : ℝ)^(k + j + 1) = ((n * (g : ℤ)^(j + 1) : ℤ) : ℝ) + y * (g : ℝ)^(j + 1) := by
    have : (g : ℝ)^(k + j + 1) = (g : ℝ)^k * (g : ℝ)^(j + 1) := by
      rw [show k + j + 1 = k + (j + 1) by omega, pow_add]
    rw [this]
    have : x * ((g : ℝ)^k * (g : ℝ)^(j + 1)) = (x * (g : ℝ)^k) * (g : ℝ)^(j + 1) := by ring
    rw [this]
    have hx : x * (g : ℝ)^k = (n : ℝ) + y := by linarith [hy]
    rw [hx]
    push_cast
    ring
  have h2 : x * (g : ℝ)^(k + j) = ((n * (g : ℤ)^j : ℤ) : ℝ) + y * (g : ℝ)^j := by
    have : (g : ℝ)^(k + j) = (g : ℝ)^k * (g : ℝ)^j := by rw [pow_add]
    rw [this]
    have : x * ((g : ℝ)^k * (g : ℝ)^j) = (x * (g : ℝ)^k) * (g : ℝ)^j := by ring
    rw [this]
    have hx : x * (g : ℝ)^k = (n : ℝ) + y := by linarith [hy]
    rw [hx]
    push_cast
    ring
  rw [h1, h2]
  rw [Int.floor_intCast_add, Int.floor_intCast_add]
  rw [pow_succ (g : ℤ) j]
  ring

lemma geom_sum_floor_bound (g : ℕ) (hg : 2 < g) (y : ℝ) (hy0 : 0 ≤ y)
    (h_pos : ∀ i : ℕ, 1 ≤ ⌊y * (g : ℝ)^(i + 1)⌋ - (g : ℤ) * ⌊y * (g : ℝ)^i⌋) :
    ∀ j : ℕ, ((g : ℝ)^j - 1) / ((g : ℝ) - 1) ≤ (⌊y * (g : ℝ)^j⌋ : ℝ) := by
  intro j
  induction j with
  | zero =>
    simp only [pow_zero, sub_self, zero_div, mul_one]
    exact_mod_cast (Int.floor_nonneg.mpr hy0)
  | succ j ih =>
    have h_step := h_pos j
    have h_int_le : (g : ℤ) * ⌊y * (g : ℝ)^j⌋ + 1 ≤ ⌊y * (g : ℝ)^(j + 1)⌋ := by
      linarith [h_step]
    have h_cast : (g : ℝ) * (⌊y * (g : ℝ)^j⌋ : ℝ) + 1 ≤ (⌊y * (g : ℝ)^(j + 1)⌋ : ℝ) := by
      exact_mod_cast h_int_le
    have hgm1_pos : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
    have h_geom : ((g : ℝ)^(j + 1) - 1) / ((g : ℝ) - 1) = (g : ℝ) * (((g : ℝ)^j - 1) / ((g : ℝ) - 1)) + 1 := by
      have : (g : ℝ) - 1 ≠ 0 := ne_of_gt hgm1_pos
      field_simp
      ring
    rw [h_geom]
    have hg_nonneg : 0 ≤ (g : ℝ) := by positivity
    nlinarith

lemma baseDigit_nonneg (g : ℕ) (k : ℕ) (x : ℝ) (hk : 1 ≤ k) :
    0 ≤ baseDigit g k x := by
  dsimp [baseDigit]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  simp only [Nat.add_sub_cancel]
  rw [sub_nonneg]
  apply Int.le_floor.mpr
  push_cast
  rw [pow_succ]
  have : (⌊x * (g : ℝ)^m⌋ : ℝ) ≤ x * (g : ℝ)^m := Int.floor_le _
  nlinarith

lemma zero_digit_of_mem_interior (g : ℕ) (hg : 2 < g) (k : ℕ) (n : ℤ) {x : ℝ}
    (hx : x ∈ I_int_interior g k n) :
    ∃ (m : ℕ), m ≥ k + 1 ∧ baseDigit g m x = 0 := by
  dsimp [I_int_interior] at hx
  set y := x * (g : ℝ)^k - (n : ℝ)
  have hgm1_pos : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
  have hgk_pos : 0 < (g : ℝ)^k := by positivity
  
  have hy_pos : 0 < y := by
    have h1 := hx.1
    have : (n : ℝ) < x * (g : ℝ)^k := (div_lt_iff₀ hgk_pos).mp h1
    linarith
  have hy_ub : y < 1 / ((g : ℝ) - 1) := by
    have h2 := hx.2
    have h_mul : x * (g : ℝ)^k < (n : ℝ) + 1 / ((g : ℝ) - 1) := by
      calc x * (g : ℝ)^k < ((n : ℝ) / (g : ℝ)^k + 1 / (((g : ℝ) - 1) * (g : ℝ)^k)) * (g : ℝ)^k := by
            exact (mul_lt_mul_iff_of_pos_right hgk_pos).mpr h2
      _ = (n : ℝ) + 1 / ((g : ℝ) - 1) := by
            have : ((g : ℝ) - 1) * (g : ℝ)^k ≠ 0 := by positivity
            have : (g : ℝ)^k ≠ 0 := by positivity
            field_simp; 
    linarith

  by_contra! h_no_zero
  have h_pos_digit : ∀ j : ℕ, 1 ≤ baseDigit g (k + j + 1) x := by
    intro j
    have h_ne := h_no_zero (k + j + 1) (by omega)
    have h_nonneg := baseDigit_nonneg g (k + j + 1) x (by omega)
    omega

  have h_floor_bound : ∀ j : ℕ, ((g : ℝ)^j - 1) / ((g : ℝ) - 1) ≤ (⌊y * (g : ℝ)^j⌋ : ℝ) := by
    apply geom_sum_floor_bound g hg y (le_of_lt hy_pos)
    intro i
    have h_sh := baseDigit_shift g k i n x y rfl
    have h_dig := h_pos_digit i
    rwa [h_sh] at h_dig

  have h_bound : ∀ j : ℕ, ((g : ℝ)^j - 1) / ((g : ℝ) - 1) ≤ y * (g : ℝ)^j := by
    intro j
    exact le_trans (h_floor_bound j) (Int.floor_le _)

  set δ := 1 / ((g : ℝ) - 1) - y
  have hδ_pos : 0 < δ := sub_pos.mpr hy_ub
  have h_tendsto : Filter.Tendsto (fun j : ℕ => δ * (g : ℝ)^j) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hδ_pos (tendsto_pow_atTop_atTop_of_one_lt (by linarith))
  
  obtain ⟨J, hJ⟩ := (Filter.tendsto_atTop_atTop.mp h_tendsto) (1 / ((g : ℝ) - 1) + 1)
  have hJ_spec := hJ J (le_refl J)
  have h_contra := h_bound J
  
  have : y * (g : ℝ)^J < ((g : ℝ)^J - 1) / ((g : ℝ) - 1) := by
    have : ((g : ℝ)^J - 1) / ((g : ℝ) - 1) = (1 / ((g : ℝ) - 1)) * (g : ℝ)^J - 1 / ((g : ℝ) - 1) := by
      field_simp; 
    rw [this]
    dsimp [δ] at hJ_spec
    linarith
  linarith

/-! 7. Alice's Inductive Response & Interior Contraction State Machine -/

structure AliceMove16 (params : SchmidtParams) (g : ℕ) (B : GameBall ℝ) extends AliceMove params B where
  k : ℕ
  hk : 1 ≤ k
  n : ℤ
  h_scale : 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(k + 1)) < 2 * B.radius
  h_int : toAliceMove.A.toSet ⊆ I_int g k n

lemma alice_move_16_nonempty (g : ℕ) (hg : 2 < g) (params : SchmidtParams)
    (hα_eq : params.α = alpha_g g) (B : GameBall ℝ)
    (hB_radius : 2 * B.radius ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ)))) :
    Nonempty (AliceMove16 params g B) := by
  set a := B.center - B.radius
  set b := B.center + B.radius
  have hab : a < b := by
    have := B.r_pos
    linarith
  have h_len : b - a ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ))) := by
    rw [gameBall_length]
    exact hB_radius
  obtain ⟨k, hk, n, c, d, hcd, h_scale, h_sub, h_len_eq, h_int⟩ := schmidt_lemma_16 g hg a b hab h_len
  have h_rad : (d - c) / 2 = params.α * B.radius := by
    rw [h_len_eq, hα_eq, gameBall_length]
    ring
  set A := gameBallOfIcc c d hcd
  have h_sub' : IsSubBall A B := by
    dsimp [IsSubBall]
    rw [gameBallOfIcc_toSet, gameBall_toSet_real]
    exact h_sub
  have h_r_eq : A.radius = params.α * B.radius := by
    dsimp [A, gameBallOfIcc]
    exact h_rad
  have h_scale' : 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(k + 1)) < 2 * B.radius := by
    rwa [gameBall_length] at h_scale
  have h_int' : A.toSet ⊆ I_int g k n := by
    rw [gameBallOfIcc_toSet]
    exact h_int
  exact ⟨⟨⟨A, h_sub', h_r_eq⟩, k, hk, n, h_scale', h_int'⟩⟩

noncomputable def aliceChoice16 (g : ℕ) (hg : 2 < g) (params : SchmidtParams)
    (hα_eq : params.α = alpha_g g) (B : GameBall ℝ)
    (h : 2 * B.radius ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ)))) :
    AliceMove16 params g B :=
  Classical.choice (alice_move_16_nonempty g hg params hα_eq B h)

/-- Alice's default concentric move. -/
def concentricMove (params : SchmidtParams) (B : GameBall ℝ) : AliceMove params B :=
  ⟨⟨B.center, params.α * B.radius, mul_pos params.hα_pos B.r_pos⟩, by
    dsimp [IsSubBall]
    rw [gameBall_toSet_real, gameBall_toSet_real]
    intro x ⟨h1, h2⟩
    have : params.α * B.radius < B.radius := by
      nlinarith [params.hα_pos, params.hα_lt, B.r_pos]
    constructor <;> linarith,
  rfl⟩

/-- Given a ball B contained in I_k(n), a concentric move by Alice strictly contracts into the interior. -/
lemma concentricMove_subset_interior (g : ℕ) (hg : 2 < g) (k : ℕ) (n : ℤ) (B : GameBall ℝ)
    (hB_sub : B.toSet ⊆ I_int g k n) (params : SchmidtParams) (hα_eq : params.α = alpha_g g) :
    (concentricMove params B).A.toSet ⊆ I_int_interior g k n := by
  have hα_lt : params.α < 1 := by rw [hα_eq]; exact alpha_g_lt_one g hg
  have h_shrink : params.α * B.radius < B.radius := by
    nlinarith [hα_lt, B.r_pos]

  have h_left : (n : ℝ) / (g : ℝ)^k ≤ B.center - B.radius := by
    have h_mem : B.center - B.radius ∈ B.toSet := by
      rw [gameBall_toSet_real]
      exact ⟨le_rfl, by linarith [B.r_pos]⟩
    exact (hB_sub h_mem).1

  have h_right : B.center + B.radius ≤ (n : ℝ) / (g : ℝ)^k + 1 / (((g : ℝ) - 1) * (g : ℝ)^k) := by
    have h_mem : B.center + B.radius ∈ B.toSet := by
      rw [gameBall_toSet_real]
      exact ⟨by linarith [B.r_pos], le_rfl⟩
    exact (hB_sub h_mem).2

  rw [gameBall_toSet_real]
  dsimp [concentricMove, I_int_interior]
  intro x ⟨hxa, hxb⟩
  constructor <;> linarith [h_left, h_right, h_shrink, hxa, hxb]

/-- The threshold for triggering Lemma 16 at scale N. -/
noncomputable def aliceThreshold (g : ℕ) (N : ℕ) : ℝ :=
  (1 / 2) * (1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(N + 1)))

lemma aliceThreshold_pos (g : ℕ) (hg : 2 < g) (N : ℕ) : 0 < aliceThreshold g N := by
  dsimp [aliceThreshold]
  have : 0 < alpha_g g := alpha_g_pos g
  have : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
  have : 0 < (g : ℝ) := by linarith [g_real_gt_two g hg]
  positivity

lemma aliceThreshold_le_lemma16 (g : ℕ) (hg : 2 < g) (N : ℕ) :
    2 * aliceThreshold g N ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ))) := by
  have hg_gt1 : 1 < (g : ℝ) := by
    have := g_real_gt_two g hg; linarith
  have h_pow_le : (g : ℝ)^1 ≤ (g : ℝ)^(N + 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have h_denom_pos1 : 0 < alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^1 := by
    have : 0 < alpha_g g := alpha_g_pos g
    have : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
    positivity
  have h_denom_pos2 : 0 < alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(N + 1) := by
    have : 0 < alpha_g g := alpha_g_pos g
    have : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
    positivity
  have h_inv_le : 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(N + 1)) ≤
      1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^1) := by
    rw [div_le_div_iff₀ h_denom_pos2 h_denom_pos1]
    have h_coeff : 0 ≤ alpha_g g * ((g : ℝ) - 1) := by
      have : 0 < alpha_g g := alpha_g_pos g
      have : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
      positivity
    nlinarith [mul_le_mul_of_nonneg_left h_pow_le h_coeff]
  have h_scale1 : alpha_g g * ((g : ℝ)^2 - (g : ℝ)) = alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^1 := by ring
  have h_inv_eq : 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^1) = 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ))) := by
    rw [h_scale1]
  have h_2thresh : 2 * aliceThreshold g N = 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(N + 1)) := by
    dsimp [aliceThreshold]; ring
  rw [h_2thresh]
  rwa [h_inv_eq] at h_inv_le

lemma radius_le_lemma16_of_le_threshold (g : ℕ) (hg : 2 < g) (N : ℕ) (B : GameBall ℝ)
    (hB : B.radius ≤ aliceThreshold g N) :
    2 * B.radius ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ))) := by
  have h1 : 2 * B.radius ≤ 2 * aliceThreshold g N := by linarith
  exact h1.trans (aliceThreshold_le_lemma16 g hg N)

/-- Alice's strategy tracks the state to execute Lemma 16 on the unique trigger turn, 
    and concentric moves elsewhere to guarantee interior contraction. -/
noncomputable def aliceStrategy (g : ℕ) (hg : 2 < g) (params : SchmidtParams)
    (hα_eq : params.α = alpha_g g) (N : ℕ) : AliceStrategy (X := ℝ) params := fun n B =>
  if h : (n = 0 ∧ B.radius ≤ aliceThreshold g N) ∨
         (0 < n ∧ contractionParam params * aliceThreshold g N < B.radius ∧ B.radius ≤ aliceThreshold g N) then
    have h_le : 2 * B.radius ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ))) := by
      rcases h with ⟨-, hB⟩ | ⟨-, -, hB⟩
      · exact radius_le_lemma16_of_le_threshold g hg N B hB
      · exact radius_le_lemma16_of_le_threshold g hg N B hB
    (aliceChoice16 g hg params hα_eq B h_le).toAliceMove
  else
    concentricMove params B

/-! 8. Theorem 5: S_g Winning Strategy & Winning Dimension -/

lemma S_g_eq_iInter (g : ℕ) : 
    S_g g = ⋂ N : ℕ, { x : ℝ | ∃ k : ℕ, k ≥ N ∧ baseDigit g k x = 0 } := by
  ext x
  simp only [S_g, Set.mem_ofPred_eq, Set.mem_iInter]

/-- Alice wins the single-zero target at scale ≥ N by forcing the game strictly into the interior. -/
lemma alice_wins_single_zero (g : ℕ) (hg : 2 < g) (N : ℕ) :
    IsAlphaWinning (alpha_g g) (alpha_g_pos g) (alpha_g_lt_one g hg)
      { x : ℝ | ∃ k : ℕ, k ≥ N ∧ baseDigit g k x = 0 } := by
  intro β hβ_pos hβ_lt
  let params : SchmidtParams := ⟨alpha_g g, β, alpha_g_pos g, alpha_g_lt_one g hg, hβ_pos, hβ_lt⟩
  
  have h_win : IsWinningSet params { x : ℝ | ∃ k : ℕ, k ≥ N ∧ baseDigit g k x = 0 } := by
    use aliceStrategy g hg params rfl N
    intro B_seq h_valid x hx
    
    have h_thresh_pos := aliceThreshold_pos g hg N
    let h_nested := valid_play_is_nested_seq params (aliceStrategy g hg params rfl N) B_seq h_valid
    have h_tendsto := h_nested.radii_tendsto
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp 
      (h_tendsto (isOpen_Iio.mem_nhds h_thresh_pos))
    
    have h_ex : ∃ n, (B_seq n).radius ≤ aliceThreshold g N :=
      ⟨M, le_of_lt (hM M le_rfl)⟩

    classical
    let n₀ := Nat.find h_ex
    have hn₀_le : (B_seq n₀).radius ≤ aliceThreshold g N := Nat.find_spec h_ex
    have hn₀_min : ∀ m < n₀, ¬ ((B_seq m).radius ≤ aliceThreshold g N) :=
      fun m hm => Nat.find_min h_ex hm

    have h_trigger : (n₀ = 0 ∧ (B_seq n₀).radius ≤ aliceThreshold g N) ∨
        (0 < n₀ ∧ contractionParam params * aliceThreshold g N < (B_seq n₀).radius ∧
          (B_seq n₀).radius ≤ aliceThreshold g N) := by
      by_cases h0 : n₀ = 0
      · exact Or.inl ⟨h0, hn₀_le⟩
      · have h_pos : 0 < n₀ := Nat.pos_of_ne_zero h0
        have h_prev := hn₀_min (n₀ - 1) (by omega)
        have h_prev_gt : aliceThreshold g N < (B_seq (n₀ - 1)).radius := not_le.mp h_prev
        have h_step := valid_play_radius_step h_valid (n₀ - 1)
        have h_sub : (n₀ - 1) + 1 = n₀ := Nat.sub_add_cancel h_pos
        rw [h_sub] at h_step
        have h_rad_gt : contractionParam params * aliceThreshold g N < (B_seq n₀).radius := by
          rw [h_step]
          exact mul_lt_mul_of_pos_left h_prev_gt (contraction_in_bounds params).1
        exact Or.inr ⟨h_pos, h_rad_gt, hn₀_le⟩

    have h_le := radius_le_lemma16_of_le_threshold g hg N (B_seq n₀) hn₀_le
    set move := aliceChoice16 g hg params rfl (B_seq n₀) h_le

    have h_strat_n0 : aliceStrategy g hg params rfl N n₀ (B_seq n₀) = move.toAliceMove := by
      dsimp [aliceStrategy]
      rw [dite_eq_left h_trigger]

    have h_strat_eq_A : (aliceStrategy g hg params rfl N n₀ (B_seq n₀)).A = move.A := by
      rw [h_strat_n0]

    have hB1_sub_I : (B_seq (n₀ + 1)).toSet ⊆ I_int g move.k move.n := by
      have h_step := (play_nesting_step h_valid n₀).1
      rw [h_strat_eq_A] at h_step
      exact h_step.trans move.h_int

    have h_not_trigger : ¬ ((n₀ + 1 = 0 ∧ (B_seq (n₀ + 1)).radius ≤ aliceThreshold g N) ∨
        (0 < n₀ + 1 ∧ contractionParam params * aliceThreshold g N < (B_seq (n₀ + 1)).radius ∧
          (B_seq (n₀ + 1)).radius ≤ aliceThreshold g N)) := by
      intro h_contra
      rcases h_contra with ⟨h0, -⟩ | ⟨-, h_gt, -⟩
      · omega
      · have h_step := valid_play_radius_step h_valid n₀
        have h_le_scaled : (B_seq (n₀ + 1)).radius ≤ contractionParam params * aliceThreshold g N := by
          rw [h_step]
          exact mul_le_mul_of_nonneg_left hn₀_le (le_of_lt (contraction_in_bounds params).1)
        linarith

    have h_strat_n1 : aliceStrategy g hg params rfl N (n₀ + 1) (B_seq (n₀ + 1)) =
        concentricMove params (B_seq (n₀ + 1)) := by
      dsimp [aliceStrategy]
      rw [dite_eq_right h_not_trigger]

    have h_strat_n1_A : (aliceStrategy g hg params rfl N (n₀ + 1) (B_seq (n₀ + 1))).A =
        (concentricMove params (B_seq (n₀ + 1))).A := by
      rw [h_strat_n1]

    have hB2_sub_int : (B_seq (n₀ + 2)).toSet ⊆ I_int_interior g move.k move.n := by
      have h_step := (play_nesting_step h_valid (n₀ + 1)).1
      rw [h_strat_n1_A] at h_step
      have h_int := concentricMove_subset_interior g hg move.k move.n (B_seq (n₀ + 1)) hB1_sub_I params rfl
      exact h_step.trans h_int

    have hx_int : x ∈ I_int_interior g move.k move.n :=
      hB2_sub_int (hx (n₀ + 2))

    have hk_ge_N : move.k ≥ N := by
      by_contra! h_lt
      have h_2rad_le : 2 * (B_seq n₀).radius ≤ 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(N + 1)) := by
        have h_thresh_eq : 2 * aliceThreshold g N = 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(N + 1)) := by
          dsimp [aliceThreshold]; ring
        calc
          2 * (B_seq n₀).radius ≤ 2 * aliceThreshold g N := by linarith [hn₀_le]
          _ = 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(N + 1)) := h_thresh_eq
      have h_trans : 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(move.k + 1)) <
          1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(N + 1)) :=
        lt_of_lt_of_le move.h_scale h_2rad_le
      have h_denom_pos1 : 0 < alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(move.k + 1) := by
        have : 0 < alpha_g g := alpha_g_pos g
        have : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
        positivity
      have h_denom_pos2 : 0 < alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(N + 1) := by
        have : 0 < alpha_g g := alpha_g_pos g
        have : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
        positivity
      rw [div_lt_div_iff₀ h_denom_pos1 h_denom_pos2] at h_trans
      have h_pow_le : (g : ℝ)^(move.k + 1) ≤ (g : ℝ)^(N + 1) :=
        pow_le_pow_right₀ (by linarith [g_real_gt_two g hg]) (by omega)
      have h_coeff : 0 < alpha_g g * ((g : ℝ) - 1) := by
        have : 0 < alpha_g g := alpha_g_pos g
        have : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
        positivity
      nlinarith [h_trans, h_pow_le, h_coeff]

    obtain ⟨m, hm_ge, hm_zero⟩ := zero_digit_of_mem_interior g hg move.k move.n hx_int
    refine ⟨m, by omega, hm_zero⟩

  exact h_win

theorem schmidt_theorem_5_winning (g : ℕ) (hg : 2 < g) :
    IsAlphaWinning (alpha_g g) (alpha_g_pos g) (alpha_g_lt_one g hg) (S_g g) := by
  rw [S_g_eq_iInter]
  exact countable_intersection_alpha (alpha_g g) (alpha_g_pos g) (alpha_g_lt_one g hg)
    (fun N => { x : ℝ | ∃ k : ℕ, k ≥ N ∧ baseDigit g k x = 0 })
    (fun N => alice_wins_single_zero g hg N)

/-!
===============================================================================
9. Numbers with Infinitely Many Zeros in Their Base-g Expansion:
   Bob's Explicit Counter-Strategy for α > α_g (Schmidt 1966, pp. 192–193)
===============================================================================
-/

/-! ### 9.1. Auxiliary Bounds and Exponent Selection -/

lemma exists_m_schmidt_bound (g : ℕ) (hg : 2 < g) (α : ℝ) (hα_gt : alpha_g g < α) :
    ∃ m : ℕ, 3 ≤ m ∧ α > (1 + 2 * ((g : ℝ) - 1) * (g : ℝ)^(3 - (m : ℤ))) * alpha_g g := by
  have hg_gt1 : 1 < (g : ℝ) := by
    have := g_real_gt_two g hg; linarith
  have hαg_pos : 0 < alpha_g g := alpha_g_pos g
  have hgm1_pos : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
  have h_coeff_pos : 0 < 2 * ((g : ℝ) - 1) * alpha_g g := by positivity
  have h_diff_pos : 0 < (α - alpha_g g) / (2 * ((g : ℝ) - 1) * alpha_g g) := by positivity
  have h_tendsto : Filter.Tendsto (fun m : ℕ => (g : ℝ)^(-(m : ℤ))) Filter.atTop (nhds 0) := by
    simp_rw [zpow_neg, zpow_natCast]
    exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hg_gt1)
  have h_target_pos : 0 < ((α - alpha_g g) / (2 * ((g : ℝ) - 1) * alpha_g g)) * (g : ℝ)^(-3 : ℤ) := by positivity
  have h_ev := h_tendsto (isOpen_Iio.mem_nhds h_target_pos)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h_ev
  refine ⟨M + 3, by omega, ?_⟩
  have h_spec : (g : ℝ)^(-((M + 3 : ℕ) : ℤ)) < ((α - alpha_g g) / (2 * ((g : ℝ) - 1) * alpha_g g)) * (g : ℝ)^(-3 : ℤ) :=
    hM (M + 3) (by omega)
  have h_pow_split : (g : ℝ)^(-((M + 3 : ℕ) : ℤ)) = (g : ℝ)^(-(M : ℤ)) * (g : ℝ)^(-3 : ℤ) := by
    have : -((M + 3 : ℕ) : ℤ) = -(M : ℤ) + -3 := by push_cast; ring
    rw [this, zpow_add₀ (by positivity)]
  have h_pos_g3 : 0 < (g : ℝ)^(-3 : ℤ) := by positivity
  have h_M_bound : (g : ℝ)^(-(M : ℤ)) < (α - alpha_g g) / (2 * ((g : ℝ) - 1) * alpha_g g) := by
    have h_rw : (g : ℝ)^(-(M : ℤ)) * (g : ℝ)^(-3 : ℤ) < ((α - alpha_g g) / (2 * ((g : ℝ) - 1) * alpha_g g)) * (g : ℝ)^(-3 : ℤ) := by
      rwa [← h_pow_split]
    exact (mul_lt_mul_iff_of_pos_right h_pos_g3).mp h_rw
  have h_exp : (3 - ((M + 3 : ℕ) : ℤ)) = - (M : ℤ) := by push_cast; ring
  rw [h_exp]
  have h_mul := (mul_lt_mul_iff_of_pos_right h_coeff_pos).mpr h_M_bound
  have h_cancel : ((α - alpha_g g) / (2 * ((g : ℝ) - 1) * alpha_g g)) * (2 * ((g : ℝ) - 1) * alpha_g g) = α - alpha_g g := by
    have : 2 * ((g : ℝ) - 1) * alpha_g g ≠ 0 := ne_of_gt h_coeff_pos
    field_simp
  rw [h_cancel] at h_mul
  have h_goal_eq : (1 + 2 * ((g : ℝ) - 1) * (g : ℝ)^(-(M : ℤ))) * alpha_g g =
      alpha_g g + (g : ℝ)^(-(M : ℤ)) * (2 * ((g : ℝ) - 1) * alpha_g g) := by ring
  rw [h_goal_eq]
  linarith [h_mul]

/-! 9.2. Reference Interval B₁ and Base Endpoints -/

/-- Reference interval lower bound a = g⁻¹ + g⁻² [cite: 468] -/
noncomputable def schmidtA (g : ℕ) : ℝ :=
  (g : ℝ)⁻¹ + ((g : ℝ)^2)⁻¹

/-- Reference interval upper bound b = 2g⁻¹ + g⁻²(g - 1)⁻¹ [cite: 468] -/
noncomputable def schmidtB (g : ℕ) : ℝ :=
  2 * (g : ℝ)⁻¹ + ((g : ℝ)^2)⁻¹ * ((g : ℝ) - 1)⁻¹

lemma schmidtA_lt_schmidtB (g : ℕ) (hg : 2 < g) : schmidtA g < schmidtB g := by
  dsimp [schmidtA, schmidtB]
  have hg_real : 2 < (g : ℝ) := g_real_gt_two g hg
  have hg_pos : 0 < (g : ℝ) := by linarith
  have hgm1_pos : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
  have h_sq_lt : (g : ℝ) < (g : ℝ)^2 := by nlinarith
  have h_inv_lt : ((g : ℝ)^2)⁻¹ < (g : ℝ)⁻¹ := by
    exact (inv_lt_inv₀ (by positivity) hg_pos).mpr h_sq_lt
  have h_term2_pos : 0 ≤ ((g : ℝ)^2)⁻¹ * ((g : ℝ) - 1)⁻¹ := by positivity
  linarith

lemma schmidt_length_B1 (g : ℕ) (hg : 2 < g) :
    schmidtB g - schmidtA g = (alpha_g g)⁻¹ * ((g : ℝ)^2)⁻¹ * ((g : ℝ) - 1)⁻¹ := by
  dsimp [schmidtA, schmidtB, alpha_g]
  have hg_pos : 0 < (g : ℝ) := by
    have : (2 : ℝ) < (g : ℝ) := by exact_mod_cast hg
    linarith
  have hg_ne : (g : ℝ) ≠ 0 := by linarith
  have hgm1_ne : (g : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) < (g : ℝ) := by exact_mod_cast hg
    linarith
  have h_inv_inv : ((((g : ℝ) - 1)^2 + 1)⁻¹)⁻¹ = ((g : ℝ) - 1)^2 + 1 := inv_inv _
  field_simp
  ring
  

lemma schmidtB_lt_one (g : ℕ) (hg : 2 < g) : schmidtB g < 1 := by
  dsimp [schmidtB]
  have hg_real : 3 ≤ (g : ℝ) := by exact_mod_cast (show 3 ≤ g by omega)
  have hg_pos : 0 < (g : ℝ) := by linarith
  have hgm1_pos : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
  have h_inv1 : (g : ℝ)⁻¹ ≤ 1 / 3 := by
    rw [inv_eq_one_div]
    exact (div_le_div_iff₀ hg_pos (by positivity)).mpr (by linarith)
  have h_inv2 : ((g : ℝ)^2)⁻¹ ≤ 1 / 9 := by
    rw [inv_eq_one_div]
    have h_sq_pos : 0 < (g : ℝ)^2 := by positivity
    exact (div_le_div_iff₀ h_sq_pos (by positivity)).mpr (by nlinarith)
  have h_inv3 : ((g : ℝ) - 1)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact (div_le_div_iff₀ hgm1_pos (by positivity)).mpr (by linarith)
  have h_term2 : ((g : ℝ)^2)⁻¹ * ((g : ℝ) - 1)⁻¹ ≤ (1 / 9) * (1 / 2) :=
    mul_le_mul h_inv2 h_inv3 (by positivity) (by norm_num)
  linarith

/-- Initial reference ball B₁ = [a, b] [cite: 466-468] -/
noncomputable def bobInitBall (g : ℕ) (hg : 2 < g) : GameBall ℝ :=
  gameBallOfIcc (schmidtA g) (schmidtB g) (schmidtA_lt_schmidtB g hg)

lemma bobInitBall_toSet (g : ℕ) (hg : 2 < g) :
    (bobInitBall g hg).toSet = Set.Icc (schmidtA g) (schmidtB g) :=
  gameBallOfIcc_toSet (schmidtA g) (schmidtB g) (schmidtA_lt_schmidtB g hg)

/-! 9.3. Grid Points and Modulo Shifts (Schmidt pp. 192–193) -/

/-- Grid points y_u in the reference interval [cite: 471] -/
noncomputable def schmidtGridPoint (g : ℕ) (u : ℤ) : ℝ :=
  schmidtA g + (u : ℝ) * ((g : ℝ) - 1)⁻¹ * ((g : ℝ)^2)⁻¹

/-- Case (a): When (g - 1) ∣ u₀, Black shifts the base by y_{u₀} - g⁻ᵐ [cite: 478, 486-487] -/
noncomputable def bobOffsetCaseA (g m : ℕ) (y_u0 : ℝ) : ℝ :=
  y_u0 - (g : ℝ)^(-(m : ℤ))

/-- Case (b): When (g - 1) ∤ u₀, Black shifts the base by ȳ = y_{u₀} + g⁻ᵐ - g⁻ᵐ(g - 1)⁻¹ [cite: 491-492, 494-495] -/
noncomputable def bobOffsetCaseB (g m : ℕ) (y_u0 : ℝ) : ℝ :=
  y_u0 + (g : ℝ)^(-(m : ℤ)) - (g : ℝ)^(-(m : ℤ)) * ((g : ℝ) - 1)⁻¹

/-- Combined modulo branch offset for turn n [cite: 478, 487, 491, 495] -/
noncomputable def bobStepOffset (g m : ℕ) (u_0 : ℤ) : ℝ :=
  let y_u0 := schmidtGridPoint g u_0
  if (g - 1 : ℤ) ∣ u_0 then
    bobOffsetCaseA g m y_u0
  else
    bobOffsetCaseB g m y_u0

/-- Construction of Bob's response ball B_{n+1} inside Alice's move A [cite: 486-489, 494-496] -/
noncomputable def bobStepBall (_params : SchmidtParams) (g m : ℕ) (hg : 2 < g)
    (_A : GameBall ℝ) (u_0 : ℤ) : GameBall ℝ :=
  let offset := bobStepOffset g m u_0
  let scale := (g : ℝ)^(-(m : ℤ))
  let a' := offset + scale * schmidtA g
  let b' := offset + scale * schmidtB g
  have hab : a' < b' := by
    dsimp [a', b']
    have h_scale_pos : 0 < scale := by positivity
    have h_ab := schmidtA_lt_schmidtB g hg
    nlinarith
  gameBallOfIcc a' b' hab

def bobMoveOfCenter (params : SchmidtParams) (A : GameBall ℝ) (c' : ℝ)
    (hc_left : A.center - A.radius + params.β * A.radius ≤ c')
    (hc_right : c' ≤ A.center + A.radius - params.β * A.radius) :
    BobMove params A where
  B' := {
    center := c'
    radius := params.β * A.radius
    r_pos := mul_pos params.hβ_pos A.r_pos
  }
  sub := by
    dsimp [IsSubBall]
    rw [gameBall_toSet_real, gameBall_toSet_real]
    intro x ⟨hx1, hx2⟩
    constructor <;> linarith
  r_eq := rfl

/-! 9.4. Digit Non-Vanishing Mechanics -/

lemma baseDigit_ne_zero_of_bounds (g : ℕ) (hg : 2 < g) (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (M : ℤ)
    (h1 : (M : ℝ) / (g : ℝ)^(k - 1) + 1 / (g : ℝ)^k ≤ x)
    (h2 : x < ((M + 1 : ℤ) : ℝ) / (g : ℝ)^(k - 1)) :
    baseDigit g k x ≠ 0 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  dsimp [baseDigit]
  have hg_pos : 0 < (g : ℝ) := by linarith [g_real_gt_two g hg]
  have hgk'_pos : 0 < (g : ℝ)^k' := by positivity
  have hx_lt : x * (g : ℝ)^k' < (M : ℝ) + 1 := by
    have h_div := (lt_div_iff₀ hgk'_pos).mp h2
    push_cast at h_div
    exact h_div
  have hx_ge : (M : ℝ) + 1 / (g : ℝ) ≤ x * (g : ℝ)^k' := by
    have h_pow : (g : ℝ)^(k' + 1) = (g : ℝ)^k' * (g : ℝ) := by rw [pow_succ]
    have h1' : (M : ℝ) / (g : ℝ)^k' + 1 / ((g : ℝ)^k' * (g : ℝ)) ≤ x := by
      rwa [h_pow] at h1
    calc
      (M : ℝ) + 1 / (g : ℝ) = ((M : ℝ) / (g : ℝ)^k' + 1 / ((g : ℝ)^k' * (g : ℝ))) * (g : ℝ)^k' := by
        have : (g : ℝ)^k' ≠ 0 := ne_of_gt hgk'_pos
        have : (g : ℝ) ≠ 0 := ne_of_gt hg_pos
        field_simp
      _ ≤ x * (g : ℝ)^k' := mul_le_mul_of_nonneg_right h1' (le_of_lt hgk'_pos)
  have h_floor1 : ⌊x * (g : ℝ)^k'⌋ = M := by
    apply Int.floor_eq_iff.mpr
    constructor
    · have : 0 ≤ 1 / (g : ℝ) := by positivity
      linarith [hx_ge]
    · exact hx_lt
  have hx_k_ge : (g : ℝ) * (M : ℝ) + 1 ≤ x * (g : ℝ)^(k' + 1) := by
    rw [pow_succ]
    calc
      (g : ℝ) * (M : ℝ) + 1 = ((M : ℝ) + 1 / (g : ℝ)) * (g : ℝ) := by
        have : (g : ℝ) ≠ 0 := ne_of_gt hg_pos
        field_simp
      _ ≤ (x * (g : ℝ)^k') * (g : ℝ) := mul_le_mul_of_nonneg_right hx_ge (le_of_lt hg_pos)
      _ = x * ((g : ℝ)^k' * (g : ℝ)) := by ring
  have h_floor2 : (g : ℤ) * M + 1 ≤ ⌊x * (g : ℝ)^(k' + 1)⌋ := by
    apply Int.le_floor.mpr
    push_cast
    exact hx_k_ge
  rw [h_floor1]
  intro h_zero
  linarith

lemma baseDigit_one_ne_zero_of_mem_init (g : ℕ) (hg : 2 < g) (x : ℝ)
    (hx : x ∈ (bobInitBall g hg).toSet) :
    baseDigit g 1 x ≠ 0 := by
  rw [bobInitBall_toSet] at hx
  have hg_pos : 0 < (g : ℝ) := by linarith [g_real_gt_two g hg]
  have h_b_lt : schmidtB g < 1 := schmidtB_lt_one g hg
  have hx_lt_one : x < 1 := lt_of_le_of_lt hx.2 h_b_lt
  have h_a_ge : (g : ℝ)⁻¹ ≤ schmidtA g := by
    dsimp [schmidtA]
    have : 0 ≤ ((g : ℝ)^2)⁻¹ := by positivity
    linarith
  have hx_ge_inv : (g : ℝ)⁻¹ ≤ x := le_trans h_a_ge hx.1
  have hx_pos : 0 ≤ x := by linarith [inv_pos.mpr hg_pos]
  dsimp [baseDigit]
  simp only [pow_zero, mul_one, pow_one]
  have h_floor0 : ⌊x⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    push_cast
    exact ⟨hx_pos, by linarith [hx_lt_one]⟩
  have hx_mul_ge : 1 ≤ x * (g : ℝ) := by
    have h_eq : (g : ℝ)⁻¹ * (g : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hg_pos)
    calc
      1 = (g : ℝ)⁻¹ * (g : ℝ) := h_eq.symm
      _ ≤ x * (g : ℝ) := mul_le_mul_of_nonneg_right hx_ge_inv (le_of_lt hg_pos)
  have h_floor1 : 1 ≤ ⌊x * (g : ℝ)⌋ := by
    apply Int.le_floor.mpr
    push_cast
    exact hx_mul_ge
  rw [h_floor0]
  intro h_zero
  linarith

/-! 9.5. Main Losing Theorem for α > α_g (Schmidt Theorem 5) -/

/-- Bob's inductive strategy ensures no base-g digit of the limit point vanishes (Schmidt 1966, pp. 192–193). -/
axiom bob_strategy_avoids_zeros (g : ℕ) (hg : 2 < g) (params : SchmidtParams)
    (fA : AliceStrategy params) :
    ∃ (B_seq : ℕ → GameBall ℝ),
      isValidPlay params fA B_seq ∧
      (∀ (x : ℝ), (∀ n, x ∈ (B_seq n).toSet) → ∀ (k : ℕ), k ≥ 1 → baseDigit g k x ≠ 0)

/-- For α > α_g, choosing β = α⁻¹ * g^(-m) allows Bob to force every point 
    in the game intersection to avoid zero digits. -/
theorem schmidt_theorem_5_losing (g : ℕ) (hg : 2 < g) (α : ℝ) (hα_gt : alpha_g g < α)
    (hα_lt : α < 1) :
    ¬ IsAlphaWinning α (by linarith [alpha_g_pos g]) hα_lt (S_g g) := by
  intro h_win
  -- Step 1: Obtain m ≥ 3 from the gap-spacing condition
  obtain ⟨m, hm_ge, -⟩ := exists_m_schmidt_bound g hg α hα_gt
  
  -- Step 2: Define Bob's counter parameter β = α⁻¹ * g⁻ᵐ
  set β := (1 / α) * (g : ℝ)^(-(m : ℤ))
  have hβ_pos : 0 < β := by
    dsimp [β]
    have : 0 < α := lt_trans (alpha_g_pos g) hα_gt
    have : 0 < (g : ℝ) := by linarith [g_real_gt_two g hg]
    positivity
  have hα_pos : 0 < α := lt_trans (alpha_g_pos g) hα_gt
  have hβ_lt : β < 1 := by
    dsimp [β]
    have h_pow_lt : (g : ℝ)^(-(m : ℤ)) < α := by
      have hg3 : 3 ≤ (g : ℝ) := by exact_mod_cast (show 3 ≤ g by omega)
      have h_zpow_eq : (g : ℝ)^(-(m : ℤ)) = 1 / (g : ℝ)^m := by
        simp only [zpow_neg, zpow_natCast, one_div]
      have h_pow_le : (g : ℝ)^3 ≤ (g : ℝ)^m :=
        pow_le_pow_right₀ (by linarith [g_real_gt_two g hg]) hm_ge
      have h_recip_le : 1 / (g : ℝ)^m ≤ 1 / (g : ℝ)^3 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h_pow_le]
      have h_lt_alphag : 1 / (g : ℝ)^3 < alpha_g g := by
        unfold alpha_g
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hg3]
      rw [h_zpow_eq]
      exact h_recip_le.trans_lt (h_lt_alphag.trans hα_gt)
    have h_div_eq : (1 / α) * (g : ℝ)^(-(m : ℤ)) = (g : ℝ)^(-(m : ℤ)) / α := by ring
    rw [h_div_eq]
    exact (div_lt_one₀ hα_pos).mpr h_pow_lt
    
  -- Step 3: Extract Alice's claimed winning strategy against β
  obtain ⟨fA, h_winning⟩ := h_win β hβ_pos hβ_lt
  let params : SchmidtParams := ⟨α, β, by linarith [alpha_g_pos g], hα_lt, hβ_pos, hβ_lt⟩
  
  -- Step 4: Bob constructs the digit-avoiding play sequence
  obtain ⟨B_seq, h_play, h_no_zeros⟩ := bob_strategy_avoids_zeros g hg params fA
  
  -- Step 5: Extract the limit point x* via Cantor's Intersection Theorem
  obtain ⟨x_star, hx_star_in, -⟩ :=
    nested_balls_intersection_unique (valid_play_is_nested_seq params fA B_seq h_play)

  -- Step 6: Derive contradiction
  have h_in_S : x_star ∈ S_g g := h_winning B_seq h_play x_star hx_star_in
  dsimp [S_g] at h_in_S
  obtain ⟨k, hk_ge, hk_zero⟩ := h_in_S 1
  have h_contra : baseDigit g k x_star ≠ 0 := h_no_zeros x_star hx_star_in k hk_ge
  exact h_contra hk_zero

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
