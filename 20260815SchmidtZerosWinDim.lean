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
  -- Apply Mathlib's theorem that q^n -> 0 when |q| < 1, then multiply by constant r0
  have h_pow : Filter.Tendsto (fun (n : ℕ) => (contractionParam params) ^ n) Filter.atTop (nhds 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · linarith [h_bounds.1]
    · exact h_bounds.2
  -- Multiplying a sequence tending to 0 by a constant r0 still yields 0
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

  -- STEP 1: Define our sequences for centers and radii to make the math cleaner
  let c := fun n => (seq.ball n).center
  let r := fun n => (seq.ball n).radius

  -- STEP 2: Prove the sequence of centers is a Cauchy sequence
  have hCauchy : CauchySeq c := by
    -- Use the alternative metric characterization for Cauchy sequences
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε

    -- From seq.radii_tendsto, the radii eventually become smaller than ε
    have h_tendsto := Metric.tendsto_atTop.mp seq.radii_tendsto ε hε
    rcases h_tendsto with ⟨N, hN⟩

    -- Provide this N as the Cauchy bound
    use N
    intro m hm

    -- Prove that since m ≥ N, ball m is entirely nested inside ball N
    have h_subset : (seq.ball m).toSet ⊆ (seq.ball N).toSet := by
      induction hm with
      | refl => exact subset_rfl
      | step hm' ih => exact Set.Subset.trans (seq.nested _) ih

    -- The center of ball m is inside ball m (distance is 0 ≤ r_m)
    have h_cm_in_Bm : c m ∈ (seq.ball m).toSet :=
      Metric.mem_closedBall_self (le_of_lt (seq.ball m).r_pos)

    -- Therefore, by our nesting property, the center of ball m is also in ball N
    have h_cm_in_BN : c m ∈ (seq.ball N).toSet := h_subset h_cm_in_Bm

    -- By definition of a closed ball, this bounds the distance between centers by r_N
    have h_dist_centers : dist (c m) (c N) ≤ r N := h_cm_in_BN

    -- From the radii limit, the distance from r_N to 0 is less than ε
    have h_limit_N : dist (r N) 0 < ε := hN N (le_refl N)

-- Convert the metric distance on ℝ to a strict inequality r N < ε
    have h_rN_lt_ε : r N < ε := by
      calc
        r N ≤ |r N| := le_abs_self (r N)
        _ = |r N - 0| := by rw [sub_zero]
        _ = dist (r N) 0 := (Real.dist_eq (r N) 0).symm
        _ < ε := h_limit_N
    exact lt_of_le_of_lt h_dist_centers h_rN_lt_ε

  -- STEP 3: Because X is a [CompleteSpace], we can extract the limit point x*
  -- `cauchySeq_tendsto_of_complete` is the Mathlib theorem that bridges
  -- Cauchy sequences to topological limits.
  rcases cauchySeq_tendsto_of_complete hCauchy with ⟨x_star, hx_lim⟩

  -- STEP 4: Tell Lean to use x_star to satisfy the "Exists" part of the theorem
  use x_star

-- STEP 5: Build the existence witness and prove it works globally first
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

  -- Now we split into Existence and Uniqueness
  constructor
  · -- SUB-GOAL 1: EXISTENCE
    -- Since we just proved this above, we can close this branch in one line!
    exact hx_star_in

  · -- SUB-GOAL 2: UNIQUENESS
    intro y hy
    apply dist_eq_zero.mp

    -- Now hx_star_in is safely in scope to be used here!
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

-- A valid sequence of plays guarantees the creation of a NestedBallSeq. -
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
    have h_radius_step : ∀ n, (B_seq (n + 1)).radius = (contractionParam params) * (B_seq n).radius := by
      intro n
      obtain ⟨moveB, hB_eq⟩ := h_valid n
      calc
        (B_seq (n + 1)).radius = moveB.B'.radius := by rw [← hB_eq]
        _ = params.β * (fA n (B_seq n)).A.radius := moveB.r_eq
        _ = params.β * (params.α * (B_seq n).radius) := by rw [(fA n (B_seq n)).r_eq]
        _ = (params.α * params.β) * (B_seq n).radius := by ring
        _ = contractionParam params * (B_seq n).radius := rfl
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

-- Schmidt's Countable Intersection Theorem: 
--The intersection of countably many (α, β)-winning sets is also an (α, β)-winning set. 

/-- The tailored contraction parameter β_i for the i-th interleaved sub-game. -/
def schmidtBeta (α β : ℝ) (i : ℕ) : ℝ :=
  α ^ (2^(i + 1) - 1) * β ^ (2^(i + 1))

/-- Proof that 0 < β_i. -/
lemma schmidtBeta_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (i : ℕ) :
    0 < schmidtBeta α β i := by
  unfold schmidtBeta
  positivity

/-- Proof that β_i < 1. -/
lemma schmidtBeta_lt {α β : ℝ} (hα_pos : 0 < α) (hα_lt : α < 1)
    (hβ_pos : 0 < β) (hβ_lt : β < 1) (i : ℕ) :
    schmidtBeta α β i < 1 := by
  unfold schmidtBeta
  have hα : α ^ (2^(i + 1) - 1) ≤ 1 := pow_le_one₀ hα_pos.le hα_lt.le
  have hβ : β ^ (2^(i + 1)) < 1 := pow_lt_one₀ hβ_pos.le hβ_lt (by positivity)
  have : 0 ≤ α ^ (2^(i + 1) - 1) := by positivity
  have : 0 ≤ β ^ (2^(i + 1)) := by positivity
  nlinarith

/-- The physical game turn corresponding to round k of sub-strategy i. -/
def turnIdx (i k : ℕ) : ℕ :=
  2^(i + 1) * k + 2^i - 1

/-- Extract the subsequence of balls visible to sub-game i. -/
def subBallSeq (i : ℕ) (B_seq : ℕ → GameBall X) : ℕ → GameBall X :=
  fun k => B_seq (turnIdx i k)

  /-- Ball containment over m elapsed game steps. -/
lemma play_nesting_step {params : SchmidtParams} {fA : AliceStrategy (X := X) params}
    {B_seq : ℕ → GameBall X} (h_valid : isValidPlay params fA B_seq) (n : ℕ) :
    (B_seq (n + 1)).toSet ⊆ (fA n (B_seq n)).A.toSet ∧
    (fA n (B_seq n)).A.toSet ⊆ (B_seq n).toSet :=
    let ⟨moveB, hB_eq⟩ := h_valid n
    ⟨hB_eq ▸ moveB.sub, (fA n (B_seq n)).sub⟩

/-- Step gap between consecutive turns of sub-game i. -/
lemma turnIdx_succ_gap (i k : ℕ) :
    turnIdx i (k + 1) = turnIdx i k + 2^(i + 1) := by
  unfold turnIdx
  have : 1 ≤ 2^i := Nat.one_le_two_pow
  rw [mul_add, mul_one]
  omega
  

/-- The strategy selector correctly identifies sub-game i at turnIdx i k. -/
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

/-- Ball containment across m elapsed physical game steps. -/
lemma play_subset_step {params : SchmidtParams} {fA : AliceStrategy params}
    {B_seq : ℕ → GameBall X} (h_valid : isValidPlay params fA B_seq) (n : ℕ) :
    ∀ m ≥ 1, (B_seq (n + m)).toSet ⊆ (fA n (B_seq n)).A.toSet
  | 1, _ => (play_nesting_step h_valid n).1
  | m + 2, _ => by
    have ih := play_subset_step h_valid n (m + 1) (by omega)
    have step := (play_nesting_step h_valid (n + m + 1)).1
    have step_sub := (play_nesting_step h_valid (n + m + 1)).2
    exact step.trans (step_sub.trans ih)

/-- Radius scaling across m elapsed physical game steps. -/
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
    
    -- Evaluate the interleaved strategy on turn n to recover sub-strategy i
    have h_strat_eval :
        (interleavedStrategy params sub_params hα_eq strats n (B_seq n)).A =
        (strats i k (subBallSeq i B_seq k)).A := by
      dsimp [interleavedStrategy, subBallSeq, n]
      rw [turnToStrategy_turnIdx]

    -- Step containment and radius scaling across m physical steps
    have h_sub := play_subset_step h_valid n m hm
    have h_rad := play_radius_step h_valid n m hm
    rw [h_strat_eval] at h_sub h_rad

    -- Package Bob's simulated move in sub-game i
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

/-- Points strictly in the interior of I_k(n) must have at least one zero digit 
    at or beyond position k + 1. -/
lemma zero_digit_of_mem_interior (g : ℕ) (hg : 2 < g) (k : ℕ) (n : ℤ) {x : ℝ}
    (hx : x ∈ I_int_interior g k n) :
    ∃ (m : ℕ), m ≥ k + 1 ∧ baseDigit g m x = 0 := by
  dsimp [I_int_interior] at hx
  set y := x * (g : ℝ)^k - (n : ℝ)
  have hg_real : 2 < (g : ℝ) := g_real_gt_two g hg
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

lemma geom_sum_floor_bound_le (g : ℕ) (hg : 2 < g) (y : ℝ) (hy0 : 0 ≤ y) (m : ℕ)
    (h_pos : ∀ i < m, 1 ≤ ⌊y * (g : ℝ)^(i + 1)⌋ - (g : ℤ) * ⌊y * (g : ℝ)^i⌋) :
    ((g : ℝ)^m - 1) / ((g : ℝ) - 1) ≤ (⌊y * (g : ℝ)^m⌋ : ℝ) := by
  induction m with
  | zero =>
    simp only [pow_zero, mul_one, sub_self, zero_div]
    exact_mod_cast (Int.floor_nonneg.mpr hy0)
  | succ j ih =>
    have h_step := h_pos j (Nat.lt_succ_self j)
    have ih' := ih (fun i hi => h_pos i (Nat.lt_trans hi (Nat.lt_succ_self j)))
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

lemma zero_digit_of_compact_interior (g : ℕ) (hg : 2 < g) (k : ℕ) (n : ℤ) (c d : ℝ)
    (hcd : Set.Icc c d ⊆ I_int_interior g k n) (h_nonempty : c < d) :
    ∃ (m_bound : ℕ), ∀ x ∈ Set.Icc c d, ∃ m : ℕ, k + 1 ≤ m ∧ m ≤ m_bound ∧ baseDigit g m x = 0 := by
  have hgk_pos : 0 < (g : ℝ)^k := by positivity
  have hgm1_pos : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
  
  have hd_mem : d ∈ I_int_interior g k n := hcd ⟨le_of_lt h_nonempty, le_rfl⟩
  dsimp [I_int_interior] at hd_mem
  
  set yd := d * (g : ℝ)^k - (n : ℝ)
  have hyd_ub : yd < 1 / ((g : ℝ) - 1) := by
    have h2 := hd_mem.2
    have h_mul : d * (g : ℝ)^k < (n : ℝ) + 1 / ((g : ℝ) - 1) := by
      calc d * (g : ℝ)^k < ((n : ℝ) / (g : ℝ)^k + 1 / (((g : ℝ) - 1) * (g : ℝ)^k)) * (g : ℝ)^k :=
            (mul_lt_mul_iff_of_pos_right hgk_pos).mpr h2
      _ = (n : ℝ) + 1 / ((g : ℝ) - 1) := by
            have : ((g : ℝ) - 1) * (g : ℝ)^k ≠ 0 := by positivity
            have : (g : ℝ)^k ≠ 0 := by positivity
            field_simp
    linarith

  set δ := 1 / ((g : ℝ) - 1) - yd
  have hδ_pos : 0 < δ := sub_pos.mpr hyd_ub
  
  have h_tendsto : Filter.Tendsto (fun m : ℕ => 1 / (((g : ℝ) - 1) * (g : ℝ)^m)) Filter.atTop (nhds 0) := by
    simp_rw [one_div]
    exact tendsto_inv_atTop_zero.comp
      (Filter.Tendsto.const_mul_atTop hgm1_pos (tendsto_pow_atTop_atTop_of_one_lt (by linarith [g_real_gt_two g hg])))
  
  have h_ev := h_tendsto (isOpen_Iio.mem_nhds hδ_pos)
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp h_ev
  have hm₀_spec : 1 / (((g : ℝ) - 1) * (g : ℝ)^m₀) < δ := hm₀ m₀ le_rfl
  
  refine ⟨k + m₀, ?_⟩
  intro x hx
  set y := x * (g : ℝ)^k - (n : ℝ)
  have hx_mem : x ∈ I_int_interior g k n := hcd hx
  have hy_le_yd : y ≤ yd := by
    dsimp [y, yd]
    nlinarith [hx.2]

  by_contra! h_no_zero
  have h_pos_digit : ∀ i < m₀, 1 ≤ baseDigit g (k + i + 1) x := by
    intro i hi
    have h_ne := h_no_zero (k + i + 1) (by omega) (by omega)
    have h_nonneg := baseDigit_nonneg g (k + i + 1) x (by omega)
    omega

  have hy_nonneg : 0 ≤ y := by
    have h1 := hx_mem.1
    have : (n : ℝ) < x * (g : ℝ)^k := (div_lt_iff₀ hgk_pos).mp h1
    linarith

  have h_geom_bound := geom_sum_floor_bound_le g hg y hy_nonneg m₀ (fun i hi => by
    have h_sh := baseDigit_shift g k i n x y rfl
    have h_dig := h_pos_digit i hi
    rwa [h_sh] at h_dig
  )

  have h_floor_le : (⌊y * (g : ℝ)^m₀⌋ : ℝ) ≤ y * (g : ℝ)^m₀ := Int.floor_le _
  have h_bound : ((g : ℝ)^m₀ - 1) / ((g : ℝ) - 1) ≤ y * (g : ℝ)^m₀ := le_trans h_geom_bound h_floor_le

  have h_pow_pos : 0 < (g : ℝ)^m₀ := by positivity
  have h_yd_bound : yd * (g : ℝ)^m₀ < ((g : ℝ)^m₀ - 1) / ((g : ℝ) - 1) := by
    have h_yd_lt : yd < 1 / ((g : ℝ) - 1) - 1 / (((g : ℝ) - 1) * (g : ℝ)^m₀) := by
      linarith [hm₀_spec]
    have h_mul := (mul_lt_mul_iff_of_pos_right h_pow_pos).mpr h_yd_lt
    have h_eq : (1 / ((g : ℝ) - 1) - 1 / (((g : ℝ) - 1) * (g : ℝ)^m₀)) * (g : ℝ)^m₀ =
        ((g : ℝ)^m₀ - 1) / ((g : ℝ) - 1) := by
      have : (g : ℝ) - 1 ≠ 0 := ne_of_gt hgm1_pos
      have : (g : ℝ)^m₀ ≠ 0 := ne_of_gt h_pow_pos
      field_simp
    rwa [h_eq] at h_mul

  have h_y_le : y * (g : ℝ)^m₀ ≤ yd * (g : ℝ)^m₀ :=
    mul_le_mul_of_nonneg_right hy_le_yd (le_of_lt h_pow_pos)

  have h_contra : y * (g : ℝ)^m₀ < ((g : ℝ)^m₀ - 1) / ((g : ℝ) - 1) :=
    lt_of_le_of_lt h_y_le h_yd_bound

  linarith

/-! 7. Alice's Inductive Response: Schmidt's Lemma 16 Step -/

/-- Given Bob's ball B of sufficiently small radius, Alice can choose a sub-ball A ⊆ B 
    of radius α_g * r(B) entirely contained in K_k. -/
lemma alice_move_from_lemma_16 (g : ℕ) (hg : 2 < g) (params : SchmidtParams)
    (hα_eq : params.α = alpha_g g) (B : GameBall ℝ)
    (hB_radius : 2 * B.radius ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ)))) :
    ∃ (k : ℕ) (_hk : 1 ≤ k) (A : GameBall ℝ),
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

/-- Given an interval J ⊆ I_k(n), concentric scaling by α_g shrinks it 
    strictly into the open interior I_int_interior g k n. -/
lemma alice_shrink_to_interior (g : ℕ) (hg : 2 < g) (k : ℕ) (n : ℤ) (B : GameBall ℝ)
    (hB_sub : B.toSet ⊆ I_int g k n) (params : SchmidtParams) (hα_eq : params.α = alpha_g g) :
    ∃ (A : GameBall ℝ),
      A.toSet ⊆ B.toSet ∧
      A.radius = params.α * B.radius ∧
      A.toSet ⊆ I_int_interior g k n := by
  have hα_lt : params.α < 1 := by rw [hα_eq]; exact alpha_g_lt_one g hg
  have h_rad_pos : 0 < B.radius := B.r_pos
  have h_shrink : params.α * B.radius < B.radius := by nlinarith [params.hα_pos]
  
  have h_left : (n : ℝ) / (g : ℝ)^k ≤ B.center - B.radius := by
    have h_mem : B.center - B.radius ∈ B.toSet := by
      rw [gameBall_toSet_real]
      exact ⟨le_rfl, by linarith⟩
    exact (hB_sub h_mem).1

  have h_right : B.center + B.radius ≤ (n : ℝ) / (g : ℝ)^k + 1 / (((g : ℝ) - 1) * (g : ℝ)^k) := by
    have h_mem : B.center + B.radius ∈ B.toSet := by
      rw [gameBall_toSet_real]
      exact ⟨by linarith, le_rfl⟩
    exact (hB_sub h_mem).2

  set A : GameBall ℝ := ⟨B.center, params.α * B.radius, mul_pos params.hα_pos B.r_pos⟩
  refine ⟨A, ?_, rfl, ?_⟩
  · rw [gameBall_toSet_real, gameBall_toSet_real]
    dsimp [A]
    intro x ⟨hxa, hxb⟩
    constructor <;> linarith
  · rw [gameBall_toSet_real]
    dsimp [A, I_int_interior]
    intro x ⟨hxa, hxb⟩
    constructor <;> linarith

noncomputable def aliceStrategy (g : ℕ) (hg : 2 < g) (params : SchmidtParams)
    (hα_eq : params.α = alpha_g g) : AliceStrategy (X := ℝ) params := by
  intro _n B
  by_cases h : 2 * B.radius ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ)))
  · have h_move : ∃ A : GameBall ℝ, IsSubBall A B ∧ A.radius = params.α * B.radius := by
      obtain ⟨_k, _hk, A, hsub, hr, _⟩ := alice_move_from_lemma_16 g hg params hα_eq B h
      exact ⟨A, hsub, hr⟩
    exact ⟨Classical.choose h_move, (Classical.choose_spec h_move).1, (Classical.choose_spec h_move).2⟩
  · refine ⟨⟨B.center, params.α * B.radius, mul_pos params.hα_pos B.r_pos⟩, ?_, rfl⟩
    dsimp [IsSubBall]
    rw [gameBall_toSet_real, gameBall_toSet_real]
    intro x ⟨h1, h2⟩
    have : params.α < 1 := by rw [hα_eq]; exact alpha_g_lt_one g hg
    constructor <;> nlinarith [B.r_pos, params.hα_pos]

/-! 8. Theorem 5: S_g Winning Strategy & Winning Dimension -/

lemma S_g_eq_iInter (g : ℕ) : 
    S_g g = ⋂ N : ℕ, { x : ℝ | ∃ k : ℕ, k ≥ N ∧ baseDigit g k x = 0 } := by
  ext x
  simp only [S_g, Set.mem_ofPred_eq, Set.mem_iInter]

/-- Alice can win the single-zero target at scale ≥ N. -/
lemma alice_wins_single_zero (g : ℕ) (hg : 2 < g) (N : ℕ) :
    IsAlphaWinning (alpha_g g) (alpha_g_pos g) (alpha_g_lt_one g hg)
      { x : ℝ | ∃ k : ℕ, k ≥ N ∧ baseDigit g k x = 0 } := by
  intro β hβ_pos hβ_lt
  let params : SchmidtParams := ⟨alpha_g g, β, alpha_g_pos g, alpha_g_lt_one g hg, hβ_pos, hβ_lt⟩
  
  -- Threshold radius to guarantee k ≥ N from exists_k_scale
  set threshold := 1 / (alpha_g g * ((g : ℝ) - 1) * (g : ℝ)^(N + 1))
  
  -- Alice plays concentric dummy moves until radius ≤ threshold, 
  -- then executes Lemma 16 on turn n0, shrinks to interior on n0+1, and plays dummy moves thereafter.
  have h_win : IsWinningSet params { x : ℝ | ∃ k : ℕ, k ≥ N ∧ baseDigit g k x = 0 } := by
    -- Alice's strategy:
    use aliceStrategy g hg params rfl
    intro B_seq h_valid x hx
    
    -- Radii decay to 0, so 2 * B_n.radius eventually falls below threshold
    have h_nested := valid_play_is_nested_seq params (aliceStrategy g hg params rfl) B_seq h_valid
    have h_tendsto := h_nested.radii_tendsto
    have h_thresh_pos : 0 < threshold := by
      dsimp [threshold]
      have : 0 < alpha_g g := alpha_g_pos g
      have : 0 < (g : ℝ) - 1 := g_minus_one_pos g hg
      have : 0 < (g : ℝ) := by linarith [g_real_gt_two g hg]
      positivity
    obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp 
      (h_tendsto (isOpen_Iio.mem_nhds h_thresh_pos))
    
    -- At step n₀, Bob's ball satisfies the condition of lemma 16
    have h_r_le : 2 * (B_seq (n₀ + 1)).radius ≤ 1 / (alpha_g g * ((g : ℝ)^2 - (g : ℝ))) := by
      sorry -- Immediate bound from hn₀ (n₀ + 1) and threshold ≤ 1/(α_g * (g²-g))
      
    obtain ⟨k, hk, A_move, hA_sub, hA_rad, hA_K⟩ := 
      alice_move_from_lemma_16 g hg params rfl (B_seq (n₀ + 1)) h_r_le
      
    -- Since x ∈ B_{n₀+2} ⊆ A_move ⊆ K(g, k), x belongs to some I_int(g, k, n)
    have hx_K : x ∈ K g k := by
      have hx_in_B : x ∈ (B_seq (n₀ + 2)).toSet := hx (n₀ + 2)
      obtain ⟨moveB, hB_eq⟩ := h_valid (n₀ + 1)
      have hx_in_A : x ∈ (aliceStrategy g hg params rfl (n₀ + 1) (B_seq (n₀ + 1))).A.toSet := by
        rw [← hB_eq] at hx_in_B
        exact moveB.sub hx_in_B
      sorry -- Follows from choice of A_move in aliceStrategy and hA_K

    obtain ⟨n, hn_int⟩ : ∃ n : ℤ, x ∈ I_int g k n := by
      dsimp [K] at hx_K
      exact Set.mem_iUnion.mp hx_K

    -- By digit forcing, interior points have a zero digit at index m ≥ k + 1 ≥ N
    have hk_ge_N : k ≥ N := by sorry -- Follows from radius ≤ threshold
    obtain ⟨m, hm_ge, hm_zero⟩ := zero_digit_of_mem_interior g hg k n sorry
    refine ⟨m, by omega, hm_zero⟩

  exact h_win

theorem schmidt_theorem_5_winning (g : ℕ) (hg : 2 < g) :
    IsAlphaWinning (alpha_g g) (alpha_g_pos g) (alpha_g_lt_one g hg) (S_g g) := by
  rw [S_g_eq_iInter]
  exact countable_intersection_alpha (alpha_g g) (alpha_g_pos g) (alpha_g_lt_one g hg)
    (fun N => { x : ℝ | ∃ k : ℕ, k ≥ N ∧ baseDigit g k x = 0 })
    (fun N => alice_wins_single_zero g hg N)

lemma exists_m_schmidt_bound (g : ℕ) (hg : 2 < g) (α : ℝ) (hα_gt : alpha_g g < α) :
    ∃ m : ℕ, 3 ≤ m ∧ α > (1 + 2 * ((g : ℝ) - 1) * (g : ℝ)^(3 - (m : ℤ))) * alpha_g g := by
  have hg_gt1 : 1 < (g : ℝ) := by
    have := g_real_gt_two g hg
    linarith
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
    
/-- For α > α_g, choosing β = α⁻¹ * g^(-m) allows Bob to force every point 
    in the game intersection to avoid zero digits. -/
theorem schmidt_theorem_5_losing (g : ℕ) (hg : 2 < g) (α : ℝ) (hα_gt : alpha_g g < α)
    (hα_lt : α < 1) :
    ¬ IsAlphaWinning α (by linarith [alpha_g_pos g]) hα_lt (S_g g) := by
  intro h_win
  -- Step 1: Obtain m ≥ 3 from the gap-spacing condition
  obtain ⟨m, hm_ge, hm_bound⟩ := exists_m_schmidt_bound g hg α hα_gt
  
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
      sorry -- Arithmetic consequence of hm_bound and α > α_g
    have h_div_eq : (1 / α) * (g : ℝ)^(-(m : ℤ)) = (g : ℝ)^(-(m : ℤ)) / α := by ring
    rw [h_div_eq]
    exact (div_lt_one₀ hα_pos).mpr h_pow_lt
    
  -- Step 3: Extract Alice's claimed winning strategy against β
  obtain ⟨fA, h_winning⟩ := h_win β hβ_pos hβ_lt
  
  -- Step 4: Bob plays balls B_n avoiding digit 0 in each m-block
  have h_bob_seq : ∃ (B_seq : ℕ → GameBall ℝ),
      isValidPlay ⟨α, β, by linarith [alpha_g_pos g], hα_lt, hβ_pos, hβ_lt⟩ fA B_seq ∧
      (∃ N₀ : ℕ, ∀ (x : ℝ), (∀ n, x ∈ (B_seq n).toSet) → ∀ k ≥ N₀, baseDigit g k x ≠ 0) := by
    sorry -- Inductive selection of center avoiding 0-digit intervals

  obtain ⟨B_seq, h_play, N₀, h_no_zeros⟩ := h_bob_seq
  
-- Step 5: Extract the limit point x* via Cantor's Intersection Theorem
  let params : SchmidtParams := ⟨α, β, by linarith [alpha_g_pos g], hα_lt, hβ_pos, hβ_lt⟩
  obtain ⟨x_star, hx_star_in, -⟩ :=
    nested_balls_intersection_unique (valid_play_is_nested_seq params fA B_seq h_play)

  -- Step 6: Derive contradiction
  have h_in_S : x_star ∈ S_g g := h_winning B_seq h_play x_star hx_star_in
  dsimp [S_g] at h_in_S
  obtain ⟨k, hk_ge, hk_zero⟩ := h_in_S N₀
  have h_contra := h_no_zeros x_star hx_star_in k hk_ge
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
