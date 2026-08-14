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

abbrev TargetSet (X : Type*) := Set X

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

    /-- Schmidt's Countable Intersection Theorem:
    The intersection of countably many (α, β)-winning sets is also an (α, β)-winning set. -/
def IsAlphaWinning (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1) (S : Set X) : Prop :=
  ∀ (β : ℝ) (hβ_pos : 0 < β) (hβ_lt : β < 1),
    IsWinningSet ⟨α, β, hα_pos, hα_lt, hβ_pos, hβ_lt⟩ S

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
