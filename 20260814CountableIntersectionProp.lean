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

/-- Combine a countable sequence of Alice strategies into a single interleaved strategy. -/
def interleavedStrategy {X : Type*} [MetricSpace X] (params : SchmidtParams)
    (strats : ℕ → AliceStrategy (X := X) params) : AliceStrategy (X := X) params :=
  fun n B =>
    let (i, k) := turnToStrategy n
    strats i k B

    /-- Schmidt's Countable Intersection Theorem:
    The intersection of countably many (α, β)-winning sets is also an (α, β)-winning set. -/
def IsAlphaWinning (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1) (S : Set X) : Prop :=
  ∀ (β : ℝ) (hβ_pos : 0 < β) (hβ_lt : β < 1),
    IsWinningSet ⟨α, β, hα_pos, hα_lt, hβ_pos, hβ_lt⟩ S

theorem countable_intersection_alpha [CompleteSpace X]
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (S : ℕ → Set X) (h_win : ∀ i, IsAlphaWinning α hα_pos hα_lt (S i)) :
    IsAlphaWinning α hα_pos hα_lt (⋂ i, S i) := by
  intro β hβ_pos hβ_lt
  -- Now you can instantiate each S i with the exact β_i required by your interleaving schedule
  sorry
