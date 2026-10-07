module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianInnovation
public import GinibrePoincare.Analysis.GinibreBrownianIntegralBaseMartingale

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Actual predictable unit-field increments on any monotone time grid. -/
def brownianUnitGridInnovation {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (u : ℕ → Ω → EuclideanSpace ℝ ι)
    (τ : ℕ → ℝ≥0) (k : ℕ) : Ω → ℝ :=
  brownianUnitInnovation B (u k) (τ k) (τ (k+1)-τ k)

/-- The actual grid innovation is the literal unit-field inner product with
the Brownian increment between the actual adjacent grid endpoints. -/
theorem brownianUnitGridInnovation_eq {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (u : ℕ → Ω → EuclideanSpace ℝ ι)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (k : ℕ) (ω : Ω) :
    brownianUnitGridInnovation B u τ k ω =
      inner ℝ (u k ω) (WithLp.toLp 2 (fun j => B j (τ (k+1)) ω-B j (τ k) ω)) := by
  simp only [brownianUnitGridInnovation,brownianUnitInnovation,
    add_tsub_cancel_of_le (hτ (Nat.le_succ k))]

theorem brownianUnitGridInnovation_measurable_at_end
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (u : ℕ → Ω → EuclideanSpace ℝ ι) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hu : ∀ k, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (u k)) (k : ℕ) :
    @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (τ (k+1))) _
      (brownianUnitGridInnovation B u τ k) := by
  have hmU := (hu k).mono ((ginibreBrownianAugmentedFiltration B P hB).mono
    (hτ (Nat.le_succ k))) le_rfl
  have hmX : @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB (τ (k+1))) _
      (fun ω => WithLp.toLp 2 (fun j => B j (τ (k+1)) ω-B j (τ k) ω)) := by
    have hmcoord : ∀ j, @Measurable Ω ℝ
        (ginibreBrownianAugmentedFiltration B P hB (τ (k+1))) _
        (fun ω => B j (τ (k+1)) ω-B j (τ k) ω) := fun j =>
      (ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ (k+1)) _ le_rfl j).sub
        (ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ (k+1)) _
          (hτ (Nat.le_succ k)) j)
    letI : MeasurableSpace Ω := ginibreBrownianAugmentedFiltration B P hB (τ (k+1))
    apply (show Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) by fun_prop).comp
    exact measurable_pi_iff.mpr hmcoord
  have hh : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (τ (k+1))) _
      (fun ω => inner ℝ (u k ω) (WithLp.toLp 2 (fun j => B j (τ (k+1)) ω-B j (τ k) ω))) :=
    hmU.inner hmX
  convert hh using 1
  funext ω
  exact brownianUnitGridInnovation_eq B u τ hτ k ω

/-- Every chronological unit-field innovation has its genuine Gaussian law
and is independent of every variable in its actual completed past. -/
theorem brownianUnitGridInnovation_gaussian_independent
    {Ω ι A : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [MeasurableSpace A]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℕ → Ω → EuclideanSpace ℝ ι) (τ : ℕ → ℝ≥0)
    (hu : ∀ k, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (u k))
    (hunit : ∀ k ω, ‖u k ω‖ = 1) (k : ℕ) (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ Y) (i : ι) :
    HasLaw (brownianUnitGridInnovation B u τ k) (gaussianReal 0 (τ (k+1)-τ k)) P ∧
      IndepFun Y (brownianUnitGridInnovation B u τ k) P :=
  brownianUnitInnovation_gaussian_independent B P hB hind _ _ (u k) (hu k) (hunit k) Y hY i

end
end GinibrePoincare
