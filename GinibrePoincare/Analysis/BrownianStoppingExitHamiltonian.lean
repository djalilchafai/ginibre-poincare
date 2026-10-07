module

public import GinibrePoincare.Analysis.BrownianStoppingExitLyapunov
public import GinibrePoincare.Analysis.GinibreHamiltonianGenerator
public import GinibrePoincare.Analysis.GinibreHamiltonianCoercivity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! Actual Ginibre Hamiltonian exit estimate from a genuine stopped Itô martingale. -/
open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreHamiltonian_stopped_exit_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N ℱ μ) (hcont : ∀ᵐ ω ∂μ, Continuous (fun t => N t ω))
    (hN0 : N 0 =ᵐ[μ] 0) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T)
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 ≤ α)
    (X : ℝ → Ω → Configuration n) (z₀ : Configuration n)
    (hfree : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc (0 : ℝ) (σ ω : ℝ), CollisionFree (X t ω))
    (hLg : ∀ᵐ ω ∂μ, IntervalIntegrable
      (fun t => ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n) (X t ω))
      volume 0 (σ ω : ℝ))
    (hA : Integrable (fun ω => ∫ t in (0 : ℝ)..(σ ω : ℝ),
      ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n) (X t ω)) μ)
    (hIto : (fun ω => ginibreHamiltonian n (X (σ ω : ℝ) ω)) =ᵐ[μ]
      (fun ω => ginibreHamiltonian n z₀ + N (σ ω) ω +
        ∫ t in (0 : ℝ)..(σ ω : ℝ),
          ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n) (X t ω)))
    (R : ℝ) (hR : -ginibreHamiltonianLowerBoundConstant n < R) :
    μ.real {ω | R ≤ ginibreHamiltonian n (X (σ ω : ℝ) ω)} ≤
      (ginibreHamiltonian n z₀ + ginibreHamiltonianLowerBoundConstant n + 4*α*(T : ℝ))/
        (R+ginibreHamiltonianLowerBoundConstant n) := by
  have hupper : (fun ω => ∫ t in (0 : ℝ)..(σ ω : ℝ),
      ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n) (X t ω)) ≤ᵐ[μ]
      (fun _ => (4*α)*(T : ℝ)) := by
    filter_upwards [hfree, hLg] with ω hf hi
    have h := intervalIntegral.integral_mono_on (σ ω).property hi
      (intervalIntegrable_const (c := 4*α))
      (fun t ht => ginibreRealPaperSpeedGenerator_hamiltonian_le hn α hα (X t ω) (hf t ht))
    have ht : (σ ω : ℝ) ≤ (T : ℝ) := hσT ω
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    apply h.trans
    calc (σ ω : ℝ)*(4*α) = (4*α)*(σ ω : ℝ) := mul_comm _ _
         _ ≤ (4*α)*(T : ℝ) := mul_le_mul_of_nonneg_left ht (by positivity)
  have hlower : (fun _ : Ω => -ginibreHamiltonianLowerBoundConstant n) ≤ᵐ[μ]
      (fun ω => ginibreHamiltonian n (X (σ ω : ℝ) ω)) := by
    filter_upwards [hfree] with ω hf
    exact ginibreHamiltonian_bounded_below hn _ (hf _ ⟨(σ ω).property, le_rfl⟩)
  simpa only [sub_neg_eq_add] using continuous_stopped_lyapunov_exit_bound hN hcont hN0
    hσ hσT hA hIto hupper hlower hR

end
end GinibrePoincare
