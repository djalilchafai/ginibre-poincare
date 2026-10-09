module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsLSIObservables
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω]

lemma bakryEmery_compactObservable_bound (g : E → ℝ) (hg : Continuous g)
    (hs : HasCompactSupport g) : ∃ C : ℝ, ∀ x, |g x| ≤ C := by
  obtain ⟨C, hC⟩ := (hs.isCompact_range hg).exists_bound_of_continuousOn continuous_id.continuousOn
  exact ⟨C, fun x => by simpa only [id_eq, Real.norm_eq_abs] using hC (g x) (mem_range_self x)⟩

/-- Equilibrium closure for a concrete synchronous coupling. This is the
limit lemma; the stationary marginal and finite-time inequalities are supplied
by the separately constructed stochastic laws, and are not assumed in the
final Gibbs theorem. -/
theorem bakryEmery_stationaryCoupling_square_lsi_limit
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f)
    (X Y : ℕ → Ω → E) (hX : ∀ n, AEMeasurable (X n) P)
    (hY : ∀ n, HasLaw (Y n) ν P)
    (hXY : ∀ᵐ ω ∂P, Tendsto (fun n => dist (X n ω) (Y n ω)) atTop (nhds 0))
    (c : ℝ) (hineq : ∀ n, squareEntropy P (fun ω => f (X n ω)) ≤
      c * ∫ ω, ‖gradient f (X n ω)‖^2 ∂P) :
    squareEntropy ν f ≤ c * ∫ x, ‖gradient f x‖^2 ∂ν := by
  have hgrad : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hgs : HasCompactSupport (gradient f) :=
    (hs.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (map_zero _)
  have hs2 := hs.comp_left (g := fun x : ℝ => x^2) (by simp)
  have hsl := hs.comp_left (g := fun x : ℝ => x^2*Real.log (x^2)) (by simp)
  have hse := hgs.comp_left (g := fun x : E => ‖x‖^2) (by simp)
  obtain ⟨Cs, hCs⟩ := bakryEmery_compactObservable_bound (fun x => f x^2) (hf.continuous.pow 2) hs2
  obtain ⟨Cl, hCl⟩ := bakryEmery_compactObservable_bound (fun x => f x^2*Real.log (f x^2))
    (continuous_square_mul_log hf.continuous) hsl
  obtain ⟨Ce, hCe⟩ := bakryEmery_compactObservable_bound (fun x => ‖gradient f x‖^2)
    (hgrad.norm.pow 2) hse
  have huc := bakryEmery_compactSquareEntropy_uniformContinuous f hf.continuous hs
  have hmass := bakryEmery_stationaryCoupling_expectation_tendsto P ν
    (fun x => f x^2) huc.1 Cs hCs X Y hX hY hXY
  have hlog := bakryEmery_stationaryCoupling_expectation_tendsto P ν
    (fun x => f x^2*Real.log (f x^2)) huc.2 Cl hCl X Y hX hY hXY
  have henergy := bakryEmery_stationaryCoupling_expectation_tendsto P ν
    (fun x => ‖gradient f x‖^2) (bakryEmery_compactGradientEnergy_uniformContinuous f hf hs)
    Ce hCe X Y hX hY hXY
  have hent : Tendsto (fun n => squareEntropy P (fun ω => f (X n ω))) atTop
      (nhds (squareEntropy ν f)) := by
    exact hlog.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hmass)
  exact le_of_tendsto_of_tendsto' hent (henergy.const_mul c) hineq

#print axioms bakryEmery_compactObservable_bound
#print axioms bakryEmery_stationaryCoupling_square_lsi_limit
end
end GinibrePoincare
