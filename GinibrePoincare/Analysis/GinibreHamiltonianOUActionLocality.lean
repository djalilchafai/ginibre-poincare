module

public import GinibrePoincare.Analysis.GinibreHamiltonianOUJointPath
public import GinibrePoincare.Analysis.GinibreHamiltonianOUActionWeight

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
local instance ginibreActionLocalityPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ),Configuration n) := borel _
local instance ginibreActionLocalityPathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ),Configuration n) := ⟨rfl⟩

theorem ginibreHamiltonian_gradient_action_congr (n : ℕ) (α T : ℝ) (hT : 0 ≤ T)
    (x y : ℝ → Configuration n) (hxy : EqOn x y (Icc 0 T)) :
    ginibreHamiltonianGradientPathWeight n α T x = ginibreHamiltonianGradientPathWeight n α T y := by
  have hi : (∫ s in (0 : ℝ)..T, ginibreHamiltonianGradientNormSq n (x s)) =
      ∫ s in (0 : ℝ)..T, ginibreHamiltonianGradientNormSq n (y s) :=
    intervalIntegral.integral_congr (fun s hs => congrArg _ (hxy (by simpa [uIcc_of_le hT] using hs)))
  simp only [ginibreHamiltonianGradientPathWeight,ginibreHamiltonianPathEnergy,
    hxy (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
    hxy (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩),hi]

theorem ginibreHamiltonian_quadratic_action_congr (n : ℕ) (α T : ℝ) (hT : 0 ≤ T)
    (x y : ℝ → Configuration n) (hxy : EqOn x y (Icc 0 T)) :
    ginibreQuadraticGradientPathWeight n α T x = ginibreQuadraticGradientPathWeight n α T y := by
  have hi : (∫ s in (0 : ℝ)..T, configurationNormSq (x s)) =
      ∫ s in (0 : ℝ)..T, configurationNormSq (y s) :=
    intervalIntegral.integral_congr (fun s hs => congrArg _ (hxy (by simpa [uIcc_of_le hT] using hs)))
  simp only [ginibreQuadraticGradientPathWeight,
    hxy (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
    hxy (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩),hi]

theorem ginibreHamiltonianOUActionWeight_of_agrees (n : ℕ) (α T : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T,Configuration n)) (y : ℝ → Configuration n)
    (hy : ∀ s (hs : s ∈ Icc 0 T), y s = x ⟨s,hs⟩) :
    ginibreHamiltonianGradientPathWeight n α T y / ginibreQuadraticGradientPathWeight n α T y =
      ginibreHamiltonianOUActionWeight n α T hT x := by
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  have he : EqOn y (ContinuousMap.IccExtendCM x) (Icc 0 T) := by
    intro s hs
    rw [hy s hs,ContinuousMap.IccExtendCM_of_mem hs]
  unfold ginibreHamiltonianOUActionWeight ginibreHamiltonianCompactPathWeight
  rw [ginibreHamiltonian_gradient_action_congr n α T hT y _ he,
    ginibreHamiltonian_quadratic_action_congr n α T hT y _ he]

def ginibreHamiltonianOUReferenceHorizon {Ω : Type*} (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    C(Icc (0 : ℝ) (T : ℝ),Configuration n) :=
  ginibreHamiltonianOUJointHorizonPath n α T (z,ginibreBrownianFullContinuousNoise n B α ω)

theorem ginibreHamiltonianOUReferenceHorizon_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    Measurable (ginibreHamiltonianOUReferenceHorizon n α z B T) :=
  (ginibreHamiltonianOUJointHorizonPath_measurable n α T).comp
    (measurable_const.prodMk (ginibreBrownianFullContinuousNoise_measurable n B P hB α))

theorem ginibreHamiltonianOUReference_action_of_prefix {Ω : Type*}
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω)
    (Y : ℝ≥0 → Ω → Configuration n)
    (hY : ∀ t ≤ T, Y t ω = ginibreHamiltonianOUReferenceProcess n α z B t ω) :
    ginibreHamiltonianGradientPathWeight n α (T : ℝ) (fun s => Y s.toNNReal ω) /
      ginibreQuadraticGradientPathWeight n α (T : ℝ) (fun s => Y s.toNNReal ω) =
      ginibreHamiltonianOUActionWeight n α (T : ℝ) T.property
        (ginibreHamiltonianOUReferenceHorizon n α z B T ω) := by
  apply ginibreHamiltonianOUActionWeight_of_agrees
  intro s hs
  exact hY s.toNNReal (by simpa using Real.toNNReal_le_toNNReal hs.2)

#print axioms ginibreHamiltonianOUReference_action_of_prefix
#print axioms ginibreHamiltonianOUReferenceHorizon_measurable
end
end GinibrePoincare
