module

public import GinibrePoincare.Analysis.GinibreHamiltonianCompactPathWeight
public import GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUProductReversal

@[expose] public section

/-! The genuine independent stationary scalar OU product, assembled into a
configuration-valued continuous path. -/
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

local instance GinibreHamiltonianConfigurationOUReference_instance1 (T : ℝ≥0) : MeasurableSpace C(Icc (0 : ℝ≥0) T,ℝ) := borel _
local instance GinibreHamiltonianConfigurationOUReference_instance2 (T : ℝ≥0) : BorelSpace C(Icc (0 : ℝ≥0) T,ℝ) := ⟨rfl⟩
local instance GinibreHamiltonianConfigurationOUReference_instance3 (n : ℕ) (T : ℝ≥0) : MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance GinibreHamiltonianConfigurationOUReference_instance4 (n : ℕ) (T : ℝ≥0) : BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩
local instance GinibreHamiltonianConfigurationOUReference_instance5 (T : ℝ≥0) : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0,⟨le_rfl,T.property⟩⟩⟩

def ginibreOURealHorizonToNNReal (T : ℝ≥0) :
    C(Icc (0 : ℝ) (T : ℝ), Icc (0 : ℝ≥0) T) :=
  ⟨fun t => ⟨t.val.toNNReal, ⟨zero_le, by
    simpa using (Real.toNNReal_le_toNNReal t.property.2)⟩⟩,
    by fun_prop⟩

def ginibreConfigurationOUAssemble (n : ℕ) (T : ℝ≥0)
    (x : (Fin n × Fin 2) → C(Icc (0 : ℝ≥0) T,ℝ)) :
    C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  ⟨fun t j => ((x (j,0) (ginibreOURealHorizonToNNReal T t) : ℂ) +
      Complex.I * (x (j,1) (ginibreOURealHorizonToNNReal T t) : ℂ)) / Real.sqrt n,
    by apply continuous_pi; intro j; fun_prop⟩

theorem ginibreConfigurationOUAssemble_measurable (n : ℕ) (T : ℝ≥0) :
    Measurable (ginibreConfigurationOUAssemble n T) := by
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  apply measurable_pi_lambda
  intro j
  unfold ginibreConfigurationOUAssemble
  exact ((((continuous_eval_const (ginibreOURealHorizonToNNReal T t)).measurable.comp
    (measurable_pi_apply (j,0))).complex_ofReal).add
    (measurable_const.mul (((continuous_eval_const (ginibreOURealHorizonToNNReal T t)).measurable.comp
      (measurable_pi_apply (j,1))).complex_ofReal))).div_const _

theorem ginibreOURealHorizonToNNReal_reverse (T : ℝ≥0)
    (t : Icc (0 : ℝ) (T : ℝ)) :
    ginibreOURealHorizonToNNReal T
      (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property t) =
    ginibreOUHorizonReverseTime T (ginibreOURealHorizonToNNReal T t) := by
  apply Subtype.ext
  apply NNReal.eq
  change (((T : ℝ) - t.val).toNNReal : ℝ) = ((T - t.val.toNNReal : ℝ≥0) : ℝ)
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr t.property.2),
    NNReal.coe_sub (by simpa using Real.toNNReal_le_toNNReal t.property.2),
    Real.coe_toNNReal _ t.property.1]

theorem ginibreConfigurationOUAssemble_reverse (n : ℕ) (T : ℝ≥0)
    (x : (Fin n × Fin 2) → C(Icc (0 : ℝ≥0) T,ℝ)) :
    ginibreConfigurationOUAssemble n T
      (fun i => (x i).comp (ginibreOUHorizonReverseTime T)) =
    (ginibreConfigurationOUAssemble n T x).comp
      (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property) := by
  ext t j
  simp only [ginibreConfigurationOUAssemble, ContinuousMap.coe_mk, ContinuousMap.comp_apply,
    ginibreOURealHorizonToNNReal_reverse]

/-- Independent copies of the actual stationary scalar Brownian-convolution OU
law, scaled to the `n`-particle Gaussian reference equilibrium. -/
def ginibreConfigurationOUReferenceLaw {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (Z : Ω → ℝ) (rate T : ℝ≥0) :
    Measure C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  (Measure.pi (fun _ : Fin n × Fin 2 =>
    P.map (ginibreBrownianOUHorizonPath B Z rate T))).map (ginibreConfigurationOUAssemble n T)

theorem ginibreConfigurationOUReferenceLaw_reverse {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1/2)) P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (rate T : ℝ≥0) :
    (ginibreConfigurationOUReferenceLaw n B P Z rate T).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
    ginibreConfigurationOUReferenceLaw n B P Z rate T := by
  let μ := P.map (ginibreBrownianOUHorizonPath B Z rate T)
  let R : C(Icc (0 : ℝ≥0) T,ℝ) → C(Icc (0 : ℝ≥0) T,ℝ) :=
    fun x => x.comp (ginibreOUHorizonReverseTime T)
  have hm := ginibreBrownianOUHorizonPath_measurable B P hB Z hZ.hasGaussianLaw hind rate T
  have hR : Measurable R := (ContinuousMap.continuous_precomp (ginibreOUHorizonReverseTime T)).measurable
  have hμ : μ.map R = μ := by
    rw [Measure.map_map hR hm]
    exact (ginibreBrownianOU_stationary_continuous_horizon_law_reversal B P hB Z hZ hind rate T).symm
  haveI : IsProbabilityMeasure μ := (by infer_instance)
  haveI : IsProbabilityMeasure (μ.map R) := (by infer_instance)
  have hpi : (Measure.pi (fun _ : Fin n × Fin 2 => μ)).map (fun x i => R (x i)) =
      Measure.pi (fun _ : Fin n × Fin 2 => μ) := by
    rw [Measure.pi_map_pi (fun _ => hR.aemeasurable)]
    simp_rw [hμ]
  have ha := ginibreConfigurationOUAssemble_measurable n T
  have hr : Measurable (fun x : C(Icc (0 : ℝ) (T : ℝ),Configuration n) =>
      x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) :=
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)).measurable
  unfold ginibreConfigurationOUReferenceLaw
  rw [Measure.map_map hr ha]
  have he : (fun x => (ginibreConfigurationOUAssemble n T x).comp
      (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
      (ginibreConfigurationOUAssemble n T) ∘ (fun x i => R (x i)) := by
    funext x
    exact (ginibreConfigurationOUAssemble_reverse n T x).symm
  change (Measure.pi (fun _ : Fin n × Fin 2 => μ)).map (fun x =>
    (ginibreConfigurationOUAssemble n T x).comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
    (Measure.pi (fun _ : Fin n × Fin 2 => μ)).map (ginibreConfigurationOUAssemble n T)
  rw [he]
  have hh : Measurable (fun x : (Fin n × Fin 2) → C(Icc (0 : ℝ≥0) T,ℝ) => fun i => R (x i)) :=
    Measurable.of_eval (fun i => hR.comp (measurable_pi_apply i))
  exact (Measure.map_map ha hh).symm.trans (congrArg (Measure.map (ginibreConfigurationOUAssemble n T)) hpi)

#print axioms ginibreConfigurationOUReferenceLaw_reverse
#print axioms ginibreConfigurationOUAssemble_measurable
#print axioms ginibreConfigurationOUAssemble_reverse
end
end GinibrePoincare
