module

public import GinibrePoincare.Analysis.GinibreHamiltonianOUReferenceProcess
public import GinibrePoincare.Analysis.GinibreHamiltonianCompactPathWeight

@[expose] public section
open Set MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
local instance ginibreOUJointPath_measurable (n : ℕ) : MeasurableSpace C(ℝ, Configuration n) := borel _
local instance ginibreOUJointPath_borel (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
theorem ginibreHamiltonianOUValue_joint_measurable (n : ℕ) (α : ℝ) (t : ℝ≥0) :
    Measurable (fun p : Configuration n × GinibreContinuousNoise n => ginibreHamiltonianOUValue n α p.1 t p.2) := by
  have hj : Continuous (fun p : C(ℝ, Configuration n) × ℝ => Real.exp ((2*α/(n : ℝ))*p.2) • p.1 p.2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).smul continuous_eval
  have hInt : Measurable (fun N : C(ℝ, Configuration n) => ∫ s in (0 : ℝ)..(t : ℝ),
      Real.exp ((2*α/(n : ℝ))*s) • N s) := by
    have hi := hj.measurable.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) (t : ℝ)))
    simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using hi.measurable
  have hInner : Measurable (fun p : Configuration n × C(ℝ, Configuration n) => p.1-(2*α/(n : ℝ)) •
      ∫ s in (0 : ℝ)..(t : ℝ), Real.exp ((2*α/(n : ℝ))*s) • p.2 s) :=
    measurable_fst.sub ((hInt.comp measurable_snd).const_smul (2*α/(n : ℝ)))
  have hV : Measurable (fun p : Configuration n × C(ℝ, Configuration n) => p.2 (t : ℝ)+
      Real.exp (-(2*α/(n : ℝ))*(t : ℝ)) • (p.1-(2*α/(n : ℝ)) •
        ∫ s in (0 : ℝ)..(t : ℝ), Real.exp ((2*α/(n : ℝ))*s) • p.2 s)) :=
    ((continuous_eval_const (t : ℝ)).measurable.comp measurable_snd).add (hInner.const_smul (Real.exp (-(2*α/(n : ℝ))*(t : ℝ))))
  have hsub : Continuous (fun p : Configuration n × GinibreContinuousNoise n => (p.1, p.2.val)) := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  exact hV.comp hsub.measurable

local instance ginibreOUJointHorizon_measurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance ginibreOUJointHorizon_borel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

def ginibreHamiltonianOUJointHorizonPath (n : ℕ) (α : ℝ) (T : ℝ≥0)
    (p : Configuration n × GinibreContinuousNoise n) :
    C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  ⟨fun t => ginibreHamiltonianOUValue n α p.1 t.val.toNNReal p.2,
    ((drivenOUPath_continuous _ p.1 _ p.2.val.continuous).comp
      (NNReal.continuous_coe.comp (continuous_real_toNNReal.comp continuous_subtype_val)))⟩

theorem ginibreHamiltonianOUJointHorizonPath_measurable (n : ℕ) (α : ℝ) (T : ℝ≥0) :
    Measurable (ginibreHamiltonianOUJointHorizonPath n α T) := by
  letI : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  exact ginibreHamiltonianOUValue_joint_measurable n α t.val.toNNReal

/-- The actual deterministic OU convolution commutes with real linear
coordinate assembly. This identifies scalar reference paths with configuration paths. -/
theorem ginibreHamiltonian_drivenOUPath_map
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (κ : ℝ) (z : E) (N : ℝ → E) (hN : Continuous N) (t : ℝ) :
    L (drivenOUPath κ z N t) = drivenOUPath κ (L z) (fun s => L (N s)) t := by
  have hi : IntervalIntegrable (fun s => Real.exp (κ*s) • N s) volume 0 t :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul hN).intervalIntegrable 0 t
  have he := L.intervalIntegral_comp_comm hi
  simp only [drivenOUPath, drivenOUCorrection, map_add, map_sub, map_smul]
  simp_rw [← L.map_smul]
  rw [he, L.map_smul]

#print axioms ginibreHamiltonian_drivenOUPath_map
#print axioms ginibreHamiltonianOUValue_joint_measurable
#print axioms ginibreHamiltonianOUJointHorizonPath_measurable
end
end GinibrePoincare
