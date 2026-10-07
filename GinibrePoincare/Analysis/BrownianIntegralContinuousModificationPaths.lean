module

public import GinibrePoincare.Analysis.BrownianIntegralContinuousModificationSubsequence

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Turn the actual restriction of a continuous sample path into a continuous
map on the compact time interval; use the zero path on exceptional samples. -/
def continuousIntervalPathVersion {Ω : Type*} (F : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (ω : Ω) : C(Set.Icc 0 T,ℝ) := by
  classical
  exact if h : ContinuousOn (fun t => F t ω) (Set.Icc 0 T) then
    ⟨fun t => F t ω,h.domRestrict⟩ else 0

theorem continuousIntervalPathVersion_eq_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => F t ω) (Set.Icc 0 T)) :
    ∀ᵐ ω ∂P, ∀ t : Set.Icc 0 T, continuousIntervalPathVersion F T ω t = F t ω := by
  filter_upwards [hc] with ω hω
  intro t
  simp only [continuousIntervalPathVersion,dif_pos hω]
  rfl

/-- Genuine continuous martingales with terminal mean-square Cauchy estimates
have uniformly probability-Cauchy actual continuous path versions. -/
theorem continuousIntervalPathVersion_probability_cauchy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (F : ℕ → ℝ≥0 → Ω → ℝ)
    (hF : ∀ n, Martingale (F n) ℱ P) (T : ℝ≥0)
    (hT : ∀ n, MemLp (F n T) 2 P)
    (hc : ∀ n, ∀ᵐ ω ∂P, ContinuousOn (fun t => F n t ω) (Set.Icc 0 T))
    (hterm : Tendsto (fun q : ℕ × ℕ =>
      ∫ ω, (F q.2 T ω-F q.1 T ω)^2 ∂P) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun q : ℕ × ℕ => P {ω | ∃ t : Set.Icc 0 T,
      ε < |continuousIntervalPathVersion (F q.2) T ω t -
        continuousIntervalPathVersion (F q.1) T ω t|}) atTop (𝓝 0) := by
  intro ε hε
  let e : ℝ≥0 := ⟨ε,hε.le⟩
  have he : 0 < e := hε
  have ht := realMartingale_uniform_probability_cauchy P ℱ
    (fun q : ℕ × ℕ => F q.2) (fun q : ℕ × ℕ => F q.1)
    (fun q => hF q.2) (fun q => hF q.1) T (fun q => hT q.2) (fun q => hT q.1)
    (fun q => hc q.2) (fun q => hc q.1) atTop hterm e he
  convert ht using 1
  ext q
  apply measure_congr
  filter_upwards [continuousIntervalPathVersion_eq_ae P (F q.2) T (hc q.2),
    continuousIntervalPathVersion_eq_ae P (F q.1) T (hc q.1)] with ω h2 h1
  change (∃ t : Set.Icc 0 T, ε < |continuousIntervalPathVersion (F q.2) T ω t -
    continuousIntervalPathVersion (F q.1) T ω t|) =
    (∃ t ∈ Set.Icc 0 T, (e : ℝ) < ‖F q.2 t ω - F q.1 t ω‖)
  apply propext
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨t,t.property,?_⟩
    change ε < ‖F q.2 t ω - F q.1 t ω‖
    simpa [h2 t,h1 t,Real.norm_eq_abs,e,NNReal.coe_mk] using ht
  · rintro ⟨t,ht,hh⟩
    refine ⟨⟨t,ht⟩,?_⟩
    change ε < ‖F q.2 t ω - F q.1 t ω‖ at hh
    simpa [h2 ⟨t,ht⟩,h1 ⟨t,ht⟩,Real.norm_eq_abs,e,NNReal.coe_mk] using hh

/-- The path adapters match the original processes simultaneously at every
index and every time, outside one null set. -/
theorem continuousIntervalPathVersion_sequence_eq_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hc : ∀ n, ∀ᵐ ω ∂P, ContinuousOn (fun t => F n t ω) (Set.Icc 0 T)) :
    ∀ᵐ ω ∂P, ∀ n, ∀ t : Set.Icc 0 T,
      continuousIntervalPathVersion (F n) T ω t = F n t ω := by
  exact ae_all_iff.mpr (fun n => continuousIntervalPathVersion_eq_ae P (F n) T (hc n))

end
end GinibrePoincare
