module

public import GinibrePoincare.Analysis.NonQuadraticAlternatingMonomialClosure
public import GinibrePoincare.Analysis.NonQuadraticPiTensorConvolution

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false

theorem planarPiWeightedMonomialVector_coeFn {d : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (F : PlanarPiLebesgueL2 d) (hF : F ∈ planarPiWeightedMonomialVectors d n V) :
    ∃ p : Fin d → ℕ, ∃ c : ℂ,
      (F : Configuration d → ℂ) =ᵐ[volume]
        (fun x => c * (∏ i, x i ^ p i) * piPotentialHalfWeight d n V x) := by
  obtain ⟨u, hu, rfl⟩ := hF
  choose p c hm he using hu
  have hscalar (i : Fin d) : (u i : ℂ → ℂ) =ᵐ[volume]
      (fun z => c i * z ^ p i * planarPotentialHalfWeight n V z) := by
    rw [← he i]
    exact (hm i).coeFn_toLp
  have hall : ∀ᵐ x ∂Measure.pi (fun _ : Fin d => (volume : Measure ℂ)), ∀ i,
      u i (x i) = c i * x i ^ p i * planarPotentialHalfWeight n V (x i) :=
    ae_all_iff.mpr (fun i => (quasiMeasurePreserving_eval (fun _ => (volume : Measure ℂ)) i).ae_eq_comp (hscalar i))
  refine ⟨p, ∏ i, c i, ?_⟩
  rw [volume_pi]
  filter_upwards [l2PiProductVector_coeFn (fun _ => (volume : Measure ℂ)) u, hall] with x hx hh
  rw [hx]
  simp only [hh, Finset.prod_mul_distrib, piPotentialHalfWeight]

theorem piPotentialHalfWeight_permute {d : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (σ : ParticlePermutation d) (x : Configuration d) :
    piPotentialHalfWeight d n V (permute σ x) = piPotentialHalfWeight d n V x := by
  unfold piPotentialHalfWeight
  exact Equiv.prod_comp σ (fun i => planarPotentialHalfWeight n V (x i))

theorem complexLp_finset_sum_coeFn {A I : Type*} [MeasurableSpace A]
    (μ : Measure A) (s : Finset I) (U : I → Lp ℂ 2 μ) :
    ((∑ i ∈ s, U i : Lp ℂ 2 μ) : A → ℂ) =ᵐ[μ] (fun x => ∑ i ∈ s, U i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    simpa using hx
  | @insert i s his ih =>
    simp only [Finset.sum_insert his]
    filter_upwards [Lp.coeFn_add (U i) (∑ j ∈ s, U j), ih] with x hx hh
    rw [hx]
    change U i x + (∑ j ∈ s, U j) x = _
    rw [hh]
end
end GinibrePoincare
