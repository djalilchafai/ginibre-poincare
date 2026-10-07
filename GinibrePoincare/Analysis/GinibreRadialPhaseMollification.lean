module

public import GinibrePoincare.Analysis.GinibreRadialCompactWeakGradient
public import GinibrePoincare.Analysis.GinibreLebesgueL2Transfer
public import GinibrePoincare.Analysis.RadialL2MollifierMaps

@[expose] public section

/-! # Actual radial mollification through collision configurations

Compact radial weak pairs on the phase-regular set admit simultaneous weighted
L² approximation by actual smooth compact convolutions and their actual gradients.
-/

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

/-- The actual normalized radial convolutions and their actual classical gradients
converge to a compact radial weak pair. Collisions in either support are allowed. -/
theorem ginibre_weighted_radial_phaseRegular_mollification (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h)
    (hfs : tsupport f ⊆ {z | PhaseRegular n z}) (hhs : tsupport h ⊆ {z | PhaseRegular n z})
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    ∃ (v : ℕ → Lp ℝ 2 (ginibreMeasure n))
      (w : ℕ → Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)),
      (∀ m, ContDiff ℝ ∞ (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) ∧
        HasCompactSupport (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) ∧
        (v m : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
          (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) ∧
        (w m : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
          ginibreEuclideanGradient (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f)) ∧
      Tendsto (fun m => (v m, w m)) atTop (𝓝 (u, g)) := by
  have fv := ginibre_radial_value_memLp_volume_phaseRegular n hn u f hf hr hfc hfs
  have hv := ginibre_radial_gradient_memLp_volume_phaseRegular n hn u g hg f hf hr h hh hhc hhs
  have hd (m : ℕ) := ginibre_radial_phaseRegular_weak_gradient_mollification n hn u g hg f h
    hf hh hfc hhc hfs hhs hr (radialMollifierKernel n m)
    (radialMollifierKernel_properties n m).1 (radialMollifierKernel_properties n m).2.1
  let a m := radialSmoothCompactMollification n m f fv hfc
  let b m := radialL2MollifierAverage n m (hv.toLp h)
  have hb (m : ℕ) : (b m : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[volume]
      ginibreEuclideanGradient (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) := by
    have he (k : Fin n × Fin 2) : ∀ᵐ z ∂(volume : Measure (Configuration n)),
        b m z k = ginibreEuclideanGradient
          (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) z k := by
      let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ :=
        PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) k
      filter_upwards [P.coeFn_compLpL (b m),
        radialL2MollifierAverage_projection_convolution_ae n m P h hv hhc] with z hz hz'
      exact hz.symm.trans (hz'.trans ((hd m).2 z k).symm)
    filter_upwards [(ae_all_iff).mpr he] with z hz
    ext k
    exact hz k
  let v m := ginibreL2OfLebesgue n hn (a m)
  let w m := ginibreL2OfLebesgue n hn (b m)
  obtain ⟨c, hc, hm⟩ := ginibreMeasure_le_finite_smul_volume n hn
  have hac : ginibreMeasure n ≪ (volume : Measure (Configuration n)) :=
    Measure.absolutelyContinuous_of_le_smul hm
  have hu : ginibreL2OfLebesgue n hn (fv.toLp f) = u := by
    apply Lp.ext
    exact (ginibreL2OfLebesgue_ae n hn (fv.toLp f)).trans
      ((hac.ae_eq fv.coeFn_toLp).trans hf.symm)
  have hg' : ginibreL2OfLebesgue n hn (hv.toLp h) = g := by
    apply Lp.ext
    exact (ginibreL2OfLebesgue_ae n hn (hv.toLp h)).trans
      ((hac.ae_eq hv.coeFn_toLp).trans hh.symm)
  refine ⟨v, w, ?_, ?_⟩
  · intro m
    refine ⟨(hd m).1, (radialMollifierKernel_properties n m).2.1.convolution (lsmul ℝ ℝ) hfc,
      ?_, ?_⟩
    · exact (ginibreL2OfLebesgue_ae n hn (a m)).trans
        (hac.ae_eq (memLp_radial_convolution_compact n m f fv hfc).coeFn_toLp)
    · exact (ginibreL2OfLebesgue_ae n hn (b m)).trans (hac.ae_eq (hb m))
  · have ha := (ginibreL2OfLebesgue n hn (V := ℝ)).continuous.continuousAt.tendsto.comp
      (radialSmoothCompactMollification_tendsto n f fv hfc)
    have hb' := (ginibreL2OfLebesgue n hn (V := EuclideanSpace ℝ (Fin n × Fin 2))).continuous.continuousAt.tendsto.comp (radialL2MollifierAverage_tendsto n (hv.toLp h))
    rw [hu] at ha
    rw [hg'] at hb'
    exact ha.prodMk_nhds hb'

end
end GinibrePoincare
