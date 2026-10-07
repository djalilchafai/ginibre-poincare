module

public import GinibrePoincare.Analysis.NonQuadraticPiTensorMollification
public import GinibrePoincare.Analysis.NonQuadraticFiniteKernelIntegral

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter
open scoped ContDiff InnerProductSpace Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false

def piPotentialHalfWeight (d n : ℕ) (V : ℂ → ℝ) (x : Fin d → ℂ) : ℂ :=
  ∏ i, planarPotentialHalfWeight n V (x i)

theorem piPotentialHalfWeight_continuous (d n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    Continuous (piPotentialHalfWeight d n V) := by
  unfold piPotentialHalfWeight
  apply continuous_finset_prod
  intro i _
  have hw : Continuous (planarPotentialHalfWeight n V) := by
    unfold planarPotentialHalfWeight
    fun_prop
  exact hw.comp (continuous_apply i)

theorem planarPiTranslatedValue_coeFn {m : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ : Fin (m+1) → PlanarComplexCompactTest)
    (a : Fin (m+1) → ℂ) :
    (planarPiPureWeightedValue n V hV (fun i => planarComplexTestTranslate (φ i) (a i)) :
      (Fin (m+1) → ℂ) → ℂ) =ᵐ[Measure.pi (fun _ => (volume : Measure ℂ))]
      (fun x => (∏ i, φ i (x i - a i)) * piPotentialHalfWeight (m+1) n V x) := by
  have hi (i : Fin (m+1)) :
      (planarComplexWeightedValueL2 n V hV (planarComplexTestTranslate (φ i) (a i)) : ℂ → ℂ)
        =ᵐ[volume] (fun x => φ i (x - a i) * planarPotentialHalfWeight n V x) := by
    rw [planarComplexTestTranslate_weightedValue]
    exact (planarWeightedTranslate_memLp n V hV (φ i) (φ i).property.1.continuous (φ i).property.2 (a i)).coeFn_toLp
  have hall : ∀ᵐ x ∂Measure.pi (fun _ : Fin (m+1) => (volume : Measure ℂ)), ∀ i,
      planarComplexWeightedValueL2 n V hV (planarComplexTestTranslate (φ i) (a i)) (x i) =
        φ i (x i - a i) * planarPotentialHalfWeight n V (x i) :=
    ae_all_iff.mpr (fun i => (quasiMeasurePreserving_eval (fun _ => (volume : Measure ℂ)) i).ae_eq_comp (hi i))
  filter_upwards [l2PiProductVector_coeFn (fun _ => (volume : Measure ℂ))
    (fun i => planarComplexWeightedValueL2 n V hV (planarComplexTestTranslate (φ i) (a i))), hall]
    with x hx hh
  unfold planarPiPureWeightedValue
  rw [hx]
  simp only [hh, Finset.prod_mul_distrib, piPotentialHalfWeight]

theorem planarPiTranslatedGraph_integral_value_ae {m : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ : Fin (m+1) → PlanarComplexCompactTest)
    (f : (Fin (m+1) → ℂ) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    (((∫ a, f a • planarPiPureDbarGraph n V hV
      (fun i => planarComplexTestTranslate (φ i) (a i))
      ∂Measure.pi (fun _ => (volume : Measure ℂ))).1) : (Fin (m+1) → ℂ) → ℂ)
      =ᵐ[Measure.pi (fun _ => (volume : Measure ℂ))]
        (fun x => (∫ a, f a * ∏ i, φ i (x i - a i)
          ∂Measure.pi (fun _ => (volume : Measure ℂ))) * piPotentialHalfWeight (m+1) n V x) := by
  let μ := Measure.pi (fun _ : Fin (m+1) => (volume : Measure ℂ))
  let k : (Fin (m+1) → ℂ) → ℂ := fun x => ∏ i, φ i (x i)
  have hk : Continuous k := continuous_finset_prod _ (fun i _ => (φ i).property.1.continuous.comp (continuous_apply i))
  have hkc : HasCompactSupport k := piSeparatedKernel_hasCompactSupport _ (fun i => (φ i).property.2)
  have hg : Continuous (fun p : (Fin (m+1) → ℂ) × (Fin (m+1) → ℂ) =>
      (f p.1 * k (p.2 - p.1)) * piPotentialHalfWeight (m+1) n V p.2) :=
    ((hf.comp continuous_fst).mul (hk.comp (continuous_snd.sub continuous_fst))).mul
      ((piPotentialHalfWeight_continuous (m+1) n V hV).comp continuous_snd)
  have hgc := (finiteTranslatedKernel_hasCompactSupport f k hc hkc).mul_right
    (f' := fun p => piPotentialHalfWeight (m+1) n V p.2)
  let G := fun a => f a • planarPiPureWeightedValue n V hV
    (fun i => planarComplexTestTranslate (φ i) (a i))
  have hG : Integrable G μ :=
    (planarPiTranslatedGraph_integrable n V hV φ f hf hc).fst
  have hcoef (a) : (G a : (Fin (m+1) → ℂ) → ℂ) =ᵐ[μ]
      (fun x => (f a * k (x-a)) * piPotentialHalfWeight (m+1) n V x) := by
    filter_upwards [Lp.coeFn_smul (f a) (planarPiPureWeightedValue n V hV
      (fun i => planarComplexTestTranslate (φ i) (a i))), planarPiTranslatedValue_coeFn n V hV φ a]
      with x hx hh
    rw [hx]
    change f a * _ = _
    rw [hh]
    exact (mul_assoc (f a) (∏ i, φ i (x i - a i)) (piPotentialHalfWeight (m+1) n V x)).symm
  have he := finiteDimensionalL2_kernel_integral_ae μ _ hg hgc G hG hcoef
  rw [fst_integral (planarPiTranslatedGraph_integrable n V hV φ f hf hc)]
  exact he.mono (fun x hx => hx.trans
    (integral_mul_const (piPotentialHalfWeight (m+1) n V x)
      (fun a : Fin (m+1) → ℂ => f a * ∏ i, φ i (x i - a i))))
end
end GinibrePoincare
