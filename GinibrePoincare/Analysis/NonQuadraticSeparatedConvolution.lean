module

public import GinibrePoincare.Analysis.NonQuadraticSeparatedBumpAverage
public import GinibrePoincare.Analysis.NonQuadraticL2KernelIntegral
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! # Actual separated smoothing equals scalar convolution -/
open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] separatedPlanarBump
local instance : VAddInvariantMeasure (ℂ × ℂ) (ℂ × ℂ) (volume : Measure (ℂ × ℂ)) :=
  inferInstanceAs (VAddInvariantMeasure (ℂ × ℂ) (ℂ × ℂ) ((volume : Measure ℂ).prod (volume : Measure ℂ)))

local instance : ((volume : Measure ℂ).prod (volume : Measure ℂ)).IsNegInvariant := by
  constructor
  exact ((Measure.measurePreserving_neg (volume : Measure ℂ)).prod
    (Measure.measurePreserving_neg (volume : Measure ℂ))).map_eq

def productCompactFunctionL2 (f : ℂ × ℂ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) : Lp ℂ 2 ((volume : Measure ℂ).prod (volume : Measure ℂ)) :=
  (hf.memLp_of_hasCompactSupport hc).toLp f

theorem productPlaneTranslate_compact_smul_ae (c : ℝ) (a : ℂ × ℂ)
    (f : ℂ × ℂ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    ((c • productPlaneL2Translate a (productCompactFunctionL2 f hf hc) :
      Lp ℂ 2 ((volume : Measure ℂ).prod (volume : Measure ℂ))) : ℂ × ℂ → ℂ)
      =ᵐ[(volume : Measure ℂ).prod (volume : Measure ℂ)] (fun x => (c : ℂ) * f (x-a)) := by
  let u := productCompactFunctionL2 f hf hc
  have hu : (u : ℂ × ℂ → ℂ) =ᵐ[((volume : Measure ℂ).prod (volume : Measure ℂ))] f :=
    (hf.memLp_of_hasCompactSupport hc).coeFn_toLp
  have he := (eventually_add_right_iff ((volume : Measure ℂ).prod (volume : Measure ℂ)) (-a)).mpr hu
  filter_upwards [Lp.coeFn_smul c (productPlaneL2Translate a u), productPlaneL2Translate_ae a u, he]
    with x hs ht he
  rw [hs]
  change c • (productPlaneL2Translate a u) x = _
  rw [Complex.real_smul, ht]
  change u (x-a) = f (x-a) at he
  rw [he]

theorem separatedL2BumpAverage_convolution_ae
    (φ ψ : ContDiffBump (0 : ℂ)) (f : ℂ × ℂ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    ((separatedL2BumpAverage φ ψ (productCompactFunctionL2 f hf hc) :
      Lp ℂ 2 ((volume : Measure ℂ).prod (volume : Measure ℂ))) : ℂ × ℂ → ℂ)
      =ᵐ[(volume : Measure ℂ).prod (volume : Measure ℂ)]
      (fun x => ∫ a, (separatedPlanarBump φ ψ a : ℂ) * f (x - a)
        ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) := by
  let u := productCompactFunctionL2 f hf hc
  unfold separatedL2BumpAverage
  have hk : Continuous (fun a => (separatedPlanarBump φ ψ a : ℂ)) :=
    Complex.continuous_ofReal.comp (separatedPlanarBump_continuous φ ψ)
  have hkc : HasCompactSupport (fun a => (separatedPlanarBump φ ψ a : ℂ)) :=
    (separatedPlanarBump_compact φ ψ).comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hker := productL2_kernel_integral_ae
    (fun p => (separatedPlanarBump φ ψ p.1 : ℂ) * f (p.2 - p.1))
    ((hk.comp continuous_fst).mul (hf.comp (continuous_snd.sub continuous_fst)))
    (translatedProductKernel_hasCompactSupport (fun a => (separatedPlanarBump φ ψ a : ℂ)) f hkc hc)
    (fun a => separatedPlanarBump φ ψ a • productPlaneL2Translate a u)
    (integrable_separatedL2BumpIntegrand φ ψ u)
    (fun a => productPlaneTranslate_compact_smul_ae (separatedPlanarBump φ ψ a) a f hf hc)
  exact hker
/-- Reflection and translation of Lebesgue measure identify the two
actual scalar convolution orientations. -/
theorem productPlane_convolution_swap (k f : ℂ × ℂ → ℂ) (x : ℂ × ℂ) :
    (∫ a, k a * f (x-a) ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) =
      ∫ a, f a * k (x-a) ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  rw [← integral_sub_left_eq_self (fun a => k a * f (x-a))
    ((volume : Measure ℂ).prod (volume : Measure ℂ)) x]
  apply integral_congr_ae
  exact Eventually.of_forall (fun a => by simp only [sub_sub_cancel]; exact mul_comm _ _)

end
end GinibrePoincare
