module

public import GinibrePoincare.Analysis.NonQuadraticBochner
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section

/-! # A concrete scalar confinement form and its Riesz resolvent

The graph is the closed span of literal compact smooth value/derivative pairs
under the density `exp(-W)`. This construction neither assumes an LSI nor
asserts the parabolic regularity needed for entropy differentiation.
-/

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Literal confinement measure, before normalization. -/
def bakryEmeryScalarMeasure (W : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-W x)))

abbrev BakryEmeryScalarL2 (W : ℝ → ℝ) := Lp ℝ 2 (bakryEmeryScalarMeasure W)
abbrev BakryEmeryScalarFormAmbient (W : ℝ → ℝ) :=
  WithLp 2 (BakryEmeryScalarL2 W × BakryEmeryScalarL2 W)

/-- Literal compact smooth graph pairs in weighted L². -/
def bakryEmeryScalarCorePairs (W : ℝ → ℝ) : Set (BakryEmeryScalarFormAmbient W) :=
  {p | ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (∀ᵐ x ∂bakryEmeryScalarMeasure W, (WithLp.ofLp p).1 x = f x) ∧
    (∀ᵐ x ∂bakryEmeryScalarMeasure W, (WithLp.ofLp p).2 x = deriv f x)}

/-- Every smooth compact test actually determines a point of the weighted
core graph; its L² integrability is derived from the confinement density. -/
def bakryEmeryScalarCorePair (W : ℝ → ℝ) (hW : Continuous W)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    BakryEmeryScalarFormAmbient W := by
  letI : IsLocallyFiniteMeasure (bakryEmeryScalarMeasure W) :=
    IsLocallyFiniteMeasure.withDensity_ofReal
      (Real.continuous_exp.comp hW.neg)
  have hm : MemLp f 2 (bakryEmeryScalarMeasure W) :=
    hf.continuous.memLp_of_hasCompactSupport hc
  have hd : Continuous (deriv f) :=
    (show ContDiff ℝ (0 + 1) f from hf.of_le (by simp)).deriv'.continuous
  have hdm : MemLp (deriv f) 2 (bakryEmeryScalarMeasure W) :=
    hd.memLp_of_hasCompactSupport hc.deriv
  exact WithLp.toLp 2 (hm.toLp f, hdm.toLp (deriv f))

theorem bakryEmeryScalarCorePair_mem (W : ℝ → ℝ) (hW : Continuous W)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    bakryEmeryScalarCorePair W hW f hf hc ∈ bakryEmeryScalarCorePairs W := by
  let : IsLocallyFiniteMeasure (bakryEmeryScalarMeasure W) :=
    IsLocallyFiniteMeasure.withDensity_ofReal
      (Real.continuous_exp.comp hW.neg)
  have hm : MemLp f 2 (bakryEmeryScalarMeasure W) :=
    hf.continuous.memLp_of_hasCompactSupport hc
  have hd : Continuous (deriv f) :=
    (show ContDiff ℝ (0 + 1) f from hf.of_le (by simp)).deriv'.continuous
  have hdm : MemLp (deriv f) 2 (bakryEmeryScalarMeasure W) :=
    hd.memLp_of_hasCompactSupport hc.deriv
  refine ⟨f, hf, hc, ?_, ?_⟩
  · unfold bakryEmeryScalarCorePair
    exact hm.coeFn_toLp
  · unfold bakryEmeryScalarCorePair
    exact hdm.coeFn_toLp

/-- The actual closed confinement value-gradient form domain. -/
def bakryEmeryScalarFormSpace (W : ℝ → ℝ) :
    Submodule ℝ (BakryEmeryScalarFormAmbient W) :=
  (Submodule.span ℝ (bakryEmeryScalarCorePairs W)).topologicalClosure

instance bakryEmeryScalarFormSpace_complete (W : ℝ → ℝ) :
    CompleteSpace (bakryEmeryScalarFormSpace W) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Value projection from the actual closed graph. -/
def bakryEmeryScalarFormValue (W : ℝ → ℝ) :
    bakryEmeryScalarFormSpace W →L[ℝ] BakryEmeryScalarL2 W :=
  (WithLp.fstL 2 ℝ (BakryEmeryScalarL2 W) (BakryEmeryScalarL2 W)).comp
    (bakryEmeryScalarFormSpace W).subtypeL

/-- Derivative projection from the actual closed graph. -/
def bakryEmeryScalarFormGradient (W : ℝ → ℝ) :
    bakryEmeryScalarFormSpace W →L[ℝ] BakryEmeryScalarL2 W :=
  (WithLp.sndL 2 ℝ (BakryEmeryScalarL2 W) (BakryEmeryScalarL2 W)).comp
    (bakryEmeryScalarFormSpace W).subtypeL

/-- Concrete Riesz resolvent on the closed confinement graph. -/
def bakryEmeryScalarFormResolvent (W : ℝ → ℝ) (f : BakryEmeryScalarL2 W) :
    bakryEmeryScalarFormSpace W :=
  (InnerProductSpace.toDual ℝ (bakryEmeryScalarFormSpace W)).symm
    ((innerSL ℝ f).comp (bakryEmeryScalarFormValue W))

theorem bakryEmeryScalarFormResolvent_riesz (W : ℝ → ℝ)
    (f : BakryEmeryScalarL2 W) (q : bakryEmeryScalarFormSpace W) :
    inner ℝ (bakryEmeryScalarFormResolvent W f) q =
      inner ℝ f (bakryEmeryScalarFormValue W q) :=
  InnerProductSpace.toDual_symm_apply

/-- The graph norm has the ordinary Dirichlet normalization. -/
theorem bakryEmeryScalarForm_inner (W : ℝ → ℝ)
    (p q : bakryEmeryScalarFormSpace W) :
    inner ℝ p q = inner ℝ (bakryEmeryScalarFormValue W p) (bakryEmeryScalarFormValue W q) +
      inner ℝ (bakryEmeryScalarFormGradient W p) (bakryEmeryScalarFormGradient W q) := by
  change inner ℝ p.val q.val = _
  rw [WithLp.prod_inner_apply]
  rfl

/-- The exact weak resolvent equation on the concrete closed graph. -/
theorem bakryEmeryScalarFormResolvent_equation (W : ℝ → ℝ)
    (f : BakryEmeryScalarL2 W) (q : bakryEmeryScalarFormSpace W) :
    inner ℝ (bakryEmeryScalarFormValue W (bakryEmeryScalarFormResolvent W f))
      (bakryEmeryScalarFormValue W q) +
    inner ℝ (bakryEmeryScalarFormGradient W (bakryEmeryScalarFormResolvent W f))
      (bakryEmeryScalarFormGradient W q) = inner ℝ f (bakryEmeryScalarFormValue W q) := by
  rw [← bakryEmeryScalarForm_inner]
  exact bakryEmeryScalarFormResolvent_riesz W f q

theorem bakryEmeryScalarFormResolvent_norm_le (W : ℝ → ℝ)
    (f : BakryEmeryScalarL2 W) : ‖bakryEmeryScalarFormResolvent W f‖ ≤ ‖f‖ := by
  let p := bakryEmeryScalarFormResolvent W f
  have hr := bakryEmeryScalarFormResolvent_riesz W f p
  rw [real_inner_self_eq_norm_sq] at hr
  have hv : ‖bakryEmeryScalarFormValue W p‖ ≤ ‖p‖ :=
    WithLp.norm_fst_le (α := BakryEmeryScalarL2 W) (β := BakryEmeryScalarL2 W) p.val
  have hi := real_inner_le_norm f (bakryEmeryScalarFormValue W p)
  have hb : ‖p‖ ^ 2 ≤ ‖f‖ * ‖p‖ := by
    rw [hr]
    exact hi.trans (mul_le_mul_of_nonneg_left hv (norm_nonneg f))
  change ‖p‖ ≤ ‖f‖
  nlinarith [norm_nonneg p, norm_nonneg f]

/-- Linear dependence of the actual graph resolvent on the datum. -/
def bakryEmeryScalarFormResolventLinear (W : ℝ → ℝ) :
    BakryEmeryScalarL2 W →ₗ[ℝ] bakryEmeryScalarFormSpace W where
  toFun := bakryEmeryScalarFormResolvent W
  map_add' := by
    intro f g
    unfold bakryEmeryScalarFormResolvent
    rw [← map_add]
    congr 1
    ext q
    simp
  map_smul' := by
    intro c f
    unfold bakryEmeryScalarFormResolvent
    rw [← map_smul]
    congr 1
    ext q
    simp

/-- The actual graph resolvent as a bounded linear map. -/
def bakryEmeryScalarFormResolventCLM (W : ℝ → ℝ) :
    BakryEmeryScalarL2 W →L[ℝ] bakryEmeryScalarFormSpace W :=
  (bakryEmeryScalarFormResolventLinear W).mkContinuous 1 (by
    intro f
    simpa [bakryEmeryScalarFormResolventLinear] using bakryEmeryScalarFormResolvent_norm_le W f)

/-- The actual value resolvent on the confinement weighted L² space. -/
def bakryEmeryScalarValueResolvent (W : ℝ → ℝ) :
    BakryEmeryScalarL2 W →L[ℝ] BakryEmeryScalarL2 W :=
  (bakryEmeryScalarFormValue W).comp (bakryEmeryScalarFormResolventCLM W)

theorem bakryEmeryScalarValueResolvent_symmetric (W : ℝ → ℝ)
    (f h : BakryEmeryScalarL2 W) :
    inner ℝ (bakryEmeryScalarValueResolvent W f) h =
      inner ℝ f (bakryEmeryScalarValueResolvent W h) := by
  have hf := bakryEmeryScalarFormResolvent_riesz W f (bakryEmeryScalarFormResolvent W h)
  have hh := bakryEmeryScalarFormResolvent_riesz W h (bakryEmeryScalarFormResolvent W f)
  change inner ℝ (bakryEmeryScalarFormValue W (bakryEmeryScalarFormResolvent W f)) h =
    inner ℝ f (bakryEmeryScalarFormValue W (bakryEmeryScalarFormResolvent W h))
  calc
    _ = inner ℝ h (bakryEmeryScalarFormValue W (bakryEmeryScalarFormResolvent W f)) :=
      real_inner_comm _ _
    _ = inner ℝ (bakryEmeryScalarFormResolvent W h) (bakryEmeryScalarFormResolvent W f) := hh.symm
    _ = inner ℝ (bakryEmeryScalarFormResolvent W f) (bakryEmeryScalarFormResolvent W h) :=
      real_inner_comm _ _
    _ = _ := hf

/-- Positivity is proved as an exact graph-norm identity. -/
theorem bakryEmeryScalarValueResolvent_positive (W : ℝ → ℝ)
    (f : BakryEmeryScalarL2 W) :
    inner ℝ f (bakryEmeryScalarValueResolvent W f) =
      ‖bakryEmeryScalarFormResolvent W f‖ ^ 2 := by
  exact (bakryEmeryScalarFormResolvent_riesz W f (bakryEmeryScalarFormResolvent W f)).symm.trans
    (real_inner_self_eq_norm_sq _)

#print axioms bakryEmeryScalarValueResolvent_symmetric
#print axioms bakryEmeryScalarValueResolvent_positive

#print axioms bakryEmeryScalarFormResolvent_riesz
#print axioms bakryEmeryScalarForm_inner
#print axioms bakryEmeryScalarCorePair_mem
#print axioms bakryEmeryScalarFormResolvent_equation
#print axioms bakryEmeryScalarFormResolvent_norm_le

end
end GinibrePoincare
