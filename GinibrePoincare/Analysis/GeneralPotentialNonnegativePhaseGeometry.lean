module

public import GinibrePoincare.Analysis.GeneralPotentialPositivePhaseClosure
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open MeasureTheory Set
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def potentialConstantSpace (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) :
    Submodule ℂ (Lp ℂ 2 (potentialMeasure n V)) :=
  Submodule.span ℂ {potentialConstantL2 n hn hV hfin 1}

/-- The actual closed nonnegative-character space: constants plus the full
closed positive-character space. -/
def potentialNonnegativePhaseClosedSpan (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) :
    ClosedSubmodule ℂ (Lp ℂ 2 (potentialMeasure n V)) where
  toSubmodule := potentialConstantSpace n hn hV hfin ⊔ (potentialPositivePhaseClosedSpan n hV hrot).toSubmodule
  isClosed' := by
    unfold potentialConstantSpace
    rw [sup_comm]
    exact Submodule.isClosed_sup_finiteDimensional _ _ (potentialPositivePhaseClosedSpan n hV hrot).isClosed

theorem potentialConstantL2_eq_smul_one (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) (c : ℂ) :
    potentialConstantL2 n hn hV hfin c = c • potentialConstantL2 n hn hV hfin 1 := by
  apply Lp.ext
  filter_upwards [potentialConstantL2_coeFn n hn hV hfin c,
    potentialConstantL2_coeFn n hn hV hfin 1,
    Lp.coeFn_smul c (potentialConstantL2 n hn hV hfin 1)] with z hc h1 hs
  rw [hc, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h1, mul_one]

theorem potentialConstantL2_inner_one_one (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) :
    inner ℂ (potentialConstantL2 n hn hV hfin 1) (potentialConstantL2 n hn hV hfin 1) = 1 := by
  letI := potentialMeasure_isProbabilityMeasure n hn hV hfin
  rw [MeasureTheory.L2.inner_def]
  rw [integral_congr_ae (show (fun z => inner ℂ (potentialConstantL2 n hn hV hfin 1 z)
      (potentialConstantL2 n hn hV hfin 1 z)) =ᵐ[potentialMeasure n V] (fun _ => (1 : ℂ)) by
    filter_upwards [potentialConstantL2_coeFn n hn hV hfin 1] with z hz
    rw [hz]
    simp)]
  simp

/-- Orthogonality to constants removes precisely the constant component of the
actual closed nonnegative-character space. -/
theorem potentialNonnegativePhase_mem_positive_of_orthogonal_constant
    (n : ℕ) (hn : 0 < n) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (x : Lp ℂ 2 (potentialMeasure n V))
    (hx : x ∈ potentialNonnegativePhaseClosedSpan n hn hV hrot hfin)
    (ho : inner ℂ (potentialConstantL2 n hn hV hfin 1) x = 0) :
    x ∈ potentialPositivePhaseClosedSpan n hV hrot := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
  have he : x = c • potentialConstantL2 n hn hV hfin 1 + b := by rw [hc]; exact hab.symm
  have hz : c = 0 := by
    rw [he, inner_add_right, inner_smul_right, potentialConstantL2_inner_one_one,
      potentialConstantL2_orthogonal_positivePhaseClosedSpan n hn hV hrot hfin 1 b hb,
      mul_one, add_zero] at ho
    exact ho
  rw [he, hz, zero_smul, zero_add]
  exact hb

theorem potentialConstantL2_mem_nonnegativePhaseClosedSpan
    (n : ℕ) (hn : 0 < n) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) (c : ℂ) :
    potentialConstantL2 n hn hV hfin c ∈ potentialNonnegativePhaseClosedSpan n hn hV hrot hfin := by
  rw [potentialConstantL2_eq_smul_one]
  apply Submodule.smul_mem
  exact Submodule.mem_sup_left (Submodule.subset_span (by simp))

theorem potentialPositivePhaseClosedSpan_le_nonnegative
    (n : ℕ) (hn : 0 < n) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) :
    (potentialPositivePhaseClosedSpan n hV hrot).toSubmodule ≤
      (potentialNonnegativePhaseClosedSpan n hn hV hrot hfin).toSubmodule :=
  le_sup_right

#print axioms potentialNonnegativePhase_mem_positive_of_orthogonal_constant
end
end GinibrePoincare
