module

public import GinibrePoincare.Analysis.GinibreFullGeneratorDensity
public import GinibrePoincare.Analysis.GinibreValueTruncationL2

@[expose] public section

/-! Genuine bounded symmetric values are dense in the entire actual real
symmetric Ginibre L² space. -/
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def ginibreFullSymmetricBoundedTruncation (n m : ℕ) (u : ginibreFullSymmetricValues n) :
    ginibreFullSymmetricValues n := by
  let h := ginibreValueTruncation_memLp n m u.val (Lp.memLp u.val)
  let v := h.toLp (fun z => sobolevValueTruncation m (u.val z))
  refine ⟨v,?_⟩
  intro σ
  apply Lp.ext
  have hv := h.coeFn_toLp
  have hvc := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq hv
  have hup := ginibreRealPermutationL2_ae σ u.val
  rw [u.property σ] at hup
  filter_upwards [ginibreRealPermutationL2_ae σ v, hvc, hv, hup] with z hp hc hz hu
  dsimp only [Function.comp_apply] at hc
  rw [hp, hc, hz,← hu]

theorem ginibreFullSymmetricBoundedTruncation_ae (n m : ℕ) (u : ginibreFullSymmetricValues n) :
    ((ginibreFullSymmetricBoundedTruncation n m u).val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      (fun z => sobolevValueTruncation m (u.val z)) :=
  (ginibreValueTruncation_memLp n m u.val (Lp.memLp u.val)).coeFn_toLp

theorem ginibreFullSymmetricBoundedTruncation_bound (n m : ℕ) (u : ginibreFullSymmetricValues n) :
    ∀ᵐ z ∂ginibreMeasure n, ‖(ginibreFullSymmetricBoundedTruncation n m u).val z‖ ≤ 2*((m : ℝ)+1) :=
  (ginibreFullSymmetricBoundedTruncation_ae n m u).mono fun z hz => by
    rw [hz]
    exact sobolevValueTruncation_bounded m (u.val z)

theorem ginibreFullSymmetricBoundedTruncation_tendsto (n : ℕ) (u : ginibreFullSymmetricValues n) :
    Tendsto (fun m => ginibreFullSymmetricBoundedTruncation n m u) atTop (𝓝 u) := by
  apply tendsto_subtype_rng.mpr
  exact ginibreValueTruncation_L2_tendsto n u.val

def actualBoundedRealVersion {Ω : Type*} (f : Ω → ℝ) (A : ℝ) : Ω → ℝ :=
  fun x => if ‖f x‖ ≤ A then f x else 0

theorem actualBoundedRealVersion_bound {Ω : Type*} (f : Ω → ℝ) (A : ℝ) (hA : 0 ≤ A) :
    ∀ x, ‖actualBoundedRealVersion f A x‖ ≤ A := by
  intro x
  unfold actualBoundedRealVersion
  split_ifs with h
  · exact h
  · simpa using hA

theorem actualBoundedRealVersion_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (A : ℝ) (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ A) :
    actualBoundedRealVersion f A =ᵐ[μ] f :=
  hb.mono fun x hx => if_pos hx

theorem actualBoundedRealVersion_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (A : ℝ)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ A) : MemLp (actualBoundedRealVersion f A) 2 μ :=
  hf.ae_eq (actualBoundedRealVersion_ae μ f A hb).symm

#print axioms actualBoundedRealVersion_bound
#print axioms actualBoundedRealVersion_ae
#print axioms actualBoundedRealVersion_memLp
theorem ginibreFullSymmetric_operators_eq_of_bounded_values (n : ℕ)
    (R S : ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n)
    (heq : ∀ u : ginibreFullSymmetricValues n,
      (∃ A : ℝ, ∀ᵐ z ∂ginibreMeasure n, ‖u.val z‖ ≤ A) → R u=S u) : R=S := by
  apply ContinuousLinearMap.ext
  intro u
  have ht := ginibreFullSymmetricBoundedTruncation_tendsto n u
  have hh (m : ℕ) : R (ginibreFullSymmetricBoundedTruncation n m u)=
      S (ginibreFullSymmetricBoundedTruncation n m u) :=
    heq _ ⟨2*((m : ℝ)+1), ginibreFullSymmetricBoundedTruncation_bound n m u⟩
  have hRt : Tendsto (fun m => R (ginibreFullSymmetricBoundedTruncation n m u)) atTop (𝓝 (R u)) :=
    R.continuous.tendsto u |>.comp ht
  have hSt : Tendsto (fun m => R (ginibreFullSymmetricBoundedTruncation n m u)) atTop (𝓝 (S u)) := by
    convert (S.continuous.tendsto u |>.comp ht) using 1
    funext m
    exact hh m
  exact tendsto_nhds_unique hRt hSt

#print axioms ginibreFullSymmetric_operators_eq_of_bounded_values
#print axioms ginibreFullSymmetricBoundedTruncation
#print axioms ginibreFullSymmetricBoundedTruncation_bound
#print axioms ginibreFullSymmetricBoundedTruncation_tendsto
end
end GinibrePoincare
