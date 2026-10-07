module

public import GinibrePoincare.Analysis.GinibreFullSemigroupWeakHeat
public import GinibrePoincare.Analysis.GinibreFullSemigroupL1
public import GinibrePoincare.Analysis.GinibreFullSemigroupDecay
public import GinibrePoincare.Analysis.GinibreDynamicsGenerator

@[expose] public section

/-! # The full diffusion at the paper's arbitrary speed -/
open MeasureTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Exact paper time scale at inverse temperature n². -/
def ginibrePaperSpeedFactor (n : ℕ) (α : ℝ≥0) : ℝ≥0 := α / n

@[simp] theorem ginibrePaperSpeedFactor_coe (n : ℕ) (α : ℝ≥0) :
    (ginibrePaperSpeedFactor n α : ℝ) = (α : ℝ) / (n : ℝ) := by
  simp [ginibrePaperSpeedFactor]

/-- The actual full symmetric diffusion at arbitrary nonnegative paper speed. -/
def ginibreFullPaperEvolution (n : ℕ) (hn : 0 < n) (α t : ℝ≥0) :
    ginibreSymmetricL2 n →L[ℂ] ginibreSymmetricL2 n :=
  ginibreFullEvolution n hn (ginibrePaperSpeedFactor n α * t)

/-- Actual real paper-speed diffusion. -/
def ginibreFullRealPaperEvolution (n : ℕ) (hn : 0 < n) (α t : ℝ≥0) :
    ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n :=
  ginibreFullRealEvolution n hn (ginibrePaperSpeedFactor n α * t)

@[simp] theorem ginibreFullPaperEvolution_zero (n : ℕ) (hn : 0 < n) (α : ℝ≥0) :
    ginibreFullPaperEvolution n hn α 0 = 1 := by simp [ginibreFullPaperEvolution]

theorem ginibreFullPaperEvolution_add (n : ℕ) (hn : 0 < n) (α s t : ℝ≥0) :
    ginibreFullPaperEvolution n hn α (s + t) =
      ginibreFullPaperEvolution n hn α s * ginibreFullPaperEvolution n hn α t := by
  unfold ginibreFullPaperEvolution
  rw [mul_add, ginibreFullEvolution_add]

theorem continuous_ginibreFullPaperEvolution (n : ℕ) (hn : 0 < n) (α : ℝ≥0)
    (x : ginibreSymmetricL2 n) : Continuous (fun t => ginibreFullPaperEvolution n hn α t x) :=
  (continuous_ginibreFullEvolution n hn x).comp (continuous_const.mul continuous_id)

theorem ginibreFullPaperEvolution_contracts (n : ℕ) (hn : 0 < n) (α t : ℝ≥0)
    (x : ginibreSymmetricL2 n) : ‖ginibreFullPaperEvolution n hn α t x‖ ≤ ‖x‖ :=
  ginibreFullEvolution_contracts n hn _ x

theorem ginibreFullPaperEvolution_integral (n : ℕ) (hn : 0 < n) (α t : ℝ≥0)
    (x : ginibreSymmetricL2 n) :
    (∫ z, (ginibreFullPaperEvolution n hn α t x).val z ∂ginibreMeasure n) =
      ∫ z, x.val z ∂ginibreMeasure n := ginibreFullEvolution_integral n hn _ x

theorem ginibreFullRealPaperEvolution_interval (n : ℕ) (hn : 0 < n) (α t : ℝ≥0)
    (x : ginibreFullSymmetricValues n) (a b : ℝ)
    (hx : ∀ᵐ z ∂ginibreMeasure n, x.val z ∈ Set.Icc a b) :
    ∀ᵐ z ∂ginibreMeasure n, (ginibreFullRealPaperEvolution n hn α t x).val z ∈ Set.Icc a b :=
  ginibreFullRealEvolution_interval n hn _ x a b hx

/-- The actual infinitesimal derivative has exactly the α/n paper multiplier. -/
theorem ginibreFullPaperEvolution_right_derivative (n : ℕ) (hn : 0 < n) (α : ℝ≥0)
    (u v : ginibreSymmetricL2 n) (hg : (u, v) ∈ (ginibreFullGenerator n hn).graph) :
    HasDerivWithinAt (fun s : ℝ => ginibreFullPaperEvolution n hn α (Real.toNNReal s) u)
      (((α : ℝ) / (n : ℝ)) • v) (Set.Ici 0) 0 := by
  let c : ℝ := ginibrePaperSpeedFactor n α
  have hc : 0 ≤ c := (ginibrePaperSpeedFactor n α).coe_nonneg
  have hd := (ginibreFullGenerator_graph_iff_right_derivative n hn u v).mp hg
  have hs : HasDerivWithinAt (fun s : ℝ => c * s) c (Set.Ici 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul c).hasDerivWithinAt
  have hcomp := hd.scomp_of_eq 0 hs (by
    intro s hs
    exact mul_nonneg hc hs) (by simp)
  have hcc : Real.toNNReal c = ginibrePaperSpeedFactor n α := Real.toNNReal_coe
  simp only [Function.comp_def, Real.toNNReal_mul hc, hcc] at hcomp
  simpa only [ginibreFullPaperEvolution, c, ginibrePaperSpeedFactor_coe] using hcomp

/-- The sharp full centered relaxation rate at the paper's exact speed. -/
theorem ginibreFullPaperEvolution_centered_decay (n : ℕ) (hn : 0 < n) (α t : ℝ≥0)
    (x : ginibreSymmetricL2 n) :
    ‖ginibreFullPaperEvolution n hn α t (ginibreFullComplexCenter n hn x)‖ ≤
      Real.exp (-2 * ((α : ℝ) / (n : ℝ)) * (t : ℝ)) * ‖ginibreFullComplexCenter n hn x‖ := by
  have h := ginibreFullEvolution_centered_decay n hn (ginibrePaperSpeedFactor n α * t) x
  simpa only [ginibreFullPaperEvolution, NNReal.coe_mul, ginibrePaperSpeedFactor_coe,
    mul_assoc] using h

end
end GinibrePoincare
