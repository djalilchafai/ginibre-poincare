module
public import GinibrePoincare.Analysis.CorrespondenceGUERealPoincare
public import GinibrePoincare.Analysis.MatrixGaussianH1Closure
@[expose] public section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev GUEValueL2 (n : ℕ) := Lp ℝ 2 (gueOrderedMeasure n)
abbrev GUEGradientL2 (n : ℕ) := Lp (EuclideanSpace ℝ (Fin n)) 2 (gueOrderedMeasure n)
abbrev GUESobolevPair (n : ℕ) := GUEValueL2 n×GUEGradientL2 n

def gueCompactC1Pairs (n : ℕ) : Set (GUESobolevPair n) :=
  {p | ∃f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f ∧ HasCompactSupport f ∧
    (p.1 : EuclideanSpace ℝ (Fin n) → ℝ)=ᵐ[gueOrderedMeasure n]f ∧
    (p.2 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))=ᵐ[gueOrderedMeasure n]gradient f}

def gueH1Completion (n : ℕ) : Set (GUESobolevPair n) := closure (gueCompactC1Pairs n)

theorem gueH1Completion_square_lsi {n : ℕ} (hn : 0<n)
    (p : GUESobolevPair n) (hp : p∈gueH1Completion n) :
    Integrable (fun x => p.1 x^2*Real.log (p.1 x^2)) (gueOrderedMeasure n) ∧
    squareEntropy (gueOrderedMeasure n) p.1 ≤ (2/(n : ℝ))*‖p.2‖^2 := by
  letI := gueOrderedMeasure_probability hn
  have hc : IsClosed {p : GUESobolevPair n |
      Integrable (fun x => p.1 x^2*Real.log (p.1 x^2)) (gueOrderedMeasure n) ∧
      squareEntropy (gueOrderedMeasure n) p.1 ≤ (2/(n : ℝ))*‖p.2‖^2} := by
    apply IsSeqClosed.isClosed
    intro q r hq hr
    exact squareEntropy_le_of_L2_tendsto (gueOrderedMeasure n) (fun k => (q k).1) r.1
      (fun k => (2/(n : ℝ))*‖(q k).2‖^2) ((2/(n : ℝ))*‖r.2‖^2)
      (continuous_fst.tendsto r |>.comp hr)
      ((continuous_snd.tendsto r |>.comp hr).norm.pow 2 |>.const_mul _)
      (fun k => (hq k).1) (fun k => (hq k).2)
  apply closure_minimal ?_ hc hp
  intro q hq
  obtain ⟨f, hf, hs, hv, hg⟩ := hq
  have hlog := (continuous_square_mul_log hf.continuous).integrable_of_hasCompactSupport
    (μ := gueOrderedMeasure n) (compactSupport_square_mul_log hs)
  refine ⟨hlog.congr ?_,?_⟩
  · filter_upwards [hv] with x hx
    simp [hx]
  · rw [squareEntropy_congr_ae _ hv,← integral_norm_sq_eq_L2_norm_sq]
    have he : (∫x, ‖q.2 x‖^2 ∂gueOrderedMeasure n)=
        (∫x, ‖gradient f x‖^2 ∂gueOrderedMeasure n) := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]
    rw [he]
    exact gueOrderedMeasure_square_lsi hn f hf hs


def gueOneL2 (n : ℕ) (hn : 0<n) : GUEValueL2 n := by
  letI := gueOrderedMeasure_probability hn
  exact (memLp_const (1 : ℝ)).toLp (fun _ => 1)

theorem gueOneL2_ae (n : ℕ) (hn : 0<n) :
    (gueOneL2 n hn : EuclideanSpace ℝ (Fin n) → ℝ)=ᵐ[gueOrderedMeasure n]fun _ => 1 := by
  letI := gueOrderedMeasure_probability hn
  exact (memLp_const (1 : ℝ)).coeFn_toLp

theorem gueH1Completion_poincare {n : ℕ} (hn : 0<n)
    (p : GUESobolevPair n) (hp : p∈gueH1Completion n) :
    (∫x, p.1 x^2 ∂gueOrderedMeasure n)-(∫x, p.1 x ∂gueOrderedMeasure n)^2 ≤
      (1/(n : ℝ))*‖p.2‖^2 := by
  letI := gueOrderedMeasure_probability hn
  have hv (u : GUEValueL2 n) :
      ‖u‖^2-(inner ℝ (gueOneL2 n hn) u)^2=
        (∫x, u x^2 ∂gueOrderedMeasure n)-(∫x, u x ∂gueOrderedMeasure n)^2 := by
    rw [← integral_square_eq_L2_norm_sq, L2.inner_def]
    congr 2
    apply integral_congr_ae
    filter_upwards [gueOneL2_ae n hn] with x hx
    simp [hx]
  have hc : IsClosed {p : GUESobolevPair n |
      ‖p.1‖^2-(inner ℝ (gueOneL2 n hn) p.1)^2≤(1/(n : ℝ))*‖p.2‖^2} := by
    apply isClosed_le
    · exact continuous_fst.norm.pow 2 |>.sub ((continuous_const.inner continuous_fst).pow 2)
    · exact continuous_const.mul (continuous_snd.norm.pow 2)
  rw [← hv p.1]
  apply closure_minimal ?_ hc hp
  intro q hq
  obtain ⟨f, hf, hs, huf, hgf⟩ := hq
  change ‖q.1‖^2-(inner ℝ (gueOneL2 n hn) q.1)^2≤(1/(n : ℝ))*‖q.2‖^2
  rw [hv q.1,← integral_norm_sq_eq_L2_norm_sq]
  have hsquare : (∫x, q.1 x^2 ∂gueOrderedMeasure n)=(∫x, f x^2 ∂gueOrderedMeasure n) :=
    integral_congr_ae (huf.fun_comp (fun t => t^2))
  have he : (∫x, ‖q.2 x‖^2 ∂gueOrderedMeasure n)=(∫x, ‖gradient f x‖^2 ∂gueOrderedMeasure n) :=
    integral_congr_ae (hgf.fun_comp (fun t => ‖t‖^2))
  rw [hsquare, integral_congr_ae huf, he]
  exact gueOrderedMeasure_poincare_compactC1 hn f hf hs

#print axioms gueH1Completion_poincare

#print axioms gueH1Completion_square_lsi
end
end GinibrePoincare
