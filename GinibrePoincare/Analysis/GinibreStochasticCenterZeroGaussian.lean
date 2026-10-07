module

public import GinibrePoincare.Analysis.BrownianOrthogonalVectorProcess
public import GinibrePoincare.Analysis.GinibreStochasticOUConvolution
public import GinibrePoincare.Analysis.GinibreHamiltonianCenterFunctional

@[expose] public section

/-! Actual normalized original-coordinate center noises are Brownian motions.
Their OU laws permit positive-time nonvanishing even from a zero initial center. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem brownianFamily_unit_projection_isBrownian {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ ι) (he : ‖e‖=1) :
    IsBrownianReal (fun t ω => inner ℝ e (WithLp.toLp 2 (fun i => B i t ω))) P := by
  classical
  have hv := brownianFamily_toEuclidean_isBrownianVectorProcess B P hB hind
  have hg := hv.gaussian.comp_left (fun _ => innerSL ℝ e)
  refine ⟨hg.isPreBrownianReal_of_covariance ?_ ?_,?_⟩
  · intro t
    change (∫ ω, inner ℝ e (WithLp.toLp 2 (fun i => B i t ω)) ∂P) = 0
    simp only [PiLp.inner_apply,Real.inner_apply]
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro i hi
      rw [integral_const_mul,(hB i).integral_eval,mul_zero]
    · intro i hi
      exact (((hB i).isGaussianProcess.hasGaussianLaw_eval t).integrable).const_mul _
  · intro s t hst
    change covariance (fun ω => inner ℝ e (WithLp.toLp 2 (fun i => B i s ω)))
      (fun ω => inner ℝ e (WithLp.toLp 2 (fun i => B i t ω))) P = (s : ℝ)
    rw [hv.covariance,min_eq_left hst,real_inner_self_eq_norm_sq,he]
    simp
  · filter_upwards [hv.continuous] with ω hω
    exact (innerSL ℝ e).continuous.comp hω

def ginibreCenterNoiseUnit (n : ℕ) (b : Fin 2) : EuclideanSpace ℝ (Fin n × Fin 2) :=
  WithLp.toLp 2 (fun i => if i.2=b then (Real.sqrt (n : ℝ))⁻¹ else 0)

def ginibreNormalizedCenterBrownian {Ω : Type*} (n : ℕ) (b : Fin 2)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ * ∑ j : Fin n, B (j,b) t ω

theorem ginibreCenterNoiseUnit_norm {n : ℕ} (hn : 0 < n) (b : Fin 2) :
    ‖ginibreCenterNoiseUnit n b‖=1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  have hh : ‖ginibreCenterNoiseUnit n b‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i : Fin n × Fin 2, (if i.2=b then (Real.sqrt (n : ℝ))⁻¹ else 0)^2) = 1
    simp only [Fintype.sum_prod_type]
    simp only [ite_pow,zero_pow (by norm_num : (2 : ℕ) ≠ 0),Finset.sum_ite_eq',
      Finset.mem_univ,if_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [inv_pow,Real.sq_sqrt hnR.le,mul_inv_cancel₀ hnR.ne']
  nlinarith [norm_nonneg (ginibreCenterNoiseUnit n b)]

theorem ginibreNormalizedCenterBrownian_isBrownian
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (b : Fin 2)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IsBrownianReal (ginibreNormalizedCenterBrownian n b B) P := by
  have h := brownianFamily_unit_projection_isBrownian B P hB hind
    (ginibreCenterNoiseUnit n b) (ginibreCenterNoiseUnit_norm hn b)
  convert h using 1
  funext t ω
  simp [ginibreNormalizedCenterBrownian,ginibreCenterNoiseUnit,PiLp.inner_apply,
    Real.inner_apply,Fintype.sum_prod_type,Finset.mul_sum,mul_comm]

theorem brownianFamily_orthogonal_scalar_paths_independent {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e f : EuclideanSpace ℝ ι) (hef : inner ℝ e f = 0) :
    IndepFun (fun ω t => inner ℝ e (WithLp.toLp 2 (fun i => B i t ω)))
      (fun ω t => inner ℝ f (WithLp.toLp 2 (fun i => B i t ω))) P := by
  classical
  have hv := brownianFamily_toEuclidean_isBrownianVectorProcess B P hB hind
  let X := fun t ω => inner ℝ e (WithLp.toLp 2 (fun i => B i t ω))
  let Y := fun t ω => inner ℝ f (WithLp.toLp 2 (fun i => B i t ω))
  have hj : IsGaussianProcess (Sum.elim X Y) P := by
    apply hv.gaussian.of_isGaussianProcess
    intro p
    cases p with
    | inl t =>
      refine ⟨{t},?_,?_⟩
      · exact { toFun := fun x => inner ℝ e (x ⟨t,by simp⟩)
                map_add' := by intro x y; simp [inner_add_right]
                map_smul' := by intro a x; simp [inner_smul_right] }
      · intro ω
        simp [X,Finset.restrict_def]
    | inr t =>
      refine ⟨{t},?_,?_⟩
      · exact { toFun := fun x => inner ℝ f (x ⟨t,by simp⟩)
                map_add' := by intro x y; simp [inner_add_right]
                map_smul' := by intro a x; simp [inner_smul_right] }
      · intro ω
        simp [Y,Finset.restrict_def]
  exact hj.indepFun_of_covariance_eq_zero
    (fun t => hj.aemeasurable (Sum.inl t)) (fun t => hj.aemeasurable (Sum.inr t))
    (fun s t => by simpa [X,Y,hef] using hv.covariance s t e f)

theorem ginibreNormalizedCenterBrownian_real_imag_independent
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IndepFun (fun ω t => ginibreNormalizedCenterBrownian n 0 B t ω)
      (fun ω t => ginibreNormalizedCenterBrownian n 1 B t ω) P := by
  have he : inner ℝ (ginibreCenterNoiseUnit n 0) (ginibreCenterNoiseUnit n 1)=0 := by
    simp [ginibreCenterNoiseUnit,PiLp.inner_apply,Fintype.sum_prod_type,Fin.sum_univ_two]
  have h := brownianFamily_orthogonal_scalar_paths_independent B P hB hind _ _ he
  simpa [ginibreNormalizedCenterBrownian,ginibreCenterNoiseUnit,PiLp.inner_apply,
    Fintype.sum_prod_type,Finset.mul_sum,mul_comm] using h

#print axioms ginibreNormalizedCenterBrownian_real_imag_independent
#print axioms ginibreNormalizedCenterBrownian_isBrownian
end
end GinibrePoincare
