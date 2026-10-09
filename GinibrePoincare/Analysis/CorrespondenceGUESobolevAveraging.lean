module
public import GinibrePoincare.Analysis.CorrespondenceGUESmoothAveraging
@[expose] public section
open MeasureTheory Set
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def gueFullSmoothPairs (n : ℕ) : Set (GUEFullSobolevPair n) :=
  {p | ∃f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (p.1 : EuclideanSpace ℝ (Fin n) → ℝ)=ᵐ[gueFullMeasure n]f ∧
    (p.2 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))=ᵐ[gueFullMeasure n]gradient f}

def gueFullH1Completion (n : ℕ) : Set (GUEFullSobolevPair n) := closure (gueFullSmoothPairs n)

def gueSobolevPermutation {n : ℕ} (hn : 0<n) (σ : Equiv.Perm (Fin n)) :
    GUEFullSobolevPair n →L[ℝ] GUEFullSobolevPair n :=
  ((Lp.compMeasurePreservingₗᵢ ℝ (guePermute n σ)
    (gueFullMeasure_permutation_preserving hn σ)).toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ _ _)).prod
  (((guePermuteIsometry n σ.symm).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 (gueFullMeasure n)).comp
    ((Lp.compMeasurePreservingₗᵢ ℝ (guePermute n σ)
      (gueFullMeasure_permutation_preserving hn σ)).toContinuousLinearMap.comp
      (ContinuousLinearMap.snd ℝ _ _)))

def gueSobolevAverage {n : ℕ} (hn : 0<n) : GUEFullSobolevPair n →L[ℝ] GUEFullSobolevPair n :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ •∑σ, gueSobolevPermutation hn σ

theorem gueSobolevPermutation_core {n : ℕ} (hn : 0<n) (σ : Equiv.Perm (Fin n))
    (p : GUEFullSobolevPair n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f)
    (hv : (p.1 : EuclideanSpace ℝ (Fin n) → ℝ)=ᵐ[gueFullMeasure n]f)
    (hg : (p.2 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))=ᵐ[gueFullMeasure n]gradient f) :
    ((gueSobolevPermutation hn σ p).1 : EuclideanSpace ℝ (Fin n)→ℝ)=ᵐ[gueFullMeasure n]f ∘guePermute n σ ∧
    ((gueSobolevPermutation hn σ p).2 : EuclideanSpace ℝ (Fin n)→EuclideanSpace ℝ (Fin n))=ᵐ[gueFullMeasure n]gradient (f ∘guePermute n σ) := by
  let hp := gueFullMeasure_permutation_preserving hn σ
  constructor
  · exact (Lp.coeFn_compMeasurePreserving p.1 hp).trans (hp.quasiMeasurePreserving.ae_eq_comp hv)
  · have h1 := Lp.coeFn_compMeasurePreserving p.2 hp
    have h2 := (guePermuteIsometry n σ.symm).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
      (Lp.compMeasurePreserving (guePermute n σ) hp p.2)
    filter_upwards [h1, h2, hp.quasiMeasurePreserving.ae_eq_comp hg] with x hx1 hx2 hx3
    change _=gradient (f ∘guePermute n σ) x
    rw [guePermute_gradient n σ f (hf.of_le (by simp)) x]
    exact hx2.trans (congrArg (guePermute n σ.symm) (hx1.trans hx3))

theorem gueSobolevAverage_core {n : ℕ} (hn : 0<n)
    (p : GUEFullSobolevPair n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f)
    (hv : (p.1 : EuclideanSpace ℝ (Fin n) → ℝ)=ᵐ[gueFullMeasure n]f)
    (hg : (p.2 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))=ᵐ[gueFullMeasure n]gradient f) :
    ((gueSobolevAverage hn p).1 : EuclideanSpace ℝ (Fin n)→ℝ)=ᵐ[gueFullMeasure n]gueSmoothAverage n f ∧
    ((gueSobolevAverage hn p).2 : EuclideanSpace ℝ (Fin n)→EuclideanSpace ℝ (Fin n))=ᵐ[gueFullMeasure n]gradient (gueSmoothAverage n f) := by
  have hvσ σ := (gueSobolevPermutation_core hn σ p f hf hv hg).1
  have hgσ σ := (gueSobolevPermutation_core hn σ p f hf hv hg).2
  have he : gueSobolevAverage hn p=(Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ •∑σ, gueSobolevPermutation hn σ p := by
    simp [gueSobolevAverage]
  rw [he]
  simp only [Prod.smul_fst, Prod.fst_sum, Prod.smul_snd, Prod.snd_sum]
  constructor
  · change (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ • ∑σ, (gueSobolevPermutation hn σ p).1 : GUEFullValueL2 n) : _ →ℝ)=ᵐ[_]_
    refine (Lp.coeFn_smul _ _).trans ?_
    have hs := Lp.coeFn_finsetSum Finset.univ (fun σ => (gueSobolevPermutation hn σ p).1)
    filter_upwards [hs, Filter.eventually_all.mpr hvσ] with x hx hσ
    simp only [Pi.smul_apply, smul_eq_mul, hx, Finset.sum_apply, gueSmoothAverage]
    congr 1
    exact Finset.sum_congr rfl (fun σ _ => hσ σ)
  · change (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ • ∑σ, (gueSobolevPermutation hn σ p).2 : GUEFullGradientL2 n) : _ →_)=ᵐ[_]_
    refine (Lp.coeFn_smul _ _).trans ?_
    have hs := Lp.coeFn_finsetSum Finset.univ (fun σ => (gueSobolevPermutation hn σ p).2)
    filter_upwards [hs, Filter.eventually_all.mpr hgσ] with x hx hσ
    rw [gueSmoothAverage_gradient n f hf x]
    simp only [Pi.smul_apply, hx, Finset.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro σ hσ'
    exact (hσ σ).trans (guePermute_gradient n σ f (hf.of_le (by simp)) x)


theorem gueSobolevAverage_maps_core {n : ℕ} (hn : 0<n) :
    MapsTo (gueSobolevAverage hn) (gueFullSmoothPairs n) (guePaperSmoothPairs n) := by
  rintro p ⟨f, hf, hc, hv, hg⟩
  exact ⟨gueSmoothAverage n f, gueSmoothAverage_contDiff n f hf,
    gueSmoothAverage_compact n f hc, gueSmoothAverage_symmetric n f,
    (gueSobolevAverage_core hn p f hf hv hg).1, (gueSobolevAverage_core hn p f hf hv hg).2⟩

theorem gueSobolevAverage_fixed_core {n : ℕ} (hn : 0<n)
    (p : GUEFullSobolevPair n) (hp : p∈guePaperSmoothPairs n) : gueSobolevAverage hn p=p := by
  rcases hp with ⟨f, hf, hc, hs, hv, hg⟩
  have h := gueSobolevAverage_core hn p f hf hv hg
  rw [gueSmoothAverage_eq_of_symmetric n f hs] at h
  apply Prod.ext
  · exact Lp.ext (h.1.trans hv.symm)
  · exact Lp.ext (h.2.trans hg.symm)

/-- The paper's symmetric smooth completion is precisely the invariant subspace
of the unrestricted smooth completion, for the covariant permutation action on
values and ordinary gradients. -/
theorem guePaperH1Completion_iff_full_fixed_average {n : ℕ} (hn : 0<n)
    (p : GUEFullSobolevPair n) :
    p∈guePaperH1Completion n ↔ p∈gueFullH1Completion n ∧ gueSobolevAverage hn p=p := by
  constructor
  · intro hp
    constructor
    · exact closure_mono (by rintro q ⟨f, hf, hc, hs, hv, hg⟩; exact ⟨f, hf, hc, hv, hg⟩) hp
    · have hclosed : IsClosed {q : GUEFullSobolevPair n | gueSobolevAverage hn q=q} :=
        isClosed_eq (gueSobolevAverage hn).continuous continuous_id
      exact closure_minimal (fun q hq => gueSobolevAverage_fixed_core hn q hq) hclosed hp
  · rintro ⟨hp, hfix⟩
    have h := (gueSobolevAverage_maps_core hn).closure (gueSobolevAverage hn).continuous hp
    rwa [hfix] at h

#print axioms guePaperH1Completion_iff_full_fixed_average

end
end GinibrePoincare
