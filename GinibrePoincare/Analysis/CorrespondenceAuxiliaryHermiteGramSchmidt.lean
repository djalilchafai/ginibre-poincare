module

public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryTriangularGramSchmidt
public import GinibrePoincare.Analysis.GaussianHermiteMoments
public import GinibrePoincare.Analysis.HermiteL2Family
public import Mathlib.Data.Nat.Pairing

@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option maxHeartbeats 800000

private def singleHermite (p q : ℕ) : Lp ℂ 2 (complexGaussianMeasure 1) :=
  multivariateNormalizedL2 1 (by decide) (fun _ => p) (fun _ => q)
private def singleMonomial (p q : ℕ) : Lp ℂ 2 (complexGaussianMeasure 1) :=
  multivariateMixedMonomialL2 1 (by decide) (fun _ => p) (fun _ => q)
private def hermiteScale (p q : ℕ) : ℝ :=
  oneDimNormalization 1 p * oneDimNormalization 1 q
private def rawScalar (p q k : ℕ) : ℂ :=
  (-1)^k * (k.factorial : ℂ) * (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)

private theorem hermiteScale_pos (p q : ℕ) : 0 < hermiteScale p q := by
  unfold hermiteScale oneDimNormalization
  positivity

private theorem singleHermite_expansion (p q : ℕ) :
    singleHermite p q = (hermiteScale p q : ℂ) •
      ∑ k ∈ Finset.range (min p q+1), rawScalar p q k • singleMonomial (p-k) (q-k) := by
  apply Lp.ext
  have hm (p q : ℕ) : (singleMonomial p q : Configuration 1 → ℂ) =ᵐ[complexGaussianMeasure 1]
      (fun z => z 0 ^ p * conj (z 0) ^ q) := by
    simpa only [singleMonomial, multivariateMixedMonomialL2, Fin.prod_univ_one] using
      (memLp_two_multivariateMixedMonomial 1 (by decide) (fun _ => p) (fun _ => q)).coeFn_toLp
  have hs := Lp.coeFn_smul (hermiteScale p q : ℂ)
    (∑ k ∈ Finset.range (min p q+1), rawScalar p q k • singleMonomial (p-k) (q-k))
  have hsum := Lp.coeFn_fun_finsetSum (Finset.range (min p q+1))
    (fun k => rawScalar p q k • singleMonomial (p-k) (q-k))
  have hall : ∀ᵐ z ∂complexGaussianMeasure 1, ∀ k : ℕ,
      (rawScalar p q k • singleMonomial (p-k) (q-k)) z =
        rawScalar p q k * (z 0 ^ (p-k)*conj (z 0)^(q-k)) := by
    rw [ae_all_iff]
    intro k
    filter_upwards [Lp.coeFn_smul (rawScalar p q k) (singleMonomial (p-k) (q-k)),
      hm (p-k) (q-k)] with z h1 h2
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul, h2]
  filter_upwards [multivariateNormalizedL2_coeFn 1 (by decide) (fun _ => p) (fun _ => q),
    hs, hsum, hall] with z hg hs hsum hall
  change (multivariateNormalizedL2 1 (by decide) (fun _ => p) (fun _ => q) : Configuration 1 → ℂ) z = _
  rw [hg, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hsum, Fin.prod_univ_one, multivariateNormalized]
  rw [normalizedEval_eq_sum]
  change (hermiteScale p q : ℂ) * _ = (hermiteScale p q : ℂ) * _
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [hall k]
  simp [rawScalar, mul_assoc]

private theorem singleMonomial_mem_rectangle (p q : ℕ) :
    singleMonomial p q ∈ Submodule.span ℂ
      {v | ∃ r ≤ p, ∃ s ≤ q, v = singleHermite r s} := by
  let S := Submodule.span ℂ {v | ∃ r ≤ p, ∃ s ≤ q, v = singleHermite r s}
  have lift : ∀ {f : ℂ → ℂ}, f ∈ normalizedEvalRectangleSpan 1 (by decide) p q →
      ∃ hf : MemLp (fun z : Configuration 1 => f (z 0)) 2 (complexGaussianMeasure 1),
        hf.toLp (fun z : Configuration 1 => f (z 0)) ∈ S := by
    intro f h
    induction h using Submodule.span_induction with
    | mem f h =>
      obtain ⟨r, hr, s, hs, rfl⟩ := h
      have he : (fun z : Configuration 1 => normalizedEval 1 (by decide) r s (z 0)) =
          multivariateNormalized 1 (by decide) (fun _ => r) (fun _ => s) := by
        funext z
        simp [multivariateNormalized, Fin.prod_univ_one]
      have hm : MemLp (fun z : Configuration 1 => normalizedEval 1 (by decide) r s (z 0))
          2 (complexGaussianMeasure 1) := by
        rw [he]
        exact memLp_two_multivariateNormalized 1 (by decide) _ _
      refine ⟨hm,?_⟩
      have heLp : hm.toLp _ = singleHermite r s := by
        apply Lp.ext
        filter_upwards [hm.coeFn_toLp, multivariateNormalizedL2_coeFn 1 (by decide)
          (fun _ => r) (fun _ => s)] with z h1 h2
        rw [h1]
        simpa [singleHermite, multivariateNormalized, Fin.prod_univ_one] using h2.symm
      rw [heLp]
      exact Submodule.subset_span ⟨r, hr, s, hs, rfl⟩
    | zero => exact ⟨MemLp.zero, by simp⟩
    | add f g hf hg ihf ihg =>
      obtain ⟨hfm, hfs⟩ := ihf
      obtain ⟨hgm, hgs⟩ := ihg
      refine ⟨hfm.add hgm,?_⟩
      change (hfm.add hgm).toLp ((fun z : Configuration 1 => f (z 0)) +
        (fun z : Configuration 1 => g (z 0))) ∈ S
      rw [MemLp.toLp_add hfm hgm]
      exact S.add_mem hfs hgs
    | smul c f hf ih =>
      obtain ⟨hfm, hfs⟩ := ih
      refine ⟨hfm.const_smul c,?_⟩
      change (hfm.const_smul c).toLp (c • (fun z : Configuration 1 => f (z 0))) ∈ S
      rw [MemLp.toLp_const_smul c hfm]
      exact S.smul_mem c hfs
  obtain ⟨hm, hs⟩ := lift (mixedMonomial_mem_normalizedEvalRectangleSpan 1 (by decide) p q)
  have he : hm.toLp _ = singleMonomial p q := by
    apply Lp.ext
    filter_upwards [hm.coeFn_toLp,
      (memLp_two_multivariateMixedMonomial 1 (by decide) (fun _ => p) (fun _ => q)).coeFn_toLp]
      with z h1 h2
    rw [h1]
    simpa [singleMonomial, multivariateMixedMonomialL2, Fin.prod_univ_one] using h2.symm
  simpa [he] using hs

private def pairedHermite (i : ℕ) := singleHermite (Nat.unpair i).1 (Nat.unpair i).2
private def pairedMonomial (i : ℕ) := singleMonomial (Nat.unpair i).1 (Nat.unpair i).2

private theorem singleMonomial_mem_previous (p q k : ℕ)
    (hk0 : 0 < k) (hkp : k ≤ p) (hkq : k ≤ q) :
    singleMonomial (p-k) (q-k) ∈ Submodule.span ℂ
      (pairedHermite '' Set.Iio (Nat.pair p q)) := by
  apply Submodule.span_mono _ (singleMonomial_mem_rectangle (p-k) (q-k))
  rintro v ⟨r, hr, s, hs, rfl⟩
  refine ⟨Nat.pair r s,?_,?_⟩
  · have hleft : Nat.pair r s ≤ Nat.pair (p-k) s :=
      (show StrictMono (fun a => Nat.pair a s) from
        fun _ _ h => Nat.pair_lt_pair_left s h).monotone hr
    have hright : Nat.pair (p-k) s ≤ Nat.pair (p-k) q :=
      (show StrictMono (fun b => Nat.pair (p-k) b) from
        fun _ _ h => Nat.pair_lt_pair_right (p-k) h).monotone (hs.trans (Nat.sub_le q k))
    exact lt_of_le_of_lt (hleft.trans hright) (Nat.pair_lt_pair_left q (by omega))
  · simp [pairedHermite, Nat.unpair_pair]

private theorem pairedMonomial_triangular (i : ℕ) :
    pairedMonomial i - ((hermiteScale (Nat.unpair i).1 (Nat.unpair i).2 : ℝ) : ℂ)⁻¹ • pairedHermite i ∈
      Submodule.span ℂ (pairedHermite '' Set.Iio i) := by
  let p := (Nat.unpair i).1
  let q := (Nat.unpair i).2
  let rest := ∑ k ∈ (Finset.range (min p q+1)).erase 0,
    rawScalar p q k • singleMonomial (p-k) (q-k)
  have hrest : rest ∈ Submodule.span ℂ (pairedHermite '' Set.Iio i) := by
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    have hkr := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
    have hk0 := (Finset.mem_erase.mp hk).1
    have h := singleMonomial_mem_previous p q k (by omega) (by omega) (by omega)
    simpa [p, q, Nat.pair_unpair] using h
  have hg : singleHermite p q = (hermiteScale p q : ℂ) • (singleMonomial p q+rest) := by
    rw [singleHermite_expansion]
    congr 1
    have hz : 0 ∈ Finset.range (min p q+1) := by simp
    rw [← Finset.add_sum_erase _ _ hz]
    simp [rawScalar, rest]
  have he : pairedMonomial i - ((hermiteScale p q : ℝ) : ℂ)⁻¹ • pairedHermite i = -rest := by
    change singleMonomial p q - ((hermiteScale p q : ℝ) : ℂ)⁻¹ • singleHermite p q = _
    rw [hg]
    rw [smul_smul]
    simp only [inv_mul_cancel₀
      (Complex.ofReal_ne_zero.mpr (hermiteScale_pos p q).ne'), one_smul]
    abel
  rw [he]
  exact Submodule.neg_mem _ hrest

/-- The actual normalized Gram–Schmidt algorithm applied to mixed monomials,
in the explicit square-shell pairing order, recovers the univariate complex
Hermites of precision one. No orthogonalization certificate is supplied. -/
theorem gaussian_one_mixed_monomial_gramSchmidt (i : ℕ) :
    InnerProductSpace.gramSchmidtNormed ℂ
      (fun j : ℕ => multivariateMixedMonomialL2 1 (by decide)
        (fun _ => (Nat.unpair j).1) (fun _ => (Nat.unpair j).2)) i =
      multivariateNormalizedL2 1 (by decide)
        (fun _ => (Nat.unpair i).1) (fun _ => (Nat.unpair i).2) := by
  have hg : Orthonormal ℂ pairedHermite := by
    let e : ℕ → HermiteMultiIndex 1 := fun i =>
      ((fun _ => (Nat.unpair i).1), (fun _ => (Nat.unpair i).2))
    have he : Function.Injective e := by
      intro i j hij
      have hp := congrArg (fun x : HermiteMultiIndex 1 => x.1 0) hij
      have hq := congrArg (fun x : HermiteMultiIndex 1 => x.2 0) hij
      have hu : Nat.unpair i = Nat.unpair j := Prod.ext hp hq
      have h := congrArg (fun x : ℕ × ℕ => Nat.pair x.1 x.2) hu
      simpa [Nat.pair_unpair] using h
    exact (orthonormal_hermiteL2Family_gaussian 1 (by decide)).comp e he
  have ht := gramSchmidtNormed_of_positive_triangular pairedMonomial pairedHermite hg
    (fun i => (hermiteScale (Nat.unpair i).1 (Nat.unpair i).2)⁻¹)
    (fun i => inv_pos.mpr (hermiteScale_pos _ _))
    (fun i => by simpa only [Complex.ofReal_inv] using pairedMonomial_triangular i)
  exact congrFun ht i

#print axioms gaussian_one_mixed_monomial_gramSchmidt

#print axioms pairedMonomial_triangular

#print axioms singleHermite_expansion
end
end GinibrePoincare
