module

public import GinibrePoincare.Analysis.GinibreFullGeneratorVariational
public import GinibrePoincare.Analysis.GinibreEqualityWeakVariational

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

lemma ginibreEquality_centered_inner {n : ℕ} (hn : 0 < n)
    (u w : GinibreFullValueL2 n) (hu : ginibreL2Mean n u = 0) :
    inner ℝ (ginibreFullCenter n hn u) (ginibreFullCenter n hn w) = inner ℝ u w := by
  have huc (c : ℝ) : inner ℝ u (ginibreRealConstantL2 n hn c) = 0 := by
    rw [L2.inner_def]
    have he : (fun z => inner ℝ (u z) ((ginibreRealConstantL2 n hn c) z)) =ᵐ[ginibreMeasure n]
        fun z => c * u z := by
      filter_upwards [ginibreRealConstantL2_ae n hn c] with z hz
      rw [hz]
      rfl
    rw [integral_congr_ae he, integral_const_mul]
    change c * ginibreL2Mean n u = 0
    rw [hu, mul_zero]
  rw [ginibreFullCenter_apply, ginibreFullCenter_apply, hu]
  have hc : ginibreRealConstantL2 n hn 0 = 0 := by
    apply Lp.ext
    filter_upwards [ginibreRealConstantL2_ae n hn 0, Lp.coeFn_zero ℝ 2 (ginibreMeasure n)]
      with z hz hzero
    exact hz.trans hzero.symm
  rw [hc, sub_zero, inner_sub_right, huc, sub_zero]

/-- Sharp full weak-domain equality for a mean-zero observable is exactly the
actual full generator eigenvalue equation at the gap 2. -/
theorem ginibreEquality_full_generator_iff {n : ℕ} (hn : 0 < n)
    (u : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u.val g)
    (hs : IsGinibreSymmetricWeakPair (u.val, g))
    (hm : ginibreL2Mean n u.val = 0) :
    ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u.val ↔
      (ginibreFullSymmetricOfReal n u, (-2 : ℂ) • ginibreFullSymmetricOfReal n u) ∈
        (ginibreFullGenerator n hn).graph := by
  let p : ginibreFullWeakSpace n hn := ⟨(u.val, g), hu, hs⟩
  have hv : ginibreFullSymmetricOfReal n ((-2 : ℝ) • u) =
      (-2 : ℂ) • ginibreFullSymmetricOfReal n u := by
    rw [map_smul]
    rw [← algebraMap_smul ℂ (-2 : ℝ)]
    norm_num only [map_neg, map_ofNat]
  rw [← hv, ginibreFullGenerator_ofReal_variational_iff hn u ((-2 : ℝ) • u) g hu hs]
  rw [ginibreEquality_weak_variational_iff n hn p]
  constructor
  · intro heq w h hw hsw
    let q : ginibreFullWeakSpace n hn := ⟨(w, h), hw, hsw⟩
    have he := heq q
    rw [ginibreEquality_centered_inner hn u.val w hm] at he
    simpa only [Submodule.coe_smul, real_inner_smul_left, neg_mul, neg_neg] using he
  · intro heq q
    have he := heq q.val.1 q.val.2 q.property.1 q.property.2
    rw [ginibreEquality_centered_inner hn u.val q.val.1 hm]
    simpa only [Submodule.coe_smul, real_inner_smul_left, neg_mul, neg_neg] using he

end GinibrePoincare
