module

public import GinibrePoincare.Analysis.NonQuadraticRadialBochner

@[expose] public section

/-! # Nonlinear weighted Bochner identity for Fisher information -/
open MeasureTheory
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
private theorem compact_deriv_integral_zero (F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) : (∫ x, deriv F x) = 0 := by
  have hFc : Continuous F := hF.continuous
  have hdFc : Continuous (deriv F) :=
    (show ContDiff ℝ (0 + 1) F from hF).deriv'.continuous
  have hi : Integrable (deriv F) := hdFc.integrable_of_hasCompactSupport hc.deriv
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := F) (g := fun _ : ℝ => (1 : ℝ)) (v := (1 : ℝ))
    (by simpa only [fderiv_apply_one_eq_deriv, mul_one] using hi)
    (by simp) (by simpa using hFc.integrable_of_hasCompactSupport hc)
    (fun x _ => (hF.differentiable (by norm_num)) x)
    (fun x _ => differentiableAt_const 1)
  simp only [fderiv_apply_one_eq_deriv, deriv_const, mul_zero, integral_zero, mul_one] at he
  linarith


/-- The cubic logarithmic-gradient divergence vanishes exactly. This is the
nonlinear correction needed to convert the linear Bochner identity into
Fisher-information dissipation. -/
theorem scalarConfinement_cubic_gradient_identity (W φ : ℝ → ℝ)
    (hW : ContDiff ℝ 2 W) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, deriv (deriv φ) x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) =
      -(1 / 2) * ∫ x, scalarConfinementGenerator (W - φ) φ x *
        deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x := by
  have hφ1 : ContDiff ℝ 1 (deriv φ) := (show ContDiff ℝ (1 + 1) φ from hφ).deriv'
  have hφ2c : Continuous (deriv (deriv φ)) :=
    (show ContDiff ℝ (0 + 1) (deriv φ) from hφ1).deriv'.continuous
  have hB : ContDiff ℝ 2 (W - φ) := hW.sub hφ
  have hB1 : ContDiff ℝ 1 (deriv (W - φ)) := (show ContDiff ℝ (1 + 1) (W - φ) from hB).deriv'
  have hw : ContDiff ℝ 1 (scalarConfinementWeight (W - φ)) :=
    Real.contDiff_exp.comp ((hB.of_le (by norm_num)).neg)
  let D := fun x => deriv φ x ^ 3 * scalarConfinementWeight (W - φ) x
  have hD : ContDiff ℝ 1 D := (hφ1.pow 3).mul hw
  have hcD : HasCompactSupport D := by
    apply hc.deriv.mono
    intro x hx hz
    apply hx
    simp [D, hz]
  have hd (x : ℝ) : deriv D x =
      2 * (deriv (deriv φ) x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) +
        scalarConfinementGenerator (W - φ) φ x * deriv φ x ^ 2 *
          scalarConfinementWeight (W - φ) x := by
    have hp := ((hφ1.differentiable (by norm_num)) x).hasDerivAt
    have hb := ((hB.differentiable (by norm_num)) x).hasDerivAt.neg.exp
    have he := (hp.pow 3).mul hb
    change HasDerivAt D _ x at he
    rw [he.deriv]
    dsimp [scalarConfinementGenerator, scalarConfinementWeight]
    ring
  have hi : Integrable (fun x => deriv (deriv φ) x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) := by
    apply ((hφ2c.mul (hφ1.continuous.pow 2)).mul hw.continuous).integrable_of_hasCompactSupport
    apply hc.deriv.mono
    intro x hx hz
    apply hx
    simp [hz]
  have hig : Integrable (fun x => scalarConfinementGenerator (W - φ) φ x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) := by
    apply (((hφ2c.sub (hB1.continuous.mul hφ1.continuous)).mul
      (hφ1.continuous.pow 2)).mul hw.continuous).integrable_of_hasCompactSupport
    apply hc.deriv.mono
    intro x hx hz
    apply hx
    simp [hz]
  have hz := compact_deriv_integral_zero D hD hcD
  simp_rw [hd] at hz
  rw [integral_add (hi.const_mul 2) hig, integral_const_mul] at hz
  linarith

/-- Exact nonlinear Γ₂ identity in logarithmic coordinates. All integrals
are concrete; the cubic correction is proved rather than assumed. -/
theorem scalarConfinement_fisher_bochner_identity (W φ : ℝ → ℝ)
    (hW : ContDiff ℝ 2 W) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, scalarConfinementGenerator (W - φ) φ x ^ 2 * scalarConfinementWeight (W - φ) x) -
      (1 / 2) * (∫ x, scalarConfinementGenerator (W - φ) φ x *
        deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) =
      (∫ x, deriv (deriv φ) x ^ 2 * scalarConfinementWeight (W - φ) x) +
        ∫ x, deriv (deriv W) x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x := by
  have hW1 : ContDiff ℝ 1 (deriv W) := (show ContDiff ℝ (1 + 1) W from hW).deriv'
  have hφ1 : ContDiff ℝ 1 (deriv φ) := (show ContDiff ℝ (1 + 1) φ from hφ).deriv'
  have hW2c : Continuous (deriv (deriv W)) :=
    (show ContDiff ℝ (0 + 1) (deriv W) from hW1).deriv'.continuous
  have hφ2c : Continuous (deriv (deriv φ)) :=
    (show ContDiff ℝ (0 + 1) (deriv φ) from hφ1).deriv'.continuous
  have hw : Continuous (scalarConfinementWeight (W - φ)) :=
    (Real.contDiff_exp.comp ((show ContDiff ℝ 1 (W - φ) from
      (hW.sub hφ).of_le (by norm_num)).neg)).continuous
  have hd : deriv (W - φ) = deriv W - deriv φ := by
    funext x
    exact deriv_sub ((hW.differentiable (by norm_num)) x)
      ((hφ.differentiable (by norm_num)) x)
  have hdd (x : ℝ) : deriv (deriv (W - φ)) x =
      deriv (deriv W) x - deriv (deriv φ) x := by
    rw [hd]
    exact deriv_sub ((hW1.differentiable (by norm_num)) x)
      ((hφ1.differentiable (by norm_num)) x)
  have hiW : Integrable (fun x => deriv (deriv W) x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) := by
    apply ((hW2c.mul (hφ1.continuous.pow 2)).mul hw).integrable_of_hasCompactSupport
    apply hc.deriv.mono
    intro x hx hz
    apply hx
    simp [hz]
  have hiφ : Integrable (fun x => deriv (deriv φ) x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) := by
    apply ((hφ2c.mul (hφ1.continuous.pow 2)).mul hw).integrable_of_hasCompactSupport
    apply hc.deriv.mono
    intro x hx hz
    apply hx
    simp [hz]
  have hb := scalarConfinement_bochner_identity (W - φ) φ (hW.sub hφ) hφ hc
  have hcubic := scalarConfinement_cubic_gradient_identity W φ hW hφ hc
  have he : (∫ x, deriv (deriv (W - φ)) x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) =
      (∫ x, deriv (deriv W) x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) -
      (∫ x, deriv (deriv φ) x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) := by
    simp_rw [hdd, sub_mul]
    exact integral_sub hiW hiφ
  rw [he] at hb
  linarith

/-- Curvature gives the exact nonlinear Fisher-information dissipation
bound, with no φ'' error term remaining. -/
theorem scalarConfinement_fisher_curvature_bound (W φ : ℝ → ℝ) (κ : ℝ)
    (hW : ContDiff ℝ 2 W) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hcurv : ∀ x ∈ tsupport φ, κ ≤ deriv (deriv W) x) :
    κ * (∫ x, deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) ≤
      (∫ x, scalarConfinementGenerator (W - φ) φ x ^ 2 * scalarConfinementWeight (W - φ) x) -
        (1 / 2) * (∫ x, scalarConfinementGenerator (W - φ) φ x *
          deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) := by
  rw [scalarConfinement_fisher_bochner_identity W φ hW hφ hc]
  have hW1 : ContDiff ℝ 1 (deriv W) := (show ContDiff ℝ (1 + 1) W from hW).deriv'
  have hφ1 : ContDiff ℝ 1 (deriv φ) := (show ContDiff ℝ (1 + 1) φ from hφ).deriv'
  have hW2c : Continuous (deriv (deriv W)) :=
    (show ContDiff ℝ (0 + 1) (deriv W) from hW1).deriv'.continuous
  have hw : Continuous (scalarConfinementWeight (W - φ)) :=
    (Real.contDiff_exp.comp ((show ContDiff ℝ 1 (W - φ) from
      (hW.sub hφ).of_le (by norm_num)).neg)).continuous
  have hip : Integrable (fun x => deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) := by
    apply ((hφ1.continuous.pow 2).mul hw).integrable_of_hasCompactSupport
    apply hc.deriv.mono
    intro x hx hz
    apply hx
    simp [hz]
  have hiW : Integrable (fun x => deriv (deriv W) x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) := by
    apply ((hW2c.mul (hφ1.continuous.pow 2)).mul hw).integrable_of_hasCompactSupport
    apply hc.deriv.mono
    intro x hx hz
    apply hx
    simp [hz]
  have hle : κ * (∫ x, deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) ≤
      ∫ x, deriv (deriv W) x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x := by
    rw [← integral_const_mul]
    apply integral_mono (hip.const_mul κ) hiW
    intro x
    have hp : 0 ≤ deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x :=
      mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    by_cases hx : x ∈ tsupport φ
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hcurv x hx) hp
    · have hd0 : deriv φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hx' => hx (tsupport_deriv_subset hx'))
      simp [hd0]
  exact hle.trans (le_add_of_nonneg_left (integral_nonneg (fun x =>
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)))

/-- Nonlinear Fisher coercivity localized to an open set. In particular,
no smoothness across zero is needed for radial logarithmic barriers. -/
theorem scalarConfinement_fisher_curvature_bound_on_open
    (W φ : ℝ → ℝ) (κ : ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hW : ∀ x ∈ U, ContDiffAt ℝ 2 W x) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hcurv : ∀ x ∈ tsupport φ, κ ≤ deriv (deriv W) x) :
    κ * (∫ x, deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) ≤
      (∫ x, scalarConfinementGenerator (W - φ) φ x ^ 2 * scalarConfinementWeight (W - φ) x) -
        (1 / 2) * (∫ x, scalarConfinementGenerator (W - φ) φ x *
          deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) := by
  obtain ⟨We, hWe, he⟩ := exists_contDiff_extension_near_closed W (tsupport φ) U
    (isClosed_tsupport φ) hU hs hW
  have hce : ∀ x ∈ tsupport φ, κ ≤ deriv (deriv We) x := by
    intro x hx
    rw [(he x hx).deriv.deriv_eq]
    exact hcurv x hx
  have hi := scalarConfinement_fisher_curvature_bound We φ κ hWe hφ hc hce
  have hp (x : ℝ) :
      deriv φ x ^ 2 * scalarConfinementWeight (We - φ) x =
        deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x ∧
      scalarConfinementGenerator (We - φ) φ x ^ 2 * scalarConfinementWeight (We - φ) x =
        scalarConfinementGenerator (W - φ) φ x ^ 2 * scalarConfinementWeight (W - φ) x ∧
      scalarConfinementGenerator (We - φ) φ x * deriv φ x ^ 2 * scalarConfinementWeight (We - φ) x =
        scalarConfinementGenerator (W - φ) φ x * deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x := by
    by_cases hx : x ∈ tsupport φ
    · have ht : We - φ =ᶠ[𝓝 x] W - φ := (he x hx).sub Filter.EventuallyEq.rfl
      simp only [scalarConfinementWeight, scalarConfinementGenerator,
        ht.self_of_nhds, ht.deriv_eq, and_self]
    · have hd0 : deriv φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hx' => hx (tsupport_deriv_subset hx'))
      have hdd0 : deriv (deriv φ) x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hx' => hx (tsupport_deriv_subset (tsupport_deriv_subset hx')))
      simp [scalarConfinementGenerator, hd0, hdd0]
  have hb := funext (fun x => (hp x).1)
  have hg := funext (fun x => (hp x).2.1)
  have hm := funext (fun x => (hp x).2.2)
  rwa [hb, hg, hm] at hi

/-- Genuine nonlinear curvature coercivity for every actual radial
coordinate law, at the exact curvature scale nρ. -/
theorem radialConfinement_fisher_curvature_bound (n k : ℕ) (hk : 1 ≤ k) (ρ : ℝ)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hcV : IsRhoConvexPotential ρ V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Set.Ioi 0) :
    let W := radialEffectivePotential n k (fun t : ℝ => V (t : ℂ))
    (n : ℝ) * ρ * (∫ x, deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) ≤
      (∫ x, scalarConfinementGenerator (W - φ) φ x ^ 2 * scalarConfinementWeight (W - φ) x) -
        (1 / 2) * (∫ x, scalarConfinementGenerator (W - φ) φ x *
          deriv φ x ^ 2 * scalarConfinementWeight (W - φ) x) := by
  dsimp only
  exact scalarConfinement_fisher_curvature_bound_on_open _ φ ((n : ℝ) * ρ) (Set.Ioi 0)
    isOpen_Ioi (fun x hx => contDiffAt_radialEffectivePotential n k hV x hx) hφ hc hs
    (fun x hx => rhoConvexPotential_radial_curvature n k hk ρ hV hcV x (hs hx))

end
end GinibrePoincare
