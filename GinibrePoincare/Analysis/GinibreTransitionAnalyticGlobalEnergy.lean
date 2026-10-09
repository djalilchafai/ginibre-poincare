module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticEnergyCompactness
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticCutoffExhaustion

@[expose] public section

/-! A bounded genuine locally weak resolvent solution has a global Ginibre
L² gradient, derived from actual cutoff tests and zero boundary capacity. -/
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem ginibreTransitionAnalytic_local_resolvent_global_gradient_memLp
    {n : ℕ} (hn : 0 < n) (u f : Configuration n → ℝ)
    (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : MemLp u 2 (ginibreMeasure n)) (hf : MemLp f 2 (ginibreMeasure n))
    (hg : AEStronglyMeasurable g (ginibreMeasure n))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ z, ‖u z‖ ≤ A)
    (ℓ c : ℝ) (hℓ : 0 < ℓ) (hc : 0 < c)
    (hlocal : ∀ (η : Configuration n → ℝ), IsTheoremOneNineCore η →
      MemLp (fun z => η z • g z) 2 (ginibreMeasure n))
    (heq : ∀ (η : Configuration n → ℝ), IsTheoremOneNineCore η →
      ℓ*(∫ z, (η z*u z)^2 ∂ginibreMeasure n)+c*(∫ z, ‖η z • g z‖^2 ∂ginibreMeasure n) =
      (∫ z, (η z*f z)*(η z*u z) ∂ginibreMeasure n)-
        2*c*(∫ z, inner ℝ (η z • g z) (u z • ginibreEuclideanGradient η z) ∂ginibreMeasure n)) :
    MemLp g 2 (ginibreMeasure n) := by
  let μ := ginibreMeasure n
  obtain ⟨η, hcore, hunit, hpoint, henergy⟩ := ginibreTransitionAnalytic_vanishing_energy_cutoffs hn
  have hev : ∀ᶠ m : ℕ in atTop, (∫ z, ‖ginibreEuclideanGradient (η m) z‖^2 ∂μ) ≤ 1 := by
    exact (henergy.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))).mono fun m hm => hm.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let q := fun m : ℕ => N+m
  have hq (m : ℕ) : N ≤ q m := Nat.le_add_right N m
  have hcutbound (m : ℕ) (z : Configuration n) : ‖η (q m) z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hunit (q m) z).1]
    exact (hunit (q m) z).2
  let U := fun m z => η (q m) z*u z
  let F := fun m z => η (q m) z*f z
  let G := fun m z => η (q m) z • g z
  let H := fun m z => u z • ginibreEuclideanGradient (η (q m)) z
  have hU (m : ℕ) : MemLp (U m) 2 μ := hu.of_le
    ((hcore (q m)).1.continuous.aestronglyMeasurable.mul hu.aestronglyMeasurable)
    (ae_of_all μ fun z => by
      rw [show U m z=η (q m) z*u z from rfl, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hcutbound m z))
  have hF (m : ℕ) : MemLp (F m) 2 μ := hf.of_le
    ((hcore (q m)).1.continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (ae_of_all μ fun z => by
      rw [show F m z=η (q m) z*f z from rfl, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hcutbound m z))
  have hG (m : ℕ) : MemLp (G m) 2 μ := hlocal _ (hcore (q m))
  have hgrad (m : ℕ) := (ginibreFull_smoothCompact_memLp n hn (η (q m))
    (hcore (q m)).1 (hcore (q m)).2.1).2
  have hH (m : ℕ) : MemLp (H m) 2 μ := (hgrad m).of_le_mul
    (hu.aestronglyMeasurable.smul (hgrad m).aestronglyMeasurable)
    (ae_of_all μ fun z => by
      rw [show H m z=u z • ginibreEuclideanGradient (η (q m)) z from rfl, norm_smul]
      exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _))
  have hFE (m : ℕ) : (∫ z, (F m z)^2 ∂μ) ≤ ∫ z, (f z)^2 ∂μ := by
    apply integral_mono (hF m).integrable_sq hf.integrable_sq
    intro z
    have hh : ‖F m z‖ ≤ ‖f z‖ := by
      rw [show F m z=η (q m) z*f z from rfl, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hcutbound m z)
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hHE (m : ℕ) : (∫ z, ‖H m z‖^2 ∂μ) ≤ A^2 := by
    have hh := integral_mono (hH m).norm.integrable_sq ((hgrad m).norm.integrable_sq.const_mul (A^2))
      (fun z => by
        rw [show H m z=u z • ginibreEuclideanGradient (η (q m)) z from rfl, norm_smul, mul_pow]
        have hu2 : ‖u z‖^2 ≤ A^2 := pow_le_pow_left₀ (norm_nonneg _) (hb z) 2
        exact mul_le_mul_of_nonneg_right hu2 (sq_nonneg _))
    rw [integral_const_mul] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (hN (q m) (hq m)) (sq_nonneg A)).trans_eq (mul_one _))
  let D := (∫ z, (f z)^2 ∂μ)/(c*ℓ)+4*A^2
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hGE (m : ℕ) : (∫ z, ‖G m z‖^2 ∂μ) ≤ D := by
    have hh := localResolventCaccioppoli_energy_bound μ (U m) (F m) (G m) (H m)
      (hU m) (hF m) (hG m) (hH m) ℓ c hℓ hc (heq _ (hcore (q m)))
    have hUne : 0 ≤ (∫ z, (U m z)^2 ∂μ) := integral_nonneg fun z => sq_nonneg _
    have hFne : 0 ≤ (∫ z, (f z)^2 ∂μ) := integral_nonneg fun z => sq_nonneg _
    have hFbound := hFE m
    have hHbound := hHE m
    have hscaled : ℓ^2*(∫ z, (U m z)^2 ∂μ)+c*ℓ*(∫ z, ‖G m z‖^2 ∂μ) ≤
        (∫ z, (F m z)^2 ∂μ)+4*c*ℓ*(∫ z, ‖H m z‖^2 ∂μ) := by
      calc
        _ = (2*ℓ)*((ℓ/2)*(∫ z, (U m z)^2 ∂μ)+(c/2)*(∫ z, ‖G m z‖^2 ∂μ)) := by ring
        _ ≤ (2*ℓ)*((1/(2*ℓ))*(∫ z, (F m z)^2 ∂μ)+2*c*(∫ z, ‖H m z‖^2 ∂μ)) :=
          mul_le_mul_of_nonneg_left hh (by positivity)
        _ = _ := by field_simp; ring
    have hHscaled := mul_le_mul_of_nonneg_left hHbound (show 0 ≤ 4*c*ℓ by positivity)
    have hEq : D=((∫ z, (f z)^2 ∂μ)+4*A^2*(c*ℓ))/(c*ℓ) := by dsimp [D]; field_simp <;> ring
    rw [hEq]
    apply (le_div_iff₀ (mul_pos hc hℓ)).mpr
    nlinarith [mul_nonneg (sq_nonneg ℓ) hUne]
  apply actualL2Limit_memLp_of_energy_bound μ G g hG hg D hD hGE
  filter_upwards [ginibre_ae_collisionFree n hn] with z hz
  have hqtop : Tendsto q atTop atTop := tendsto_atTop_mono (fun m => Nat.le_add_left m N) tendsto_id
  simpa only [G, one_smul, Function.comp_def] using ((hpoint z hz).comp hqtop).smul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => g z) atTop (𝓝 (g z)))

#print axioms ginibreTransitionAnalytic_local_resolvent_global_gradient_memLp
end
end GinibrePoincare
