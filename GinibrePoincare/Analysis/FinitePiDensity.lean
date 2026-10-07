module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# Densities of finite product measures

This file proves that a finite product of measures with densities has density
the product of the coordinate densities.  Mathlib contains the binary version
(`Measure.prod_withDensity`); the theorem below packages its finite dependent
product analogue.
-/

open Fintype MeasureTheory

namespace GinibrePoincare

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- Tonelli's product formula for a product of `ℝ≥0∞`-valued functions on a
finite dependent product. -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : ∀ i : Fin n, E i → ENNReal)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0) *
            ∫⁻ x : (i : Fin n) → E (Fin.succ i),
              ∏ i, f (Fin.succ i) (x i) ∂(Measure.pi (fun i ↦ μ i.succ)) := by
          have hg : AEMeasurable
              (fun x : (i : Fin n) → E (Fin.succ i) ↦
                ∏ i, f (Fin.succ i) (x i))
              (Measure.pi (fun i ↦ μ (Fin.succ i))) :=
            Finset.aemeasurable_fun_prod Finset.univ fun i _ ↦
              (hf (Fin.succ i)).aemeasurable.comp_quasiMeasurePreserving
                (Measure.quasiMeasurePreserving_eval _ i)
          exact lintegral_prod_mul (μ := μ 0)
            (ν := Measure.pi (fun i ↦ μ (Fin.succ i))) (hf 0).aemeasurable hg
        _ = (∫⁻ x, f 0 x ∂μ 0) *
            ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ i.succ) := by
          rw [ih (fun i ↦ f i.succ) (fun i ↦ hf i.succ)]
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
          rw [Fin.prod_univ_succ]

set_option backward.isDefEq.respectTransparency false in
/-- Tonelli's product formula for a product of `ℝ≥0∞`-valued functions indexed
by an arbitrary finite type. -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : ∀ i : ι, E i → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  rw [lintegral_fin_nat_prod_eq_prod _ (fun i ↦ hf _)]

/-- A finite product of coordinate measures with measurable densities is the
product base measure with the product density. -/
theorem Measure.pi_withDensity {ι : Type*} [Fintype ι]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i : ι, E i → ENNReal) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  simp_rw [withDensity_apply _ (hs _)]
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [← lintegral_indicator (hs _)]
  rw [← lintegral_fintype_prod_eq_prod
    (fun i x ↦ (s i).indicator (f i) x)
    (fun i ↦ (hf i).indicator (hs i))]
  apply lintegral_congr
  intro x
  simp only [Set.indicator]
  split_ifs with h
  · have hh : ∀ i, x i ∈ s i := by simpa [Set.mem_pi] using h
    simp_rw [if_pos (hh _)]
  · have hh : ¬ ∀ i, x i ∈ s i := by simpa [Set.mem_pi] using h
    push Not at hh
    obtain ⟨i, hi⟩ := hh
    symm
    apply Finset.prod_eq_zero (s := Finset.univ)
    · exact Finset.mem_univ i
    · exact if_neg hi

end

end GinibrePoincare
