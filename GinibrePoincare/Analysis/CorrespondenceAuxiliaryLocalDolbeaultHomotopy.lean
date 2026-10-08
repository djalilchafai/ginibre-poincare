module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenParametricHomotopy

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem dolbeaultReplaceCoordinate_vertical {n : ℕ} (j : Fin n) (w : ℂ) :
    dolbeaultReplaceCoordinate j (0,w) = coordinateDirection j w := by
  ext k
  simp only [dolbeaultReplaceCoordinate_apply,coordinateDirection,Pi.zero_apply]

theorem dolbeaultCoordinateSlice_dbar {n : ℕ} (j : Fin n)
    (a : Configuration n → ℂ) (ha : ContDiff ℝ ∞ a)
    (p : Configuration n) (z : ℂ) :
    planarDbar (fun w => a (dolbeaultReplaceCoordinate j (p,w))) z =
      dbarComponent a j (dolbeaultReplaceCoordinate j (p,z)) := by
  have hh := (ha.differentiable (by simp)
    (dolbeaultReplaceCoordinate j (p,z))).hasFDerivAt.comp z
      ((dolbeaultReplaceCoordinate j).hasFDerivAt.comp z
        ((hasFDerivAt_const p z).prodMk (hasFDerivAt_id z)))
  have hh' : HasFDerivAt (fun w => a (dolbeaultReplaceCoordinate j (p,w)))
      (((fderiv ℝ a (dolbeaultReplaceCoordinate j (p,z))).comp
        (dolbeaultReplaceCoordinate j)).comp
          ((0 : ℂ →L[ℝ] Configuration n).prod (ContinuousLinearMap.id ℝ ℂ))) z := by
    simpa only [Function.comp_def,ContinuousLinearMap.comp_assoc] using! hh
  simp only [planarDbar,dbarComponent,hh'.fderiv,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.zero_apply,ContinuousLinearMap.id_apply,
    dolbeaultReplaceCoordinate_vertical,realCoordinateDirection,imaginaryCoordinateDirection]

/-- Exact derivative-free residual formula in arbitrary configuration
coordinates. This is the analytic identity behind the bounded L² iteration. -/
theorem configurationCauchyGreen_cutoff_residual {n : ℕ} (j k : Fin n)
    (hkj : k ≠ j) (χ : ℂ → ℂ) (a b : Configuration n → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (p : Configuration n)
    (hclosed : ∀ z ∈ tsupport χ,
      dbarComponent a k (dolbeaultReplaceCoordinate j (p,z)) =
        dbarComponent b j (dolbeaultReplaceCoordinate j (p,z))) :
    dbarComponent (configurationCauchyGreenPotential j χ a) k p =
      χ (p j) * b p - cauchyGreenPotential
        (fun z => planarDbar χ z * b (dolbeaultReplaceCoordinate j (p,z))) (p j) := by
  let A : Configuration n → ℂ → ℂ := fun q z => a (dolbeaultReplaceCoordinate j (q,z))
  let B : Configuration n → ℂ → ℂ := fun q z => b (dolbeaultReplaceCoordinate j (q,z))
  let F : Configuration n × ℂ → ℂ := localizedCauchyGreenPotential χ A
  have hA : ContDiff ℝ ∞ (Function.uncurry A) := by
    simpa only [A,Function.uncurry] using! ha.comp (dolbeaultReplaceCoordinate j).contDiff
  have hB : ContDiff ℝ ∞ (Function.uncurry B) := by
    simpa only [B,Function.uncurry] using! hb.comp (dolbeaultReplaceCoordinate j).contDiff
  have hF : ContDiff ℝ ∞ F := localizedCauchyGreenPotential_contDiff χ A hχ hc hA
  let D : Configuration n →L[ℝ] Configuration n × ℂ :=
    (ContinuousLinearMap.id ℝ _).prod (ContinuousLinearMap.proj j)
  have hh := (hF.differentiable (by simp) (p,p j)).hasFDerivAt.comp p D.hasFDerivAt
  have hh' : HasFDerivAt (configurationCauchyGreenPotential j χ a)
      ((fderiv ℝ F (p,p j)).comp D) p := by
    simpa only [configurationCauchyGreenPotential,F,A,D,Function.comp_def,
      ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.proj_apply] using! hh
  have hv (w : ℂ) : fderiv ℝ (configurationCauchyGreenPotential j χ a) p
      (coordinateDirection k w) = fderiv ℝ F (p,p j) (coordinateDirection k w,0) := by
    rw [hh'.fderiv]
    change fderiv ℝ F (p,p j) (D (coordinateDirection k w)) = _
    simp [D,coordinateDirection,Ne.symm hkj]
  have h := parametricCauchyGreen_cutoff_residual χ A B hχ hc hA hB
    (coordinateDirection k 1) (coordinateDirection k Complex.I) (p,p j) (fun z hz => by
      have hd := (ha.differentiable (by simp)
        (dolbeaultReplaceCoordinate j (p,z))).hasFDerivAt.comp (p,z)
          (dolbeaultReplaceCoordinate j).hasFDerivAt
      have hd' : HasFDerivAt (Function.uncurry A)
          ((fderiv ℝ a (dolbeaultReplaceCoordinate j (p,z))).comp
            (dolbeaultReplaceCoordinate j)) (p,z) := by
        simpa only [A,Function.uncurry,Function.comp_def] using! hd
      simp only [finiteComplexDbar,hd'.fderiv,ContinuousLinearMap.comp_apply,
        dolbeaultReplaceCoordinate_direction_other j k hkj]
      change dbarComponent a k (dolbeaultReplaceCoordinate j (p,z)) =
        planarDbar (B p) z
      rw [dolbeaultCoordinateSlice_dbar j b hb]
      exact hclosed z hz)
  simpa only [dbarComponent,realCoordinateDirection,imaginaryCoordinateDirection,hv,
    finiteComplexDbar,F,B,dolbeaultReplaceCoordinate_same] using! h

#print axioms dolbeaultReplaceCoordinate_vertical
#print axioms dolbeaultCoordinateSlice_dbar
#print axioms configurationCauchyGreen_cutoff_residual
end
end GinibrePoincare
