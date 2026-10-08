module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultLpIteration

@[expose] public section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem dbarComponent_compact_support {n : ℕ} (θ : Configuration n → ℂ)
    (hc : HasCompactSupport θ) (j : Fin n) :
    HasCompactSupport (fun p => dbarComponent θ j p) := by
  exact ((hc.fderiv_apply ℝ (realCoordinateDirection j)).add
    ((hc.fderiv_apply ℝ (imaginaryCoordinateDirection j)).mul_left
      (f := fun _ => Complex.I))).mul_left (f := fun _ => (1/2 : ℂ))

/-- Ordinary strong L² limits preserve the literal local distributional
solution identities against every ordinary compact smooth test. -/
theorem dolbeault_weak_identity_of_strong_limit {n : ℕ} {ι : Type*}
    {f : Filter ι} [f.NeBot] (u a : ι → dolbeaultOrdinaryL2 n)
    (U A : dolbeaultOrdinaryL2 n) (hu : Tendsto u f (𝓝 U)) (ha : Tendsto a f (𝓝 A))
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (j : Fin n)
    (he : ∀ i, (∫ p, θ p*a i p) = -∫ p, dbarComponent θ j p*u i p) :
    (∫ p, θ p*A p) = -∫ p, dbarComponent θ j p*U p := by
  have hd := (smooth_dbarComponent_contDiff θ hθ j).continuous
  have hdc := dbarComponent_compact_support θ hc j
  have ha' := ((dolbeaultCompactPairing θ hθ.continuous hc).continuous.tendsto _).comp ha
  have hu' := ((dolbeaultCompactPairing (fun p => dbarComponent θ j p) hd hdc).continuous.tendsto _).comp hu
  simp only [Function.comp_def,dolbeaultCompactPairing_eq_integral] at ha' hu'
  have heq : (fun i => ∫ p, θ p*a i p) =
      (fun i => -∫ p, dbarComponent θ j p*u i p) := funext he
  rw [heq] at ha'
  exact tendsto_nhds_unique ha' hu'.neg

theorem dolbeault_weak_identity_of_eventual_strong_limit {n : ℕ} {ι : Type*}
    {f : Filter ι} [f.NeBot] (u a : ι → dolbeaultOrdinaryL2 n)
    (U A : dolbeaultOrdinaryL2 n) (hu : Tendsto u f (𝓝 U)) (ha : Tendsto a f (𝓝 A))
    (θ : Configuration n → ℂ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (j : Fin n)
    (he : ∀ᶠ i in f, (∫ p, θ p*a i p) = -∫ p, dbarComponent θ j p*u i p) :
    (∫ p, θ p*A p) = -∫ p, dbarComponent θ j p*U p := by
  have hd := (smooth_dbarComponent_contDiff θ hθ j).continuous
  have hdc := dbarComponent_compact_support θ hc j
  have ha' := ((dolbeaultCompactPairing θ hθ.continuous hc).continuous.tendsto _).comp ha
  have hu' := ((dolbeaultCompactPairing (fun p => dbarComponent θ j p) hd hdc).continuous.tendsto _).comp hu
  simp only [Function.comp_def,dolbeaultCompactPairing_eq_integral] at ha' hu'
  have he' : (fun i => ∫ p, θ p*a i p) =ᶠ[f]
      (fun i => -∫ p, dbarComponent θ j p*u i p) := he
  exact tendsto_nhds_unique ha' (hu'.neg.congr' he'.symm)

#print axioms dbarComponent_compact_support
#print axioms dolbeault_weak_identity_of_strong_limit
#print axioms dolbeault_weak_identity_of_eventual_strong_limit
end
end GinibrePoincare
