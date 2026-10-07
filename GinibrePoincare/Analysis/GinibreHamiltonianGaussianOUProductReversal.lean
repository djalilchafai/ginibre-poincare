module

public import GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUContinuousReversal
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem independent_coordinate_pairs_of_independent_families
    {Ω ι A B : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → A) (Y : ι → Ω → B)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hiX : iIndepFun X P) (hiY : iIndepFun Y P)
    (hind : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P) :
    iIndepFun (fun i ω => (X i ω,Y i ω)) P := by
  have hmX : Measurable (fun ω i => X i ω) := Measurable.of_eval hX
  have hmY : Measurable (fun ω i => Y i ω) := Measurable.of_eval hY
  have hpair (i : ι) : P.map (fun ω => (X i ω,Y i ω)) = (P.map (X i)).prod (P.map (Y i)) :=
    (hind.comp (measurable_pi_apply i) (measurable_pi_apply i)).map_prod_eq_prod_map_map
      (hX i).aemeasurable (hY i).aemeasurable
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => ((hX i).prodMk (hY i)).aemeasurable)).mpr
  let e := MeasurableEquiv.arrowProdEquivProdArrow A B ι
  apply e.measurableEmbedding.map_injective
  rw [Measure.map_map e.measurable (Measurable.of_eval (fun i => (hX i).prodMk (hY i)))]
  change P.map (fun ω => ((fun i => X i ω),(fun i => Y i ω))) = _
  rw [hind.map_prod_eq_prod_map_map hmX.aemeasurable hmY.aemeasurable,
    hiX.map_fun_eq_pi_map (fun i => (hX i).aemeasurable),
    hiY.map_fun_eq_pi_map (fun i => (hY i).aemeasurable)]
  simp_rw [hpair]
  haveI (i : ι) : IsProbabilityMeasure (P.map (X i)) := (by infer_instance)
  haveI (i : ι) : IsProbabilityMeasure (P.map (Y i)) := (by infer_instance)
  exact (measurePreserving_arrowProdEquivProdArrow A B ι (fun i => P.map (X i)) (fun i => P.map (Y i))).map_eq.symm

end
end GinibrePoincare
