import Probes.ActualSecondaryGlobalPhysicalSum
import Probes.ActualSecondaryForcingPartition

/-!
# Linearized cancellation for the same constructed global U2

The actual global finite sum is differentiated here. Differentiability of
each summand follows from its genuine supported construction and the actual
smooth observer. The resulting error is exactly the physical sum already
estimated, minus the actual total transported forcing. No differentiability
or budget of a chosen output displacement is supplied as a premise.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Manifold Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem actual_coordinate_metric_linearization_sum
    {A D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (s : Finset A) (F : D → V) (U : A → D → V) (x : D)
    (hU : ∀ a ∈ s, DifferentiableAt ℝ (U a) x) :
    actualCoordinateMetricLinearization F (fun y => ∑ a ∈ s, U a y) x =
      ∑ a ∈ s, actualCoordinateMetricLinearization F (U a) x := by
  ext v w
  simp only [actualCoordinateMetricLinearization_apply, fderiv_fun_sum hU,
    ContinuousLinearMap.sum_apply, inner_sum, sum_inner, Finset.sum_add_distrib]

theorem actual_secondary_refined_sum_eq_records
    {Label Sub X Y : Type*} [Fintype Label] [DecidableEq Label] [Fintype Sub]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (waves : ((Label × Label) × Fin 4) → Sub → X → Y) :
    actualSecondaryRefinedNonzeroSum waves = fun z =>
      ∑ r ∈ actualSecondaryNonzeroRecords Label, ∑ a, waves r a z := by
  funext z
  simp only [actualSecondaryRefinedNonzeroSum, actualSecondaryNonzeroSum,
    actualSecondaryNonzeroRecords, Finset.sum_filter, Fintype.sum_prod_type]

variable {m N : ℕ} {Ep M Label Sub : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

def actualConstructedSecondaryForcingFamily
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (kappa : X → Ep × M) (tau : ℝ)
    (r : (Label × Label) × Fin 4) (a : Sub) : X → Tensor :=
  if h : r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3 then
    actualObservedSecondaryForcingTensor F hF (data ⟨r,h⟩ a).base kappa tau else 0

def actualConstructedSecondaryForcingSum
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (kappa : X → Ep × M) (tau : ℝ) : X → Tensor :=
  actualSecondaryRefinedNonzeroSum (actualConstructedSecondaryForcingFamily F hF data kappa tau)

theorem actual_constructed_secondary_linearized_cancellation
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M))
    (data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) (hW : IsOpen W)
    (kappa : X → Ep × M) (Omega : Set X) (hOmega : IsOpen Omega)
    (hkappa : ContMDiffOn 𝓘(ℝ, X) ((𝓘(ℝ, Ep)).prod 𝓙) ∞ kappa Omega)
    (hmap : MapsTo kappa Omega W) (z : X) (hz : z ∈ Omega) :
    actualJointMetricLinearization (fun y => F (kappa y).1 (kappa y).2)
      (actualConstructedSecondarySum F hF (fun r a => (data r a).base) tau length ∘ kappa) z -
      actualConstructedSecondaryForcingSum F hF data kappa tau z =
        actualConstructedSecondaryPhysicalSum F hF data kappa tau length z := by
  let waves := actualConstructedSecondaryFamily F hF (fun r a => (data r a).base) tau length
  let observed : ((Label × Label) × Fin 4) → Sub → X → V := fun r a => waves r a ∘ kappa
  have hdiff : ∀ r ∈ actualSecondaryNonzeroRecords Label, ∀ a,
      DifferentiableAt ℝ (fun x => observed r a (z.1,x)) z.2 := by
    intro r hr a
    have hq := (Finset.mem_filter.mp hr).2
    let d := (data ⟨r,hq⟩ a).base
    have hm := ((d.wave_regular tau length hW).1.comp hkappa hmap).contDiffOn
    have hs := actual_joint_contDiffOn_slice (d.wave tau length ∘ kappa) Omega hm z.1
    have hd := (hs.contDiffAt
      ((hOmega.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)).differentiableAt (by simp)
    simpa only [observed, waves, actualConstructedSecondaryFamily, dif_pos hq, Function.comp_def] using hd
  have houter : ∀ r ∈ actualSecondaryNonzeroRecords Label,
      DifferentiableAt ℝ (fun x => ∑ a, observed r a (z.1,x)) z.2 := by
    intro r hr
    exact DifferentiableAt.fun_sum (fun a _ => hdiff r hr a)
  have hsum := actual_coordinate_metric_linearization_sum (actualSecondaryNonzeroRecords Label)
    (fun x => F (kappa (z.1,x)).1 (kappa (z.1,x)).2)
    (fun r x => ∑ a, observed r a (z.1,x)) z.2 houter
  have hin : ∀ r ∈ actualSecondaryNonzeroRecords Label,
      actualCoordinateMetricLinearization (fun x => F (kappa (z.1,x)).1 (kappa (z.1,x)).2)
        (fun x => ∑ a, observed r a (z.1,x)) z.2 =
      ∑ a, actualCoordinateMetricLinearization (fun x => F (kappa (z.1,x)).1 (kappa (z.1,x)).2)
        (fun x => observed r a (z.1,x)) z.2 := by
    intro r hr
    exact actual_coordinate_metric_linearization_sum Finset.univ _ _ z.2 (fun a _ => hdiff r hr a)
  have hUeq : actualConstructedSecondarySum F hF (fun r a => (data r a).base) tau length ∘ kappa =
      actualSecondaryRefinedNonzeroSum observed := rfl
  rw [hUeq]
  unfold actualJointMetricLinearization
  rw [actual_secondary_refined_sum_eq_records, hsum]
  unfold actualConstructedSecondaryForcingSum actualConstructedSecondaryPhysicalSum
  rw [actual_secondary_refined_sum_eq_records, actual_secondary_refined_sum_eq_records]
  dsimp only
  ext v w
  simp only [ContinuousLinearMap.sub_apply, sum_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hin r hr]
  simp only [sum_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hq := (Finset.mem_filter.mp hr).2
  simp only [observed, waves, actualConstructedSecondaryFamily, actualConstructedSecondaryForcingFamily,
    actualConstructedSecondaryPhysicalFamily, dif_pos hq, Function.comp_def,
    actualObservedSecondaryPhysicalError, sub_apply]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_coordinate_metric_linearization_sum
#print axioms GlobalEmbedding.Continuation.actual_constructed_secondary_linearized_cancellation
