import Probes.ActualSecondaryPhysicalPieceData
import Probes.ActualSecondaryConstructedSum

/-!
# The actual global secondary physical error, with local multiplicity

Every summand is the literal metric variation of the SAME supported finite
secondary wave minus its actual transported forcing. Its regularity, inactive
zero germ and quantitative physical residual are all proved internally from
primitive piece data. The sum retains every nonzero ordered signed record
and every genuine secondary subordinate, with factor `4 L² R`.
-/

noncomputable section
open Manifold Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

def actualFastTensorChartTransferPrefix (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (j+1), actualFastTensorChartTransferCost T s

theorem actualFastTensorChartTransferCost_nonneg (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ) :
    0 ≤ actualFastTensorChartTransferCost T j := by
  have hp := actualFastChartTransferPrefix_nonneg T hT j
  unfold actualFastTensorChartTransferCost
  positivity

theorem actualFastTensorChartTransferPrefix_nonneg (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ) :
    0 ≤ actualFastTensorChartTransferPrefix T j :=
  Finset.sum_nonneg (fun s _ => actualFastTensorChartTransferCost_nonneg T hT s)

theorem actualFastTensorChartTransferCost_le_prefix (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i)
    {s j : ℕ} (hs : s ≤ j) :
    actualFastTensorChartTransferCost T s ≤ actualFastTensorChartTransferPrefix T j :=
  Finset.single_le_sum (fun k _ => actualFastTensorChartTransferCost_nonneg T hT k) (by simpa using hs)

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

private local instance globalSecondaryTensorSemi : SeminormedAddCommGroup Tensor :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance globalSecondaryTensorNormed : NormedAddCommGroup Tensor :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance globalSecondaryTensorSpace : NormedSpace ℝ Tensor :=
  ContinuousLinearMap.toNormedSpace

def actualConstructedSecondaryPhysicalFamily
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (kappa : X → Ep × M) (tau : ℝ) (length : ℕ)
    (r : (Label × Label) × Fin 4) (a : Sub) : X → Tensor :=
  if h : r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3 then
    actualObservedSecondaryPhysicalError F hF (data ⟨r,h⟩ a).base kappa tau length else 0

def actualConstructedSecondaryPhysicalSum
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (kappa : X → Ep × M) (tau : ℝ) (length : ℕ) : X → Tensor :=
  actualSecondaryRefinedNonzeroSum (actualConstructedSecondaryPhysicalFamily F hF data kappa tau length)

theorem actual_constructed_secondary_physical_sum_weighted_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (n j : ℕ) (ell Mg CH delta : ℝ) (W : Set (Ep × M))
    (data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) (hbudget : j+1+length ≤ n)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) (hW : IsOpen W)
    (K : Label → Set (Ep × M))
    (hprimary : ∀ r a, (data r a).base.support ⊆ K r.val.1.1 ∩ K r.val.1.2)
    (kappa : X → Ep × M) (Omega S : Set X) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (hfirst : ∀ z ∈ Omega, (kappa z).1 = z.1)
    (O : ActualSecondarySignedRecord Label → Sub → Set X)
    (hO : ∀ r a, IsOpen (O r a)) (hOOmega : ∀ r a, O r a ⊆ Omega)
    (hactiveO : ∀ r a, S ∩ kappa ⁻¹' (data r a).base.support ⊆ O r a)
    (hsource : ∀ r a, MapsTo kappa (O r a) (data r a).base.chart.source)
    (htransition : ∀ r a, ContDiffOn ℝ ∞ ((data r a).base.chart ∘ kappa) (O r a))
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i)
    (hsample : ∀ r a z, z ∈ S ∩ kappa ⁻¹' (data r a).base.support →
      (data r a).base.chart (kappa z) ∈ (data r a).base.sample)
    (htransitionb : ∀ r a z, z ∈ S ∩ kappa ⁻¹' (data r a).base.support →
      ∀ i, 1 ≤ i → i ≤ j+1 →
        ell ^ (i-1) * ‖iteratedFDeriv ℝ i ((data r a).base.chart ∘ kappa) z‖ ≤ T i)
    (L R : ℕ)
    (hL : ∀ z ∈ S, (Finset.univ.filter (fun nu => kappa z ∈ K nu)).card ≤ L)
    (hR : ∀ r : ActualSecondarySignedRecord Label, ∀ z ∈ S,
      (Finset.univ.filter (fun a => kappa z ∈ (data r a).base.support)).card ≤ R) :
    (∀ z ∈ S, ContDiffAt ℝ ∞ (actualConstructedSecondaryPhysicalSum F hF data kappa tau length) z) ∧
    ∀ s ≤ j, ∀ z ∈ S, tau ^ s * ‖iteratedFDeriv ℝ s
      (actualConstructedSecondaryPhysicalSum F hF data kappa tau length) z‖ ≤
      ((4 * L ^ 2 * R : ℕ) : ℝ) * actualFastTensorChartTransferPrefix T j *
        actualSecondaryPhysicalCost m N n length j Mg CH * (tau / ell) ^ length * delta ^ 2 := by
  let pred : ((Label × Label) × Fin 4) → Prop := fun r =>
    r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3
  let pieces := actualConstructedSecondaryPhysicalFamily F hF data kappa tau length
  let f : (((Label × Label) × Fin 4) × Sub) → X → Tensor := fun t => pieces t.1 t.2
  let Ksub : ((Label × Label) × Fin 4) → Sub → Set (Ep × M) := fun r a =>
    if h : pred r then (data ⟨r,h⟩ a).base.support else ∅
  let Budget := actualFastTensorChartTransferPrefix T j * actualSecondaryPhysicalCost m N n length j Mg CH *
    (tau / ell) ^ length * delta ^ 2
  have hC := actualSecondaryPhysicalCost_nonneg m N n length j Mg CH hMg hCH
  have hBudget : 0 ≤ Budget := by
    have hp := actualFastTensorChartTransferPrefix_nonneg T hT j
    dsimp only [Budget]
    positivity
  have hsub : ∀ r a, Ksub r a ⊆ K r.1.1 ∩ K r.1.2 := by
    intro r a
    by_cases hq : pred r
    · simpa only [Ksub, dif_pos hq] using hprimary ⟨r,hq⟩ a
    · simp only [Ksub, dif_neg hq, empty_subset]
  have he : actualConstructedSecondaryPhysicalSum F hF data kappa tau length = fun z => ∑ t, f t z := by
    funext z
    simp only [actualConstructedSecondaryPhysicalSum, actualSecondaryRefinedNonzeroSum,
      actualSecondaryNonzeroSum, Fintype.sum_prod_type, Finset.sum_filter,
      f, pieces, actualConstructedSecondaryPhysicalFamily]
    apply Finset.sum_congr rfl
    intro nu _
    apply Finset.sum_congr rfl
    intro mu _
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : nu ≠ mu ∨ q = 0 ∨ q = 3 <;> simp [hq]
  have hall (z : X) (hz : z ∈ S) :
      ContDiffAt ℝ ∞ (actualConstructedSecondaryPhysicalSum F hF data kappa tau length) z ∧
      ∀ s ≤ j, tau ^ s * ‖iteratedFDeriv ℝ s
        (actualConstructedSecondaryPhysicalSum F hF data kappa tau length) z‖ ≤
        ((4 * L ^ 2 * R : ℕ) : ℝ) * Budget := by
    let active := Finset.univ.filter (fun t : (((Label × Label) × Fin 4) × Sub) =>
      pred t.1 ∧ kappa z ∈ Ksub t.1 t.2)
    have hactive : active.card ≤ 4 * L ^ 2 * R :=
      actual_secondary_refined_active_card_le K Ksub hsub (kappa z) L R (hL z hz)
        (fun r hq => by
          have hp : pred r := hq
          simpa only [Ksub, dif_pos hp] using hR ⟨r,hq⟩ z hz)
    have hlocal (t : (((Label × Label) × Fin 4) × Sub)) (ht : t ∈ active) :
        ContDiffAt ℝ ∞ (f t) z ∧
        ∀ s ≤ j, tau ^ s * ‖iteratedFDeriv ℝ s (f t) z‖ ≤ Budget := by
      obtain ⟨hq, hKs⟩ := (Finset.mem_filter.mp ht).2
      have hq' : t.1.1.1 ≠ t.1.1.2 ∨ t.1.2 = 0 ∨ t.1.2 = 3 := hq
      have hzs : z ∈ S ∩ kappa ⁻¹' (data ⟨t.1,hq⟩ t.2).base.support := by
        refine ⟨hz, ?_⟩
        change kappa z ∈ (data ⟨t.1,hq⟩ t.2).base.support
        simpa only [Ksub, dif_pos hq] using hKs
      obtain ⟨hr, hb⟩ := actual_secondary_physical_piece_observation_jets F hF n j ell Mg CH delta W
        (data ⟨t.1,hq⟩ t.2) kappa (O ⟨t.1,hq⟩ t.2) (hO ⟨t.1,hq⟩ t.2)
        (hsource ⟨t.1,hq⟩ t.2) (fun y hy => hfirst y (hOOmega _ _ hy))
        (htransition ⟨t.1,hq⟩ t.2) tau length hbudget hell hell1 htau htaul hMg hCH T hT z
        (hactiveO _ _ hzs) (hsample _ _ z hzs) (htransitionb _ _ z hzs)
      refine ⟨?_, ?_⟩
      · simpa only [f, pieces, actualConstructedSecondaryPhysicalFamily, dif_pos hq'] using
          hr.contDiffAt ((hO _ _).mem_nhds (hactiveO _ _ hzs))
      · intro s hs
        have hprefix := actualFastTensorChartTransferCost_le_prefix T hT hs
        have hle : actualFastTensorChartTransferCost T s * actualSecondaryPhysicalCost m N n length j Mg CH *
            (tau / ell) ^ length * delta ^ 2 ≤ Budget := by
          dsimp only [Budget]
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg delta)
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (div_nonneg htau.le hell.le) length)
          exact mul_le_mul_of_nonneg_right hprefix hC
        have hb' := (hb s hs).trans hle
        simpa only [f, pieces, actualConstructedSecondaryPhysicalFamily, dif_pos hq'] using hb'
    have hzero : ∀ t ∉ active, f t =ᶠ[𝓝 z] fun _ => 0 := by
      intro t ht
      by_cases hq : pred t.1
      · have hnot : kappa z ∉ (data ⟨t.1,hq⟩ t.2).base.support := by
          intro hmem
          apply ht
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, hq, ?_⟩
          simpa only [Ksub, dif_pos hq] using hmem
        have hg := actual_observed_secondary_error_zero_germ F hF n j ell Mg CH delta W
          (data ⟨t.1,hq⟩ t.2).base kappa tau length hW z
          (hkappa.continuousAt (hOmega.mem_nhds (hSOmega hz))) (hmap (hSOmega hz)) hnot
        have hq' : t.1.1.1 ≠ t.1.1.2 ∨ t.1.2 = 0 ∨ t.1.2 = 3 := hq
        simpa only [f, pieces, actualConstructedSecondaryPhysicalFamily, dif_pos hq'] using hg
      · have hq' : ¬ (t.1.1.1 ≠ t.1.1.2 ∨ t.1.2 = 0 ∨ t.1.2 = 3) := hq
        exact Filter.Eventually.of_forall (fun _ => by
          simp only [f, pieces, actualConstructedSecondaryPhysicalFamily, dif_neg hq', Pi.zero_apply])
    have hreg (t) : ContDiffAt ℝ ∞ (f t) z := by
      by_cases ht : t ∈ active
      · exact (hlocal t ht).1
      · exact contDiffAt_const.congr_of_eventuallyEq (hzero t ht)
    rw [he]
    refine ⟨ContDiffAt.sum (fun t _ => hreg t), ?_⟩
    intro s hs
    have hb : ∀ t ∈ active, ‖iteratedFDeriv ℝ s (f t) z‖ ≤ Budget / tau ^ s := by
      intro t ht
      exact (le_div_iff₀ (pow_pos htau s)).2
        (by simpa only [mul_comm] using (hlocal t ht).2 s hs)
    have hh := parameter_finite_sum_jet_le f z active (4 * L ^ 2 * R) s
      (Budget / tau ^ s) hactive (by positivity) (fun t ht => (hlocal t ht).1) hzero hb
    calc
      _ ≤ tau ^ s * (((4 * L ^ 2 * R : ℕ) : ℝ) * (Budget / tau ^ s)) :=
        mul_le_mul_of_nonneg_left hh (pow_nonneg htau.le _)
      _ = _ := by field_simp [(pow_pos htau s).ne']
  refine ⟨fun z hz => (hall z hz).1, ?_⟩
  intro s hs z hz
  simpa only [Budget, mul_assoc] using (hall z hz).2 s hs

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_constructed_secondary_physical_sum_weighted_jets
