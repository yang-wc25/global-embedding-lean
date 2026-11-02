import Probes.ActualSecondaryConstructedPiece
import Probes.ActualIncrementSecondaryRelativeSum
import Probes.ActualJointTensorChartTransfer

/-!
# The same constructed global secondary displacement

Only genuinely nonzero signed ordered records receive adapted chart data.
Each record is further summed over its actual secondary subordinates. All
local wave bounds below are derived from primitive forcing and geometry;
none is supplied as a premise. The constant retains the primary interaction
count and the secondary subordinate count, and includes neither total count.
-/

noncomputable section
open Manifold Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

def ActualSecondarySignedRecord (Label : Type*) :=
  {r : (Label × Label) × Fin 4 // r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3}

variable {E H M Ep Y Label Sub : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [Fintype Label] [DecidableEq Label] [Fintype Sub]
  {m N n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def actualConstructedSecondaryFamily
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPieceData (m := m) F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) (r : (Label × Label) × Fin 4) (a : Sub) : Ep × M → V :=
  if h : r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3 then (data ⟨r, h⟩ a).wave tau length else 0

def actualConstructedSecondarySum
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPieceData (m := m) F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) : Ep × M → V :=
  actualSecondaryRefinedNonzeroSum (actualConstructedSecondaryFamily F hF data tau length)

theorem actual_constructed_secondary_sum_weighted_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (data : ActualSecondarySignedRecord Label → Sub →
      ActualSecondaryPieceData (m := m) F hF n j ell Mg CH delta W)
    (tau : ℝ) (length : ℕ) (hbudget : j + 1 + length ≤ n)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hMg : 0 ≤ Mg) (hCH : 0 ≤ CH) (hW : IsOpen W)
    (K : Label → Set (Ep × M))
    (hprimary : ∀ r a, (data r a).support ⊆ K r.val.1.1 ∩ K r.val.1.2)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (O : ActualSecondarySignedRecord Label → Sub → Set Y)
    (hO : ∀ r a, IsOpen (O r a))
    (hactiveO : ∀ r a, S ∩ kappa ⁻¹' (data r a).support ⊆ O r a)
    (hsource : ∀ r a, MapsTo kappa (O r a) (data r a).chart.source)
    (htransition : ∀ r a, ContDiffOn ℝ ∞ ((data r a).chart ∘ kappa) (O r a))
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i)
    (hsample : ∀ r a y, y ∈ S ∩ kappa ⁻¹' (data r a).support →
      (data r a).chart (kappa y) ∈ (data r a).sample)
    (htransitionb : ∀ r a y, y ∈ S ∩ kappa ⁻¹' (data r a).support →
      ∀ i, 1 ≤ i → i ≤ j →
        ell ^ (i - 1) * ‖iteratedFDeriv ℝ i ((data r a).chart ∘ kappa) y‖ ≤ T i)
    (L R : ℕ)
    (hL : ∀ y ∈ S, (Finset.univ.filter (fun nu => kappa y ∈ K nu)).card ≤ L)
    (hR : ∀ r : ActualSecondarySignedRecord Label, ∀ y ∈ S,
      (Finset.univ.filter (fun a => kappa y ∈ (data r a).support)).card ≤ R) :
    (∀ y ∈ S, ContDiffAt ℝ ∞ (actualConstructedSecondarySum F hF data tau length ∘ kappa) y) ∧
    ∀ s ≤ j, ∀ y ∈ S, tau ^ s * ‖iteratedFDeriv ℝ s
      (actualConstructedSecondarySum F hF data tau length ∘ kappa) y‖ ≤
      ((4 * L ^ 2 * R : ℕ) : ℝ) * actualFastChartTransferPrefix T j *
        actualSecondaryForcedWaveCost m N n length j Mg CH * delta ^ 2 := by
  let pred : ((Label × Label) × Fin 4) → Prop := fun r =>
    r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3
  let waves := actualConstructedSecondaryFamily F hF data tau length
  let Ksub : ((Label × Label) × Fin 4) → Sub → Set (Ep × M) := fun r a =>
    if h : pred r then (data ⟨r, h⟩ a).support else ∅
  let OO : ((Label × Label) × Fin 4) → Sub → Set Y := fun r a =>
    if h : pred r then O ⟨r, h⟩ a else ∅
  let Cw := actualSecondaryForcedWaveCost m N n length j Mg CH
  let Budget := actualFastChartTransferPrefix T j * Cw * delta ^ 2
  have hCw : 0 ≤ Cw := actualSecondaryForcedWaveCost_nonneg m N n length j Mg CH hMg hCH
  have hBudget : 0 ≤ Budget := mul_nonneg
    (mul_nonneg (actualFastChartTransferPrefix_nonneg T hT j) hCw) (sq_nonneg delta)
  have hsub : ∀ r a, Ksub r a ⊆ K r.1.1 ∩ K r.1.2 := by
    intro r a
    by_cases hq : pred r
    · simpa only [Ksub, dif_pos hq] using hprimary ⟨r, hq⟩ a
    · simp only [Ksub, dif_neg hq, empty_subset]
  have hsupp : ∀ r, pred r → ∀ a,
      tsupport (fun y : W => waves r a y) ⊆ Subtype.val ⁻¹' Ksub r a := by
    intro r hq a
    have hq' : r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3 := hq
    simpa only [waves, actualConstructedSecondaryFamily, Ksub, pred, dif_pos hq'] using
      ((data ⟨r, hq⟩ a).wave_regular tau length hW).2
  have hOO : ∀ r a, IsOpen (OO r a) := by
    intro r a
    by_cases hq : pred r
    · simpa only [OO, dif_pos hq] using hO ⟨r, hq⟩ a
    · simp only [OO, dif_neg hq, isOpen_empty]
  have hSO : ∀ r, pred r → ∀ a, S ∩ kappa ⁻¹' Ksub r a ⊆ OO r a := by
    intro r hq a
    simpa only [Ksub, OO, dif_pos hq] using hactiveO ⟨r, hq⟩ a
  have hreg : ∀ r, pred r → ∀ a, ContDiffOn ℝ ∞ (waves r a ∘ kappa) (OO r a) := by
    intro r hq a
    let d := data ⟨r, hq⟩ a
    have hl := (d.local_wave_jets tau length hbudget hell hell1 htau htaul hMg hCH).1
    have hh := actual_secondary_supported_observation_contDiffOn F hF d.c d.hR d.hI d.chart d.phase
      (fun z : X => z.2 0) tau length kappa (O ⟨r, hq⟩ a) (hsource ⟨r, hq⟩ a)
      (fun y hy => d.adaptation (kappa y) (hsource ⟨r, hq⟩ a hy)) (htransition ⟨r, hq⟩ a) hl
    have hq' : r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3 := hq
    simpa only [waves, actualConstructedSecondaryFamily, OO, pred, dif_pos hq',
      ActualSecondaryPieceData.wave] using hh
  have hcount : ∀ r, pred r → ∀ y ∈ S,
      (Finset.univ.filter (fun a => kappa y ∈ Ksub r a)).card ≤ R := by
    intro r hq y hy
    simpa only [Ksub, dif_pos hq] using hR ⟨r, hq⟩ y hy
  have hjets (s : ℕ) (hs : s ≤ j) : ∀ r, pred r → ∀ a,
      ∀ y ∈ S ∩ kappa ⁻¹' Ksub r a,
        tau ^ s * ‖iteratedFDeriv ℝ s (waves r a ∘ kappa) y‖ ≤ Budget := by
    intro r hq a y hy
    have hy' : y ∈ S ∩ kappa ⁻¹' (data ⟨r, hq⟩ a).support := by
      simpa only [Ksub, dif_pos hq] using hy
    let d := data ⟨r, hq⟩ a
    obtain ⟨hl, hb⟩ := d.local_wave_jets tau length hbudget hell hell1 htau htaul hMg hCH
    have hh := actual_secondary_supported_observation_weighted_jets F hF d.c d.hR d.hI d.chart
      d.phase (fun z : X => z.2 0) tau ell length kappa (O ⟨r, hq⟩ a) (hO ⟨r, hq⟩ a)
      (hsource ⟨r, hq⟩ a) (fun y hy => d.adaptation (kappa y) (hsource ⟨r, hq⟩ a hy))
      (htransition ⟨r, hq⟩ a) hl T hT s (Cw * delta ^ 2) htau htaul y
      (hactiveO ⟨r, hq⟩ a hy')
      (fun i hi => hb i (hi.trans hs) _ (hsample ⟨r, hq⟩ a y hy'))
      (fun i hi his => htransitionb ⟨r, hq⟩ a y hy' i hi (his.trans hs))
    have hle := mul_le_mul_of_nonneg_right (actualFastChartTransferCost_le_prefix T hT hs)
      (mul_nonneg hCw (sq_nonneg delta))
    have hx := hh.trans hle
    have hq' : r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3 := hq
    simpa only [waves, actualConstructedSecondaryFamily, dif_pos hq',
      ActualSecondaryPieceData.wave, Budget, mul_assoc] using hx
  have hsum (s : ℕ) (hs : s ≤ j) :=
    actual_secondary_relative_refined_observation_sum_weighted_jets waves K Ksub hsub W hW hsupp
      kappa Omega S hOmega hSOmega hkappa hmap OO hOO hSO hreg L R s hL hcount tau Budget
      htau hBudget (hjets s hs)
  have he : actualSecondaryRefinedNonzeroSum (fun r a => waves r a ∘ kappa) =
      actualConstructedSecondarySum F hF data tau length ∘ kappa := rfl
  refine ⟨?_, ?_⟩
  · intro y hy
    simpa only [he] using (hsum 0 (Nat.zero_le _) y hy).1
  · intro s hs y hy
    have hh := (hsum s hs y hy).2
    simpa only [he, Budget, Cw, mul_assoc] using hh

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_constructed_secondary_sum_weighted_jets
