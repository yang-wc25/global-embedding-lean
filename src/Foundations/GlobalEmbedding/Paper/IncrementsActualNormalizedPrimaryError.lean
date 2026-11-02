import GlobalEmbedding.Paper.IncrementsPrimaryReconstructedChannels
import GlobalEmbedding.Paper.IncrementsFullNormalizedPrimaryError
import GlobalEmbedding.Paper.IncrementsMeanRemainderNorms

/-!
# Actual normalized primary error from original data

Source: original main.tex617–661. Corrections are actual R of the real/imaginary
channels of SAME finite U. Neither a solver nor a bound on R/P/Q/E is an input.
Actual geometry/source jets remain original internal producer obligations. This
local adapted-chart consumer does not replace the full global increments target.
-/

noncomputable section
open Manifold Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ

/-- Literal full normalized coefficient of the actual finite primary construction.
The actual source family contains its subordinate cutoffs; none is moved outside R.
Source: original main.tex638–661. -/
def incrementsActualNormalizedPrimaryError {A : Type*} [Fintype A]
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (chart : D → M)
    (L : D → T →L[ℝ] ℝ) (input : D → T) (cutoff phi : D → ℝ) (normal : D → V)
    (k : A → D → Cdata) (tau : ℝ) (p : ℕ) (v : D) (coord : Fin N) (x : D) : ℂ :=
  incrementsPrimaryErrorCoefficient 1 tau
    (fun y ↦ cutoff y * Real.sqrt (L y (input y))) phi normal
    (fun a ↦ incrementsPrimaryReconstructedChannel F hF chart
      incrementsModeRealPart tau p (k a))
    (fun a ↦ incrementsPrimaryReconstructedChannel F hF chart
      incrementsModeImagPart tau p (k a)) x v coord

/-- ROOT stage2 interface, source main.tex638–661. Choose the EXISTING witness
Cv at order j+1 from the accepted free-amplitude theorem. Cr, finite profile,
TP/TQ, phase/evaluation CLM norms and Cf use only j,p,c,Bnd,K and the fixed native
m,N,v,coord. Replace only CZ's card A by the numerical Bsub BEFORE quantifying
A,F,hF,chart. Introduce those fields, then run the SAME existing actual-input E
proof body once, including all native reserve/geometry/source consumers. Its
canonical E estimate has CZ_A; card A<=Bsub and nonnegative coefficients imply
CZ_A<=CZ_cap, hence BOTH sizes and SAMEdifference have the uniform C. No new
threshold or norm, no desired E bound as input. The old published theorem will
keep its HEADER/DOC exactly and specialize this provider with Bsub=card A.
Expected one named sorry in this stage2 draft only; ROOT must lock the ABI first. -/
theorem increments_actual_normalized_primary_error_bounds_uniform
    (j p : ℕ) (v : D) (coord : Fin N) (c Bnd K : ℝ) (Bsub : ℕ)
    (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {A : Type*} [Fintype A] (_hCard : Fintype.card A ≤ Bsub)
        (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (chart : D → M),
      ∀ {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
        (O S : Set D) (_hO : IsOpen O) (_hSO : S ⊆ O)
        (L : D → T →L[ℝ] ℝ) (input inputbar : D → T)
        (cutoff phi : D → ℝ) (normal : D → V)
        (_hL : ContDiffOn ℝ ∞ L O) (_hInput : ContDiffOn ℝ ∞ input O)
        (_hInputbar : ContDiffOn ℝ ∞ inputbar O) (_hCut : ContDiffOn ℝ ∞ cutoff O)
        (_hPhi : ContDiffOn ℝ ∞ phi O) (_hNormal : ContDiffOn ℝ ∞ normal O)
        (_hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF chart) O)
        (_hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF chart) O)
        (_hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ chart) y)) O)
        (_hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (chart y)).subtypeL.comp
          (incrementsModeCoordinateJ F hF chart y)) O)
        (_hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F chart) O)
        (k kbar : A → D → Cdata) (_hk : ∀ a, ContDiffOn ℝ ∞ (k a) O)
        (_hkbar : ∀ a, ContDiffOn ℝ ∞ (kbar a) O)
        (ell tau Delta : ℝ) (_hell : 0 < ell) (_hell1 : ell ≤ 1)
        (_htau : 0 < tau) (_htauell : tau ≤ ell) (_hDelta : 0 ≤ Delta)
        (_hReserve : ∀ x ∈ S, c ≤ L x (input x) ∧ c ≤ L x (inputbar x))
        (_hLb : ∀ i ≤ j + p + 2, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i L x‖ ≤ Bnd)
        (_hInputb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i input x‖ ≤ Bnd)
        (_hInputbarb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i inputbar x‖ ≤ Bnd)
        (_hCutb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i cutoff x‖ ≤ Bnd)
        (_hNormalb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i normal x‖ ≤ Bnd)
        (_hInputd : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ input y - inputbar y) x‖ ≤ Delta)
        (_hAb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderA F hF chart) x‖ ≤ Bnd)
        (_hBb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderB F hF chart) x‖ ≤ Bnd)
        (_hGb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
          ‖iteratedFDeriv ℝ i (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ chart) y)) x‖ ≤ Bnd)
        (_hJb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
          ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (chart y)).subtypeL.comp
            (incrementsModeCoordinateJ F hF chart y)) x‖ ≤ Bnd)
        (_hT0b : ∀ i ≤ j + 1, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F chart) x‖ ≤ Bnd)
        (_hkb : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (k a) x‖ ≤ K * tau)
        (_hkbarb : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (kbar a) x‖ ≤ K * tau)
        (_hkd : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ k a y - kbar a y) x‖ ≤ K * tau * Delta)
        (_hPhib : ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ fderiv ℝ phi y v) x‖ ≤ Bnd),
      let err := incrementsActualNormalizedPrimaryError F hF chart L input cutoff phi normal
        k tau p v coord
      let errbar := incrementsActualNormalizedPrimaryError F hF chart L inputbar cutoff phi normal
        kbar tau p v coord
      (∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i err x‖ ≤ C * (tau / ell)) ∧
      (∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i errbar x‖ ≤ C * (tau / ell)) ∧
      (∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
        (fun y ↦ err y - errbar y) x‖ ≤ C * (tau / ell) * Delta) := by
  obtain ⟨Cv, hCv, hFree⟩ := increments_primary_free_amplitude_scaled_bounds (j + 1) c Bnd hc hBnd
  let Cr := 2 ^ (j + 1) * Bnd + 2 * 2 ^ ((j + 1) + (j + 1)) * Bnd *
    max Bnd ‖incrementsModeTransverseJet (m := m)‖
  let profile := ∑ a ∈ Finset.range p, (2 * 2 ^ (j + p + 2) * Bnd) ^ a
  let TP := Cr * ‖incrementsModeRealPart (m := m)‖ * K * profile
  let TQ := Cr * ‖incrementsModeImagPart (m := m)‖ * K * profile
  let H : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight
    (Complex.I • ContinuousLinearMap.id ℝ ℂ)
  let CZ := (Bsub : ℝ) *
    (‖incrementsFreeComplexCoordinate coord‖ * TP +
      ‖Complex.I • incrementsFreeComplexCoordinate coord‖ * TQ)
  let Cf := ‖(incrementsFreeComplexCoordinate coord).comp
    (ContinuousLinearMap.apply ℝ V v)‖ * Cv
  let C := Cf + (‖ContinuousLinearMap.apply ℝ ℂ v‖ + 2 ^ j * ‖H‖ * Bnd) * CZ
  have hTP : 0 ≤ TP := by dsimp [TP, Cr, profile]; positivity
  have hTQ : 0 ≤ TQ := by dsimp [TQ, Cr, profile]; positivity
  refine ⟨C, by dsimp [C, Cf, CZ]; positivity, ?_⟩
  intro A _ hCard F hF chart T _ _ O S hO hSO L input inputbar cutoff phi normal
    hL hInput hInputbar hCut hPhi
    hNormal hA hB hG hJ hT0 k kbar hk hkbar ell tau Delta hell hell1 htau htauell hDelta
    hReserve hLb hInputb hInputbarb hCutb hNormalb hInputd hAb hBb hGb hJb hT0b
    hkb hkbarb hkd hPhib
  let b := fun y ↦ cutoff y * Real.sqrt (L y (input y))
  let bbar := fun y ↦ cutoff y * Real.sqrt (L y (inputbar y))
  let PR := fun a ↦ incrementsPrimaryReconstructedChannel F hF chart
    incrementsModeRealPart tau p (k a)
  let QR := fun a ↦ incrementsPrimaryReconstructedChannel F hF chart
    incrementsModeImagPart tau p (k a)
  let Pbar := fun a ↦ incrementsPrimaryReconstructedChannel F hF chart
    incrementsModeRealPart tau p (kbar a)
  let Qbar := fun a ↦ incrementsPrimaryReconstructedChannel F hF chart
    incrementsModeImagPart tau p (kbar a)
  have hPs : ∀ a, ContDiffOn ℝ ∞ (PR a) O := fun a ↦
    increments_primary_reconstructed_channel_contDiffOn F hF chart _ tau p (k a) O hO
      hA hB hG hJ hT0 (hk a)
  have hQs : ∀ a, ContDiffOn ℝ ∞ (QR a) O := fun a ↦
    increments_primary_reconstructed_channel_contDiffOn F hF chart _ tau p (k a) O hO
      hA hB hG hJ hT0 (hk a)
  have hPbs : ∀ a, ContDiffOn ℝ ∞ (Pbar a) O := fun a ↦
    increments_primary_reconstructed_channel_contDiffOn F hF chart _ tau p (kbar a) O hO
      hA hB hG hJ hT0 (hkbar a)
  have hQbs : ∀ a, ContDiffOn ℝ ∞ (Qbar a) O := fun a ↦
    increments_primary_reconstructed_channel_contDiffOn F hF chart _ tau p (kbar a) O hO
      hA hB hG hJ hT0 (hkbar a)
  have hBudget : j + 1 + p + 1 = j + p + 2 := by omega
  have hCor (ch : Cdata →L[ℝ] D) (a : A) :=
    increments_primary_reconstructed_channel_scaled_bounds F hF chart ch (j + 1) p O S
      hO hSO hA hB hG hJ hT0 (k a) (kbar a) (hk a) (hkbar a)
      ell tau Bnd K Delta hell hell1 htau htauell hBnd hK hDelta
      (fun i hi x hx ↦ hAb i (by omega) x hx)
      (fun i hi x hx ↦ hBb i (by omega) x hx) hGb hJb hT0b
      (fun i hi x hx ↦ hkb a i (by omega) x hx)
      (fun i hi x hx ↦ hkbarb a i (by omega) x hx)
      (fun i hi x hx ↦ hkd a i (by omega) x hx)
  have hPb : ∀ a, ∀ i ≤ j + 1, ∀ x ∈ S,
      ell ^ (i + 1) * ‖iteratedFDeriv ℝ i (PR a) x‖ ≤ TP * tau ^ 2 := by
    intro a i hi x hx
    simpa only [hBudget] using (hCor incrementsModeRealPart a).1 i hi x hx
  have hQb : ∀ a, ∀ i ≤ j + 1, ∀ x ∈ S,
      ell ^ (i + 1) * ‖iteratedFDeriv ℝ i (QR a) x‖ ≤ TQ * tau ^ 2 := by
    intro a i hi x hx
    simpa only [hBudget] using (hCor incrementsModeImagPart a).1 i hi x hx
  have hPbarb : ∀ a, ∀ i ≤ j + 1, ∀ x ∈ S,
      ell ^ (i + 1) * ‖iteratedFDeriv ℝ i (Pbar a) x‖ ≤ TP * tau ^ 2 := by
    intro a i hi x hx
    simpa only [hBudget] using (hCor incrementsModeRealPart a).2.1 i hi x hx
  have hQbarb : ∀ a, ∀ i ≤ j + 1, ∀ x ∈ S,
      ell ^ (i + 1) * ‖iteratedFDeriv ℝ i (Qbar a) x‖ ≤ TQ * tau ^ 2 := by
    intro a i hi x hx
    simpa only [hBudget] using (hCor incrementsModeImagPart a).2.1 i hi x hx
  have hPd : ∀ a, ∀ i ≤ j + 1, ∀ x ∈ S,
      ell ^ (i + 1) * ‖iteratedFDeriv ℝ i (fun y ↦ PR a y - Pbar a y) x‖ ≤
        TP * tau ^ 2 * Delta := by
    intro a i hi x hx
    simpa only [hBudget] using (hCor incrementsModeRealPart a).2.2 i hi x hx
  have hQd : ∀ a, ∀ i ≤ j + 1, ∀ x ∈ S,
      ell ^ (i + 1) * ‖iteratedFDeriv ℝ i (fun y ↦ QR a y - Qbar a y) x‖ ≤
        TQ * tau ^ 2 * Delta := by
    intro a i hi x hx
    simpa only [hBudget] using (hCor incrementsModeImagPart a).2.2 i hi x hx
  have hFa := hFree O S hO hSO L input inputbar cutoff normal hL hInput hInputbar hCut hNormal
    ell Delta 1 tau hell hDelta hReserve
    (fun i hi x hx ↦ hLb i (by omega) x hx)
    (fun i hi x hx ↦ hInputb i (by omega) x hx)
    (fun i hi x hx ↦ hInputbarb i (by omega) x hx)
    (fun i hi x hx ↦ hCutb i (by omega) x hx)
    (fun i hi x hx ↦ hNormalb i (by omega) x hx)
    (fun i hi x hx ↦ hInputd i (by omega) x hx)
  have hFb := hFree O S hO hSO L inputbar inputbar cutoff normal hL hInputbar hInputbar
    hCut hNormal ell Delta 1 tau hell hDelta
    (fun y hy ↦ ⟨(hReserve y hy).2, (hReserve y hy).2⟩)
    (fun i hi x hx ↦ hLb i (by omega) x hx)
    (fun i hi x hx ↦ hInputbarb i (by omega) x hx)
    (fun i hi x hx ↦ hInputbarb i (by omega) x hx)
    (fun i hi x hx ↦ hCutb i (by omega) x hx)
    (fun i hi x hx ↦ hNormalb i (by omega) x hx)
    (fun i hi x hx ↦ by simpa using hDelta)
  have hva : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (incrementsPrimaryFreeAmplitude 1 tau b normal) x‖ ≤ Cv * tau := by
    simpa only [abs_one, mul_one, abs_of_pos htau] using hFa.1
  have hvbar : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
      ‖iteratedFDeriv ℝ i (incrementsPrimaryFreeAmplitude 1 tau bbar normal) x‖ ≤ Cv * tau := by
    simpa only [abs_one, mul_one, abs_of_pos htau] using hFb.1
  have hvd : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
      (fun y ↦ incrementsPrimaryFreeAmplitude 1 tau b normal y -
        incrementsPrimaryFreeAmplitude 1 tau bbar normal y) x‖ ≤ Cv * tau * Delta := by
    simpa only [abs_one, mul_one, abs_of_pos htau] using hFa.2
  let a := fun y ↦ L y (input y)
  let abar := fun y ↦ L y (inputbar y)
  let U := (O ∩ a ⁻¹' Set.Ioi 0) ∩ (O ∩ abar ⁻¹' Set.Ioi 0)
  have ha : ContDiffOn ℝ ∞ a O := hL.clm_apply hInput
  have hab : ContDiffOn ℝ ∞ abar O := hL.clm_apply hInputbar
  have hU : IsOpen U := (ha.continuousOn.isOpen_inter_preimage hO isOpen_Ioi).inter
    (hab.continuousOn.isOpen_inter_preimage hO isOpen_Ioi)
  have hUO : U ⊆ O := fun _ hy ↦ hy.1.1
  have hSU : S ⊆ U := fun y hy ↦
    ⟨⟨hSO hy, hc.trans_le (hReserve y hy).1⟩, ⟨hSO hy, hc.trans_le (hReserve y hy).2⟩⟩
  have hb : ContDiffOn ℝ ∞ b U := (hCut.mono hUO).mul
    ((ha.mono hUO).sqrt (fun _ hy ↦ hy.1.2.ne'))
  have hbb : ContDiffOn ℝ ∞ bbar U := (hCut.mono hUO).mul
    ((hab.mono hUO).sqrt (fun _ hy ↦ hy.2.2.ne'))
  have hEa := increments_full_normalized_primary_error_scaled_jets j b phi normal PR QR
    v coord U S hU hSU hb (hNormal.mono hUO)
    (fun a ↦ (hPs a).mono hUO) (fun a ↦ (hQs a).mono hUO) (hPhi.mono hUO)
    ell tau Cv TP TQ Bnd hell htau htauell hCv hTP hTQ hBnd hva hPb hQb hPhib
  have hEb := increments_full_normalized_primary_error_scaled_jets j bbar phi normal Pbar Qbar
    v coord U S hU hSU hbb (hNormal.mono hUO)
    (fun a ↦ (hPbs a).mono hUO) (fun a ↦ (hQbs a).mono hUO) (hPhi.mono hUO)
    ell tau Cv TP TQ Bnd hell htau htauell hCv hTP hTQ hBnd hvbar hPbarb hQbarb hPhib
  have hEd := increments_full_normalized_primary_error_difference_scaled_jets j b bbar phi normal
    PR QR Pbar Qbar v coord U S hU hSU hb hbb (hNormal.mono hUO)
    (fun a ↦ (hPs a).mono hUO) (fun a ↦ (hQs a).mono hUO)
    (fun a ↦ (hPbs a).mono hUO) (fun a ↦ (hQbs a).mono hUO) (hPhi.mono hUO)
    ell tau Cv TP TQ Bnd Delta hell htau htauell hCv hTP hTQ hBnd hDelta hvd hPd hQd hPhib
  have hCmono : Cf + (‖ContinuousLinearMap.apply ℝ ℂ v‖ + 2 ^ j * ‖H‖ * Bnd) *
      ((Fintype.card A : ℝ) * (‖incrementsFreeComplexCoordinate coord‖ * TP +
        ‖Complex.I • incrementsFreeComplexCoordinate coord‖ * TQ)) ≤ C := by
    dsimp only [C, CZ]
    gcongr
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i hi x hx
    exact (hEa i hi x hx).trans (mul_le_mul_of_nonneg_right hCmono (by positivity))
  · intro i hi x hx
    exact (hEb i hi x hx).trans (mul_le_mul_of_nonneg_right hCmono (by positivity))
  · intro i hi x hx
    exact (hEd i hi x hx).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCmono (by positivity)) hDelta)

/-- BOTH actual primary errors and their SAME tensor/source-input difference are
small by tau/ell, directly from original reserve inputs and actual geometry/source
jets. The constant precedes all input members and scales. Fixed p uses only the
original j+p+2 input budget, and no half-ratio validity hypothesis is introduced.
Source: original main.tex638–661, especially equation (6.3). -/
theorem increments_actual_normalized_primary_error_bounds {A : Type*} [Fintype A]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (chart : D → M)
    (j p : ℕ) (v : D) (coord : Fin N) (c Bnd K : ℝ)
    (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
        (O S : Set D) (_hO : IsOpen O) (_hSO : S ⊆ O)
        (L : D → T →L[ℝ] ℝ) (input inputbar : D → T)
        (cutoff phi : D → ℝ) (normal : D → V)
        (_hL : ContDiffOn ℝ ∞ L O) (_hInput : ContDiffOn ℝ ∞ input O)
        (_hInputbar : ContDiffOn ℝ ∞ inputbar O) (_hCut : ContDiffOn ℝ ∞ cutoff O)
        (_hPhi : ContDiffOn ℝ ∞ phi O) (_hNormal : ContDiffOn ℝ ∞ normal O)
        (_hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF chart) O)
        (_hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF chart) O)
        (_hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ chart) y)) O)
        (_hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (chart y)).subtypeL.comp
          (incrementsModeCoordinateJ F hF chart y)) O)
        (_hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F chart) O)
        (k kbar : A → D → Cdata) (_hk : ∀ a, ContDiffOn ℝ ∞ (k a) O)
        (_hkbar : ∀ a, ContDiffOn ℝ ∞ (kbar a) O)
        (ell tau Delta : ℝ) (_hell : 0 < ell) (_hell1 : ell ≤ 1)
        (_htau : 0 < tau) (_htauell : tau ≤ ell) (_hDelta : 0 ≤ Delta)
        (_hReserve : ∀ x ∈ S, c ≤ L x (input x) ∧ c ≤ L x (inputbar x))
        (_hLb : ∀ i ≤ j + p + 2, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i L x‖ ≤ Bnd)
        (_hInputb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i input x‖ ≤ Bnd)
        (_hInputbarb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i inputbar x‖ ≤ Bnd)
        (_hCutb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i cutoff x‖ ≤ Bnd)
        (_hNormalb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i normal x‖ ≤ Bnd)
        (_hInputd : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ input y - inputbar y) x‖ ≤ Delta)
        (_hAb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderA F hF chart) x‖ ≤ Bnd)
        (_hBb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderB F hF chart) x‖ ≤ Bnd)
        (_hGb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
          ‖iteratedFDeriv ℝ i (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ chart) y)) x‖ ≤ Bnd)
        (_hJb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
          ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (chart y)).subtypeL.comp
            (incrementsModeCoordinateJ F hF chart y)) x‖ ≤ Bnd)
        (_hT0b : ∀ i ≤ j + 1, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F chart) x‖ ≤ Bnd)
        (_hkb : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (k a) x‖ ≤ K * tau)
        (_hkbarb : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (kbar a) x‖ ≤ K * tau)
        (_hkd : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ k a y - kbar a y) x‖ ≤ K * tau * Delta)
        (_hPhib : ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ fderiv ℝ phi y v) x‖ ≤ Bnd),
      let err := incrementsActualNormalizedPrimaryError F hF chart L input cutoff phi normal
        k tau p v coord
      let errbar := incrementsActualNormalizedPrimaryError F hF chart L inputbar cutoff phi normal
        kbar tau p v coord
      (∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i err x‖ ≤ C * (tau / ell)) ∧
      (∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i errbar x‖ ≤ C * (tau / ell)) ∧
      (∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i
        (fun y ↦ err y - errbar y) x‖ ≤ C * (tau / ell) * Delta) := by
  obtain ⟨C, hC, h⟩ := increments_actual_normalized_primary_error_bounds_uniform
    (I := I) (M := M) j p v coord c Bnd K (Fintype.card A) hc hBnd hK
  exact ⟨C, hC, h (A := A) le_rfl F hF chart⟩


/-- Native Pi assembly used only to collect the actual coefficients below. -/
private theorem actual_mean_scaled_pi {X ι Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [Fintype ι] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → ι → Y) (x : X) (hf : ContDiffAt ℝ ∞ f x) (k : ℕ)
    (ell C : ℝ) (hell : 0 < ell) (hC : 0 ≤ C)
    (hb : ∀ a, ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ f y a) x‖ ≤ C) :
    ell ^ k * ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
  have he : iteratedFDeriv ℝ k f x = ContinuousMultilinearMap.pi
      (fun a ↦ iteratedFDeriv ℝ k (fun y ↦ f y a) x) := by
    ext w a
    have hp := (ContinuousLinearMap.proj a).iteratedFDeriv_comp_left hf
      (by simp : (k : WithTop ℕ∞) ≤ ∞)
    exact (congrArg (fun t ↦ t w) hp).symm
  rw [he, ContinuousMultilinearMap.opNorm_pi, mul_comm (ell ^ k)]
  apply (le_div_iff₀ (pow_pos hell k)).mp
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hC (pow_nonneg hell.le k))).2
  intro a
  exact (le_div_iff₀ (pow_pos hell k)).2 (by simpa [mul_comm] using hb a)

/-- The actual full ambient mean remainder of one primary adapted chart.
All ambient coordinates and both specified tensor directions are retained.
Source: original main.tex645–661; no mean estimate is built into this definition. -/
def incrementsActualNormalizedMean {A J T : Type*} [Fintype A] [Fintype J]
    [NormedAddCommGroup T] [NormedSpace ℝ T]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (chart : D → M)
    (L : D → T →L[ℝ] ℝ) (input : D → T) (cutoff phi : D → ℝ) (normal : D → V)
    (k : A → D → Cdata) (tau : ℝ) (p : ℕ) (v : J → D) (i i' : J) (x : D) : ℂ :=
  incrementsMeanRemainder
    (fun (_ : Unit) d coord ↦ incrementsLeadingCoefficient 1
      (cutoff x * Real.sqrt (L x (input x))) (normal x)
      (fun a : J ↦ fderiv ℝ phi x (v a)) d coord)
    (fun (_ : Unit) d coord ↦ incrementsActualNormalizedPrimaryError F hF chart L input
      cutoff phi normal k tau p (v d) coord x) i i'

private theorem actual_mean_error_smooth {A : Type*} [Fintype A]
    (b phi : D → ℝ) (normal : D → V) (P Q : A → D → V)
    (tau : ℝ) (v : D) (coord : Fin N) (U : Set D) (hU : IsOpen U)
    (hb : ContDiffOn ℝ ∞ b U) (hn : ContDiffOn ℝ ∞ normal U)
    (hp : ContDiffOn ℝ ∞ phi U) (hP : ∀ a, ContDiffOn ℝ ∞ (P a) U)
    (hQ : ∀ a, ContDiffOn ℝ ∞ (Q a) U) :
    ContDiffOn ℝ ∞
      (fun y ↦ incrementsPrimaryErrorCoefficient 1 tau b phi normal P Q y v coord) U := by
  let vf := incrementsPrimaryFreeAmplitude 1 tau b normal
  let ev := (incrementsFreeComplexCoordinate coord).comp (ContinuousLinearMap.apply ℝ V v)
  have hv : ContDiffOn ℝ ∞ vf U :=
    (hb.const_smul (Real.sqrt 2 * (1 : ℝ) * tau)).smul hn
  have hf : ContDiffOn ℝ ∞ (fun y ↦ ev (fderiv ℝ vf y)) U :=
    ev.contDiff.comp_contDiffOn (hv.fderiv_of_isOpen hU (by simp))
  have hq := increments_primary_correction_coefficient_contDiffOn P Q phi v coord U hU
    hP hQ hp tau
  apply (hf.add hq).congr
  intro x hx
  rw [increments_full_normalized_primary_error_eq tau b phi normal P Q x v coord
    ((hb.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    ((hn.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (fun a ↦ ((hP a).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (fun a ↦ ((hQ a).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)),
    increments_primary_correction_coefficient_eq phi tau P Q x v coord
    (fun a ↦ ((hP a).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (fun a ↦ ((hQ a).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
  exact add_assoc _ _ _

/-- ROOT stage2 interface, source main.tex645–661. Use the uniform E provider
above to choose Ce for each FIXED spatial direction and target coordinate before
A,F,hF,chart. Leading constants Cl already come from the accepted uniform reserve
and phase-gradient provider and contain no geometry-map/chart or subordinate
count. Keep the SAME Mcoef=sum_(direction,coordinate)(Ce+Cl) and the existing
C=6*norm(actualUnitBilinear)*2^j*Mcoef^2. Introduce A/cardcap/F/hF/chart only now,
and execute the SAME accepted actual Unit-mean proof body once. Every E, leading
and mean bound is still derived from original fields and actual input jets. The
literal REAL finiteCj conclusions/finiteness remain unchanged. The old published
HEADER/DOC stay exactly and its proof becomes specialization Bsub=card A. Fixed
finite J/v is the original spatial coordinate-direction family, not a varying
chart or parameter index. No generic quadratic estimate is reproved.
Expected one named sorry in this stage2 draft only; ROOT must lock the ABI first. -/
theorem increments_actual_normalized_mean_bounds_uniform {J : Type*} [Fintype J]
    (j p : ℕ) (v : J → D) (i i' : J) (c Bnd K : ℝ) (Bsub : ℕ)
    (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {A : Type*} [Fintype A] (_hCard : Fintype.card A ≤ Bsub)
        (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (chart : D → M),
      ∀ {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
        (O S : Set D) (_hO : IsOpen O) (_hSO : S ⊆ O)
        (L : D → T →L[ℝ] ℝ) (input inputbar : D → T)
        (cutoff phi : D → ℝ) (normal : D → V)
        (_hL : ContDiffOn ℝ ∞ L O) (_hInput : ContDiffOn ℝ ∞ input O)
        (_hInputbar : ContDiffOn ℝ ∞ inputbar O) (_hCut : ContDiffOn ℝ ∞ cutoff O)
        (_hPhi : ContDiffOn ℝ ∞ phi O) (_hNormal : ContDiffOn ℝ ∞ normal O)
        (_hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF chart) O)
        (_hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF chart) O)
        (_hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ chart) y)) O)
        (_hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (chart y)).subtypeL.comp
          (incrementsModeCoordinateJ F hF chart y)) O)
        (_hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F chart) O)
        (k kbar : A → D → Cdata) (_hk : ∀ a, ContDiffOn ℝ ∞ (k a) O)
        (_hkbar : ∀ a, ContDiffOn ℝ ∞ (kbar a) O)
        (ell tau Delta : ℝ) (_hell : 0 < ell) (_hell1 : ell ≤ 1)
        (_htau : 0 < tau) (_htauell : tau ≤ ell) (_hDelta : 0 ≤ Delta)
        (_hReserve : ∀ x ∈ S, c ≤ L x (input x) ∧ c ≤ L x (inputbar x))
        (_hLb : ∀ i ≤ j + p + 2, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i L x‖ ≤ Bnd)
        (_hInputb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i input x‖ ≤ Bnd)
        (_hInputbarb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i inputbar x‖ ≤ Bnd)
        (_hCutb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i cutoff x‖ ≤ Bnd)
        (_hNormalb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i normal x‖ ≤ Bnd)
        (_hInputd : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ input y - inputbar y) x‖ ≤ Delta)
        (_hAb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderA F hF chart) x‖ ≤ Bnd)
        (_hBb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderB F hF chart) x‖ ≤ Bnd)
        (_hGb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
          ‖iteratedFDeriv ℝ i (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ chart) y)) x‖ ≤ Bnd)
        (_hJb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
          ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (chart y)).subtypeL.comp
            (incrementsModeCoordinateJ F hF chart y)) x‖ ≤ Bnd)
        (_hT0b : ∀ i ≤ j + 1, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F chart) x‖ ≤ Bnd)
        (_hkb : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (k a) x‖ ≤ K * tau)
        (_hkbarb : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (kbar a) x‖ ≤ K * tau)
        (_hkd : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ k a y - kbar a y) x‖ ≤ K * tau * Delta)
        (_hPhib : ∀ d, ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ fderiv ℝ phi y (v d)) x‖ ≤ Bnd),
      let meanA := incrementsActualNormalizedMean F hF chart L input cutoff phi normal
        k tau p v i i'
      let meanB := incrementsActualNormalizedMean F hF chart L inputbar cutoff phi normal
        kbar tau p v i i'
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r meanA x‖ ≤ C * (tau / ell)) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r meanB x‖ ≤ C * (tau / ell)) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
        (fun y ↦ meanA y - meanB y) x‖ ≤ C * (tau / ell) * Delta) ∧
      (let realA := fun y ↦ incrementsMeanRealCoordinate (meanA y)
       (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r realA x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r realA S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * (C * (tau / ell))) ∧
      (let realB := fun y ↦ incrementsMeanRealCoordinate (meanB y)
       (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r realB x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r realB S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * (C * (tau / ell))) ∧
      (let realDiff := fun y ↦ incrementsMeanRealCoordinate (meanA y - meanB y)
       (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r realDiff x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r realDiff S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * (C * (tau / ell) * Delta)) := by
  classical
  choose Ce hCe hError using fun (d : J) (co : Fin N) ↦
    increments_actual_normalized_primary_error_bounds_uniform (I := I) (M := M) j p (v d) co
      c Bnd K Bsub hc hBnd hK
  choose Cl hCl hLeading using fun (d : J) (co : Fin N) ↦
    increments_normalized_primary_leading_scaled_bounds co (v d) j c Bnd hc hBnd
  let Mcoef := ∑ a : J × Fin N, (Ce a.1 a.2 + Cl a.1 a.2)
  have hMcoef : 0 ≤ Mcoef := Finset.sum_nonneg fun a _ ↦ add_nonneg (hCe a.1 a.2) (hCl a.1 a.2)
  have hCeM (d : J) (co : Fin N) : Ce d co ≤ Mcoef :=
    (le_add_of_nonneg_right (hCl d co)).trans
      (Finset.single_le_sum (fun a _ ↦ add_nonneg (hCe a.1 a.2) (hCl a.1 a.2))
        (Finset.mem_univ (d, co)))
  have hClM (d : J) (co : Fin N) : Cl d co ≤ Mcoef :=
    (le_add_of_nonneg_left (hCe d co)).trans
      (Finset.single_le_sum (fun a _ ↦ add_nonneg (hCe a.1 a.2) (hCl a.1 a.2))
        (Finset.mem_univ (d, co)))
  let C := 6 * ‖incrementsMeanBilinear (Λ := Unit) (N := N) i i'‖ * 2 ^ j * Mcoef ^ 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro A _ hCard F hF chart T _ _ O S hO hSO L input inputbar cutoff phi normal
    hL hInput hInputbar hCut hPhi
    hNormal hA hB hG hJ hT0 k kbar hk hkbar ell tau Delta hell hell1 htau htauell hDelta
    hReserve hLb hInputb hInputbarb hCutb hNormalb hInputd hAb hBb hGb hJb hT0b
    hkb hkbarb hkd hPhib
  have hEr (d : J) (co : Fin N) :=
    hError d co hCard F hF chart O S hO hSO L input inputbar cutoff phi normal
    hL hInput hInputbar hCut hPhi hNormal hA hB hG hJ hT0 k kbar hk hkbar
    ell tau Delta hell hell1 htau htauell hDelta hReserve hLb hInputb hInputbarb hCutb
    hNormalb hInputd hAb hBb hGb hJb hT0b hkb hkbarb hkd (hPhib d)
  have hLa (d : J) (co : Fin N) := hLeading d co O S hO hSO L input inputbar cutoff phi normal
    hL hInput hInputbar hCut hPhi hNormal ell Delta hell hDelta hReserve
    (fun r hr x hx ↦ hLb r (by omega) x hx)
    (fun r hr x hx ↦ hInputb r (by omega) x hx)
    (fun r hr x hx ↦ hInputbarb r (by omega) x hx)
    (fun r hr x hx ↦ hCutb r (by omega) x hx)
    (fun r hr x hx ↦ hNormalb r (by omega) x hx) (hPhib d)
    (fun r hr x hx ↦ hInputd r (by omega) x hx)
  have hLb' (d : J) (co : Fin N) := hLeading d co O S hO hSO L inputbar inputbar
    cutoff phi normal hL hInputbar hInputbar hCut hPhi hNormal ell Delta hell hDelta
    (fun x hx ↦ ⟨(hReserve x hx).2, (hReserve x hx).2⟩)
    (fun r hr x hx ↦ hLb r (by omega) x hx)
    (fun r hr x hx ↦ hInputbarb r (by omega) x hx)
    (fun r hr x hx ↦ hInputbarb r (by omega) x hx)
    (fun r hr x hx ↦ hCutb r (by omega) x hx)
    (fun r hr x hx ↦ hNormalb r (by omega) x hx) (hPhib d)
    (fun r hr x hx ↦ by simpa using hDelta)
  let b := fun y ↦ cutoff y * Real.sqrt (L y (input y))
  let bbar := fun y ↦ cutoff y * Real.sqrt (L y (inputbar y))
  let LA : D → Unit → J → Fin N → ℂ := fun y _ d co ↦
    incrementsLeadingCoefficient 1 (b y) (normal y)
      (fun a : J ↦ fderiv ℝ phi y (v a)) d co
  let LB : D → Unit → J → Fin N → ℂ := fun y _ d co ↦
    incrementsLeadingCoefficient 1 (bbar y) (normal y)
      (fun a : J ↦ fderiv ℝ phi y (v a)) d co
  let EA : D → Unit → J → Fin N → ℂ := fun y _ d co ↦
    incrementsActualNormalizedPrimaryError F hF chart L input cutoff phi normal k tau p (v d) co y
  let EB : D → Unit → J → Fin N → ℂ := fun y _ d co ↦
    incrementsActualNormalizedPrimaryError F hF chart L inputbar cutoff phi normal
      kbar tau p (v d) co y
  let a := fun y ↦ L y (input y)
  let abar := fun y ↦ L y (inputbar y)
  let U := (O ∩ a ⁻¹' Set.Ioi 0) ∩ (O ∩ abar ⁻¹' Set.Ioi 0)
  have ha : ContDiffOn ℝ ∞ a O := hL.clm_apply hInput
  have hab : ContDiffOn ℝ ∞ abar O := hL.clm_apply hInputbar
  have hU : IsOpen U := (ha.continuousOn.isOpen_inter_preimage hO isOpen_Ioi).inter
    (hab.continuousOn.isOpen_inter_preimage hO isOpen_Ioi)
  have hUO : U ⊆ O := fun _ hy ↦ hy.1.1
  have hSU : S ⊆ U := fun y hy ↦
    ⟨⟨hSO hy, hc.trans_le (hReserve y hy).1⟩, ⟨hSO hy, hc.trans_le (hReserve y hy).2⟩⟩
  have hb : ContDiffOn ℝ ∞ b U := (hCut.mono hUO).mul
    ((ha.mono hUO).sqrt (fun _ hy ↦ hy.1.2.ne'))
  have hbb : ContDiffOn ℝ ∞ bbar U := (hCut.mono hUO).mul
    ((hab.mono hUO).sqrt (fun _ hy ↦ hy.2.2.ne'))
  have leadSmooth (b0 : D → ℝ) (hb0 : ContDiffOn ℝ ∞ b0 U) :
      ContDiffOn ℝ ∞ (fun y (_ : Unit) d co ↦ incrementsLeadingCoefficient 1 (b0 y)
        (normal y) (fun a : J ↦ fderiv ℝ phi y (v a)) d co) U := by
    apply contDiffOn_pi.2; intro u
    apply contDiffOn_pi.2; intro d
    apply contDiffOn_pi.2; intro co
    have hv : ContDiffOn ℝ ∞ (incrementsPrimaryFreeAmplitude 1 1 b0 normal) U :=
      (hb0.const_smul (Real.sqrt 2 * (1 : ℝ) * 1)).smul (hNormal.mono hUO)
    have hp : ContDiffOn ℝ ∞ (fun y ↦ fderiv ℝ phi y (v d)) U :=
      (ContinuousLinearMap.apply ℝ ℝ (v d)).contDiff.comp_contDiffOn
        ((hPhi.mono hUO).fderiv_of_isOpen hU (by simp))
    have hprod := (((Complex.I • Complex.ofRealCLM).contDiff.comp_contDiffOn hp).mul
      ((incrementsFreeComplexCoordinate co).contDiff.comp_contDiffOn hv))
    apply hprod.congr
    intro y hy
    exact increments_normalized_leading_from_free b0 normal y
      (fun a : J ↦ fderiv ℝ phi y (v a)) d co
  have hLAs : ContDiffOn ℝ ∞ LA U := leadSmooth b hb
  have hLBs : ContDiffOn ℝ ∞ LB U := leadSmooth bbar hbb
  have errorSmooth (inp : D → T) (b0 : D → ℝ) (hb0 : ContDiffOn ℝ ∞ b0 U)
      (src : A → D → Cdata) (hsrc : ∀ z, ContDiffOn ℝ ∞ (src z) O)
      (hbdef : b0 = fun y ↦ cutoff y * Real.sqrt (L y (inp y))) :
      ContDiffOn ℝ ∞ (fun y (_ : Unit) d co ↦
        incrementsActualNormalizedPrimaryError F hF chart L inp cutoff phi normal
          src tau p (v d) co y) U := by
    apply contDiffOn_pi.2; intro u
    apply contDiffOn_pi.2; intro d
    apply contDiffOn_pi.2; intro co
    rw [hbdef] at hb0
    apply actual_mean_error_smooth _ phi normal _ _ tau (v d) co U hU hb0
      (hNormal.mono hUO) (hPhi.mono hUO)
    · intro z
      exact (increments_primary_reconstructed_channel_contDiffOn F hF chart
        incrementsModeRealPart tau p (src z) O hO hA hB hG hJ hT0 (hsrc z)).mono hUO
    · intro z
      exact (increments_primary_reconstructed_channel_contDiffOn F hF chart
        incrementsModeImagPart tau p (src z) O hO hA hB hG hJ hT0 (hsrc z)).mono hUO
  have hEAs : ContDiffOn ℝ ∞ EA U := errorSmooth input b hb k hk rfl
  have hEBs : ContDiffOn ℝ ∞ EB U := errorSmooth inputbar bbar hbb kbar hkbar rfl
  have assemble (f : D → Unit → J → Fin N → ℂ) (hf : ContDiffOn ℝ ∞ f U)
      (C0 : ℝ) (hC0 : 0 ≤ C0)
      (hcomp : ∀ (u : Unit) d co, ∀ r ≤ j, ∀ x ∈ S,
        ell ^ r * ‖iteratedFDeriv ℝ r (fun y ↦ f y u d co) x‖ ≤ C0) :
      ∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r f x‖ ≤ C0 := by
    intro r hr x hx
    have hs := hf.contDiffAt (hU.mem_nhds (hSU hx))
    apply actual_mean_scaled_pi f x hs r ell C0 hell hC0
    intro u
    apply actual_mean_scaled_pi _ x (contDiffAt_pi.1 hs u) r ell C0 hell hC0
    intro d
    apply actual_mean_scaled_pi _ x (contDiffAt_pi.1 (contDiffAt_pi.1 hs u) d)
      r ell C0 hell hC0
    intro co
    exact hcomp u d co r hr x hx
  have hLA := assemble LA hLAs Mcoef hMcoef (by
    intro u d co r hr x hx
    exact ((hLa d co).1 r hr x hx).trans (hClM d co))
  have hLB := assemble LB hLBs Mcoef hMcoef (by
    intro u d co r hr x hx
    exact ((hLb' d co).1 r hr x hx).trans (hClM d co))
  have hEA := assemble EA hEAs (Mcoef * (tau / ell)) (by positivity) (by
    intro u d co r hr x hx
    exact ((hEr d co).1 r hr x hx).trans
      (mul_le_mul_of_nonneg_right (hCeM d co) (by positivity)))
  have hEB := assemble EB hEBs (Mcoef * (tau / ell)) (by positivity) (by
    intro u d co r hr x hx
    exact ((hEr d co).2.1 r hr x hx).trans
      (mul_le_mul_of_nonneg_right (hCeM d co) (by positivity)))
  have hLd := assemble (LA - LB) (hLAs.sub hLBs) (Mcoef * Delta) (by positivity) (by
    intro u d co r hr x hx
    exact ((hLa d co).2 r hr x hx).trans
      (mul_le_mul_of_nonneg_right (hClM d co) hDelta))
  have hEd := assemble (EA - EB) (hEAs.sub hEBs) (Mcoef * (tau / ell) * Delta)
    (by positivity) (by
    intro u d co r hr x hx
    exact ((hEr d co).2.2 r hr x hx).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hCeM d co) (by positivity)) hDelta))
  have heps : 0 ≤ tau / ell := by positivity
  have heps1 : tau / ell ≤ 1 := (div_le_one hell).2 htauell
  let meanA := fun y ↦ incrementsMeanRemainder (LA y) (EA y) i i'
  let meanB := fun y ↦ incrementsMeanRemainder (LB y) (EB y) i i'
  have hmean :
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r meanA x‖ ≤ C * (tau / ell)) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r meanB x‖ ≤ C * (tau / ell)) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
        (fun y ↦ meanA y - meanB y) x‖ ≤ C * (tau / ell) * Delta) := by
    refine ⟨?_, ?_, ?_⟩
    · intro r hr x hx
      have hres := incrementsMeanRemainder_scaled_jet U hU LA EA hLAs hEAs i i' r ell
        Mcoef (tau / ell) hell.le hMcoef heps heps1 (hSU hx)
        (fun s hs ↦ hLA s (hs.trans hr) x hx) (fun s hs ↦ hEA s (hs.trans hr) x hx)
      apply hres.trans
      dsimp [C]
      gcongr <;> norm_num
    · intro r hr x hx
      have hres := incrementsMeanRemainder_scaled_jet U hU LB EB hLBs hEBs i i' r ell
        Mcoef (tau / ell) hell.le hMcoef heps heps1 (hSU hx)
        (fun s hs ↦ hLB s (hs.trans hr) x hx) (fun s hs ↦ hEB s (hs.trans hr) x hx)
      apply hres.trans
      dsimp [C]
      gcongr <;> norm_num
    · intro r hr x hx
      have hres := incrementsMeanRemainder_difference_scaled_jet U hU LA EA LB EB
        hLAs hEAs hLBs hEBs i i' r ell Mcoef (tau / ell) Delta hell.le hMcoef
        heps heps1 hDelta (hSU hx)
        (fun s hs ↦ hLA s (hs.trans hr) x hx) (fun s hs ↦ hEB s (hs.trans hr) x hx)
        (fun s hs ↦ hLB s (hs.trans hr) x hx) (fun s hs ↦ hEA s (hs.trans hr) x hx)
        (fun s hs ↦ hLd s (hs.trans hr) x hx) (fun s hs ↦ hEd s (hs.trans hr) x hx)
      apply hres.trans
      dsimp [C]
      gcongr; norm_num

  have hmAs : ContDiffOn ℝ ∞ meanA U :=
    incrementsMeanRemainder_contDiffOn U LA EA hLAs hEAs i i'
  have hmBs : ContDiffOn ℝ ∞ meanB U :=
    incrementsMeanRemainder_contDiffOn U LB EB hLBs hEBs i i'
  have realNorm (f : D → ℂ) (hf : ContDiffOn ℝ ∞ f U) (T0 : ℝ) (hT0 : 0 ≤ T0)
      (hbound : ∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r f x‖ ≤ T0) :
      let g := fun y ↦ incrementsMeanRealCoordinate (f y)
      (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r g x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r g S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * T0 := by
    apply scaled_finiteCj_sum_le j _ S ell T0 hell hell1 hT0
    intro r hr x hx
    exact (mul_le_mul_of_nonneg_left
      (incrementsMeanRealCoordinate_jet_le f x (hf.contDiffAt (hU.mem_nhds (hSU hx))) r)
      (pow_nonneg hell.le r)).trans (hbound r hr x hx)
  dsimp only
  exact ⟨hmean.1, hmean.2.1, hmean.2.2,
    realNorm meanA hmAs _ (by dsimp [C]; positivity) hmean.1,
    realNorm meanB hmBs _ (by dsimp [C]; positivity) hmean.2.1,
    realNorm (fun y ↦ meanA y - meanB y) (hmAs.sub hmBs) _
      (by dsimp [C]; positivity) hmean.2.2⟩

/-- The literal full ambient normalized mean remainder has SIZE and SAME input
DIFFERENCE from original reserve/geometry/source jets. Both actual coefficient
families are constructed here; no leading/error/mean output bound is a premise.
Source: original main.tex645–661. Global primary overlap remains a caller obligation. -/
theorem increments_actual_normalized_mean_bounds {A J : Type*} [Fintype A] [Fintype J]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (chart : D → M)
    (j p : ℕ) (v : J → D) (i i' : J) (c Bnd K : ℝ)
    (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
        (O S : Set D) (_hO : IsOpen O) (_hSO : S ⊆ O)
        (L : D → T →L[ℝ] ℝ) (input inputbar : D → T)
        (cutoff phi : D → ℝ) (normal : D → V)
        (_hL : ContDiffOn ℝ ∞ L O) (_hInput : ContDiffOn ℝ ∞ input O)
        (_hInputbar : ContDiffOn ℝ ∞ inputbar O) (_hCut : ContDiffOn ℝ ∞ cutoff O)
        (_hPhi : ContDiffOn ℝ ∞ phi O) (_hNormal : ContDiffOn ℝ ∞ normal O)
        (_hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF chart) O)
        (_hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF chart) O)
        (_hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ chart) y)) O)
        (_hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (chart y)).subtypeL.comp
          (incrementsModeCoordinateJ F hF chart y)) O)
        (_hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue F chart) O)
        (k kbar : A → D → Cdata) (_hk : ∀ a, ContDiffOn ℝ ∞ (k a) O)
        (_hkbar : ∀ a, ContDiffOn ℝ ∞ (kbar a) O)
        (ell tau Delta : ℝ) (_hell : 0 < ell) (_hell1 : ell ≤ 1)
        (_htau : 0 < tau) (_htauell : tau ≤ ell) (_hDelta : 0 ≤ Delta)
        (_hReserve : ∀ x ∈ S, c ≤ L x (input x) ∧ c ≤ L x (inputbar x))
        (_hLb : ∀ i ≤ j + p + 2, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i L x‖ ≤ Bnd)
        (_hInputb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i input x‖ ≤ Bnd)
        (_hInputbarb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i inputbar x‖ ≤ Bnd)
        (_hCutb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i cutoff x‖ ≤ Bnd)
        (_hNormalb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i normal x‖ ≤ Bnd)
        (_hInputd : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ input y - inputbar y) x‖ ≤ Delta)
        (_hAb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderA F hF chart) x‖ ≤ Bnd)
        (_hBb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderB F hF chart) x‖ ≤ Bnd)
        (_hGb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
          ‖iteratedFDeriv ℝ i (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ chart) y)) x‖ ≤ Bnd)
        (_hJb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
          ‖iteratedFDeriv ℝ i (fun y ↦ (normalSpace (I := I) F (chart y)).subtypeL.comp
            (incrementsModeCoordinateJ F hF chart y)) x‖ ≤ Bnd)
        (_hT0b : ∀ i ≤ j + 1, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeTransverseValue F chart) x‖ ≤ Bnd)
        (_hkb : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (k a) x‖ ≤ K * tau)
        (_hkbarb : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (kbar a) x‖ ≤ K * tau)
        (_hkd : ∀ a, ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ k a y - kbar a y) x‖ ≤ K * tau * Delta)
        (_hPhib : ∀ d, ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ fderiv ℝ phi y (v d)) x‖ ≤ Bnd),
      let meanA := incrementsActualNormalizedMean F hF chart L input cutoff phi normal
        k tau p v i i'
      let meanB := incrementsActualNormalizedMean F hF chart L inputbar cutoff phi normal
        kbar tau p v i i'
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r meanA x‖ ≤ C * (tau / ell)) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r meanB x‖ ≤ C * (tau / ell)) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
        (fun y ↦ meanA y - meanB y) x‖ ≤ C * (tau / ell) * Delta) ∧
      (let realA := fun y ↦ incrementsMeanRealCoordinate (meanA y)
       (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r realA x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r realA S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * (C * (tau / ell))) ∧
      (let realB := fun y ↦ incrementsMeanRealCoordinate (meanB y)
       (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r realB x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r realB S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * (C * (tau / ell))) ∧
      (let realDiff := fun y ↦ incrementsMeanRealCoordinate (meanA y - meanB y)
       (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r realDiff x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r realDiff S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * (C * (tau / ell) * Delta)) := by
  obtain ⟨C, hC, h⟩ := increments_actual_normalized_mean_bounds_uniform
    (I := I) (M := M) j p v i i' c Bnd K (Fintype.card A) hc hBnd hK
  exact ⟨C, hC, h (A := A) le_rfl F hF chart⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.incrementsActualNormalizedMean
#print axioms GlobalEmbedding.Paper.incrementsActualNormalizedPrimaryError
#print axioms GlobalEmbedding.Paper.increments_actual_normalized_mean_bounds
#print axioms GlobalEmbedding.Paper.increments_actual_normalized_primary_error_bounds

#print axioms GlobalEmbedding.Paper.increments_actual_normalized_primary_error_bounds_uniform

#print axioms GlobalEmbedding.Paper.increments_actual_normalized_mean_bounds_uniform
