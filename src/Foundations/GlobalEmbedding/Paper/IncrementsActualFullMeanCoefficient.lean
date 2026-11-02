import GlobalEmbedding.Paper.IncrementsActualNormalizedPrimaryError
import GlobalEmbedding.Paper.IncrementsPhaseGermExtraction
import GlobalEmbedding.Paper.IncrementsSupportedAmplitudeSmoothGlue
import GlobalEmbedding.Paper.IncrementsMeanQuadraticRemainder

/-!
# The actual all-primary zero-phase mean coefficient

Source: original main.tex638–661. The selected terms are determined by actual
phase germs, not equality of formal labels. Subordinate partitions are required
only at active cutoff supports. Inactive free fields are handled by zero germs;
no partition or Good condition is imposed on inactive labels. Actual
actual source supports are retained. The theorem identifies the full coefficient;
it does not establish global overlap/profile or joint-parameter estimates.
-/

noncomputable section
open Manifold Filter
open scoped Topology ContDiff ComplexConjugate
namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ

/-- The actual ALL-label zero-germ coefficient of the canonical primary wave.
The subordinate cutoff stays on the free piece; actual R already contains its
source cutoff and is never multiplied by that cutoff a second time. -/
def incrementsActualFullZeroMeanCoefficient {Λ A J T : Type*}
    [Fintype Λ] [Fintype A] [NormedAddCommGroup T] [NormedSpace ℝ T]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (chart : Λ → D → M)
    (L : Λ → D → T →L[ℝ] ℝ) (input : D → T) (cutoff phi : Λ → D → ℝ)
    (normal : Λ → D → V) (chi : Λ → A → D → ℝ)
    (k : Λ → A → D → Cdata) (tau : ℝ) (p : ℕ) (v : J → D)
    (i i' : J) (x : D) : ℂ :=
  let b := fun z y ↦ cutoff z y * Real.sqrt (L z y (input y))
  let PR := fun z a ↦ incrementsPrimaryReconstructedChannel F hF (chart z)
    incrementsModeRealPart tau p (k z a)
  let QR := fun z a ↦ incrementsPrimaryReconstructedChannel F hF (chart z)
    incrementsModeImagPart tau p (k z a)
  let coeff := fun z d ↦ incrementsPrimaryDerivativeCoefficient (phi z) tau (fun _ _ ↦ 1)
    (fun a y ↦ chi z a y • incrementsPrimaryFreeAmplitude 1 tau (b z) (normal z) y +
      PR z a y) (QR z) x (v d)
  ∑ z, ∑ w, incrementsFourPhaseZeroGermPair (fun z y ↦ phi z y / tau)
    coeff x z w i i'

/-- Only an inline consumer of native support and the published actual R split.
No new R or finite-iteration support proof is introduced. -/
theorem actual_full_mean_channel_support
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (chart : D → M)
    (ch : Cdata →L[ℝ] D) (tau : ℝ) (p : ℕ) (k : D → Cdata) :
    tsupport (incrementsPrimaryReconstructedChannel F hF chart ch tau p k) ⊆ tsupport k := by
  let u := incrementsActualModeSum (incrementsModeComplexFirstOrderA F hF chart)
    (incrementsModeComplexFirstOrderB F hF chart) ((tau : ℂ) / Complex.I) p k
  let h := ch ∘ u
  have hh : tsupport h ⊆ tsupport k :=
    (tsupport_comp_subset (map_zero ch) u).trans
      (increments_actual_mode_sum_tsupport _ _ _ p k)
  have hr : tsupport (incrementsModeReconstruction F hF chart h) ⊆ tsupport h := by
    apply closure_minimal _ (isClosed_tsupport h)
    intro y hy
    by_contra hz
    apply hy
    rw [incrementsModeReconstruction_split,
      image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz,
      map_zero, map_zero, add_zero]
  exact hr.trans hh

/-- The TRUE all-label zero-phase coefficient minus the ORIGINAL tensor equals
its actual normalized mean remainder. Original unit normals and the fixed positive
cutoff decomposition remove the leading term. Source: main.tex645–661.
Partition=1 is needed only on the primary cutoff support. Off that support
the free field has zero germ, with no partition or phase-Good condition added.
All geometry/source regularity assumptions are genuine internal producer inputs;
no desired derivative, mean estimate, or output support is assumed. -/
theorem increments_actual_full_zero_mean_eq {Λ A J T : Type*}
    [Fintype Λ] [Fintype A] [NormedAddCommGroup T] [NormedSpace ℝ T]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (chart : Λ → D → M)
    (L : Λ → D → T →L[ℝ] ℝ) (input : D → T) (cutoff phi : Λ → D → ℝ)
    (normal : Λ → D → V) (chi : Λ → A → D → ℝ)
    (k : Λ → A → D → Cdata) (tau : ℝ) (htau : tau ≠ 0) (p : ℕ)
    (v : J → D) (tensor : J → J → ℝ) (O : Set D) (hO : IsOpen O)
    (hL : ∀ z, ContDiffOn ℝ ∞ (L z) O) (hInput : ContDiffOn ℝ ∞ input O)
    (hCut : ∀ z, ContDiffOn ℝ ∞ (cutoff z) O)
    (hPhi : ∀ z, ContDiffOn ℝ ∞ (phi z) O)
    (hNormal : ∀ z, ContDiffOn ℝ ∞ (normal z) O)
    (hA : ∀ z, ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF (chart z)) O)
    (hB : ∀ z, ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF (chart z)) O)
    (hG : ∀ z, ContDiffOn ℝ ∞
      (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ chart z) y)) O)
    (hJ : ∀ z, ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (chart z y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF (chart z) y)) O)
    (hT0 : ∀ z, ContDiffOn ℝ ∞ (incrementsModeTransverseValue F (chart z)) O)
    (hk : ∀ z a, ContDiffOn ℝ ∞ (k z a) O)
    (S : Λ → Set D) (hCutSup : ∀ z, tsupport (cutoff z) ⊆ S z)
    (hkSup : ∀ z a, tsupport (k z a) ⊆ S z)
    (x : D) (hx : x ∈ O)
    (hReserve : ∀ z, x ∈ tsupport (cutoff z) → 0 < L z x (input x))
    (hUnit : ∀ z, cutoff z x ≠ 0 → ‖normal z x‖ = 1)
    (hChi : ∀ z a, DifferentiableAt ℝ (chi z a) x)
    (hPartition : ∀ z, x ∈ tsupport (cutoff z) →
      ∀ᶠ y in 𝓝 x, ∑ a, chi z a y = 1)
    (hDecomp : ∀ d e, ∑ z, (cutoff z x) ^ 2 * L z x (input x) *
      fderiv ℝ (phi z) x (v d) * fderiv ℝ (phi z) x (v e) = tensor d e)
    (hDouble : ∀ z, x ∈ S z → fderiv ℝ (fun y ↦ phi z y + phi z y) x ≠ 0)
    (hInteraction : ∀ z w, z ≠ w → x ∈ S z → x ∈ S w →
      fderiv ℝ (fun y ↦ phi z y + phi w y) x ≠ 0 ∧
        fderiv ℝ (fun y ↦ phi z y - phi w y) x ≠ 0) (i i' : J) :
    let lead := fun z d co ↦ incrementsLeadingCoefficient 1
      (cutoff z x * Real.sqrt (L z x (input x))) (normal z x)
      (fun d : J ↦ fderiv ℝ (phi z) x (v d)) d co
    let err := fun z d co ↦ incrementsActualNormalizedPrimaryError F hF (chart z)
      (L z) input (cutoff z) (phi z) (normal z) (k z) tau p (v d) co x
    let wave := incrementsPrimaryWave phi tau (fun _ _ _ ↦ 1)
      (fun z a y ↦ chi z a y • incrementsPrimaryFreeAmplitude 1 tau
        (fun y ↦ cutoff z y * Real.sqrt (L z y (input y))) (normal z) y +
        incrementsPrimaryReconstructedChannel F hF (chart z)
          incrementsModeRealPart tau p (k z a) y)
      (fun z a ↦ incrementsPrimaryReconstructedChannel F hF (chart z)
        incrementsModeImagPart tau p (k z a))
    (∀ d, fderiv ℝ wave x (v d) =
      incrementsGroupedRealDerivative (fun z ↦ phi z x / tau) (lead + err) d) ∧
    (incrementsActualFullZeroMeanCoefficient F hF chart L input cutoff phi normal chi
        k tau p v i i' x - (tensor i i' : ℂ) = incrementsMeanRemainder lead err i i') := by
  classical
  let b := fun z y ↦ cutoff z y * Real.sqrt (L z y (input y))
  let PR := fun z a ↦ incrementsPrimaryReconstructedChannel F hF (chart z)
    incrementsModeRealPart tau p (k z a)
  let QR := fun z a ↦ incrementsPrimaryReconstructedChannel F hF (chart z)
    incrementsModeImagPart tau p (k z a)
  let PF := fun z a y ↦ chi z a y • incrementsPrimaryFreeAmplitude 1 tau (b z) (normal z) y +
    PR z a y
  let coeff := fun z d ↦ incrementsPrimaryDerivativeCoefficient (phi z) tau
    (fun _ _ ↦ 1) (PF z) (QR z) x (v d)
  let lead := fun z d co ↦ incrementsLeadingCoefficient 1 (b z x) (normal z x)
    (fun d : J ↦ fderiv ℝ (phi z) x (v d)) d co
  let err := fun z d co ↦ incrementsActualNormalizedPrimaryError F hF (chart z)
    (L z) input (cutoff z) (phi z) (normal z) (k z) tau p (v d) co x
  have hPs : ∀ z a, ContDiffOn ℝ ∞ (PR z a) O := fun z a ↦
    increments_primary_reconstructed_channel_contDiffOn F hF (chart z) _ tau p (k z a)
      O hO (hA z) (hB z) (hG z) (hJ z) (hT0 z) (hk z a)
  have hQs : ∀ z a, ContDiffOn ℝ ∞ (QR z a) O := fun z a ↦
    increments_primary_reconstructed_channel_contDiffOn F hF (chart z) _ tau p (k z a)
      O hO (hA z) (hB z) (hG z) (hJ z) (hT0 z) (hk z a)
  have hQsup (z : Λ) (a : A) : tsupport (QR z a) ⊆ S z :=
    (actual_full_mean_channel_support F hF (chart z) _ tau p (k z a)).trans (hkSup z a)
  have hFreeSup (z : Λ) :
      tsupport (incrementsPrimaryFreeAmplitude 1 tau (b z) (normal z)) ⊆ S z :=
    (increments_supported_primary_free_amplitude_tsupport (L z) input (cutoff z)
      (normal z) 1 tau).trans (hCutSup z)
  have hPFsup (z : Λ) (a : A) : tsupport (PF z a) ⊆ S z :=
    (tsupport_add _ _).trans (Set.union_subset
      ((tsupport_smul_subset_right _ _).trans (hFreeSup z))
      ((actual_full_mean_channel_support F hF (chart z) _ tau p (k z a)).trans (hkSup z a)))
  have hbZero (z : Λ) (hz : x ∉ tsupport (cutoff z)) :
      b z =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport (cutoff z)).isOpen_compl.mem_nhds hz] with y hy
    simp [b, image_eq_zero_of_notMem_tsupport hy]
  have hb (z : Λ) : DifferentiableAt ℝ (b z) x := by
    by_cases hz : x ∈ tsupport (cutoff z)
    · have ha : ContDiffAt ℝ ∞ (fun y ↦ Real.sqrt (L z y (input y))) x :=
        (((hL z).clm_apply hInput).contDiffAt (hO.mem_nhds hx)).sqrt (hReserve z hz).ne'
      exact (((hCut z).contDiffAt (hO.mem_nhds hx)).mul ha).differentiableAt (by simp)
    · exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq (hbZero z hz)
  have hCoeff : coeff = lead + err := by
    funext z d co
    by_cases hz : x ∈ tsupport (cutoff z)
    · exact increments_primary_coefficient_leading 1 tau htau (b z) (phi z) (normal z)
        (chi z) (PR z) (QR z) x (v d) co (hb z)
        (((hNormal z).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
        (hChi z) (fun a ↦ ((hPs z a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
        (hPartition z hz)
    · have he (a : A) : PF z a =ᶠ[𝓝 x] PR z a := by
        filter_upwards [hbZero z hz] with y hy
        simp [PF, incrementsPrimaryFreeAmplitude, hy]
      have hval (a : A) : PF z a x = PR z a x := (he a).eq_of_nhds
      have hder (a : A) : fderiv ℝ (PF z a) x = fderiv ℝ (PR z a) x :=
        (he a).fderiv_eq (𝕜 := ℝ)
      have hD : coeff z d co = incrementsPrimaryDerivativeCoefficient (phi z) tau
          (fun _ _ ↦ 1) (PR z) (QR z) x (v d) co := by
        dsimp only [coeff]
        unfold incrementsPrimaryDerivativeCoefficient
        simp only [hval, hder]
      change coeff z d co = incrementsLeadingCoefficient 1 (b z x) (normal z x)
        (fun e : J ↦ fderiv ℝ (phi z) x (v e)) d co +
        incrementsPrimaryErrorCoefficient 1 tau (b z) (phi z) (normal z)
          (PR z) (QR z) x (v d) co
      rw [hD]
      simp [incrementsLeadingCoefficient, incrementsPrimaryErrorCoefficient,
        (hbZero z hz).eq_of_nhds, (hbZero z hz).fderiv_eq (𝕜 := ℝ)]
  have hInactive (z : Λ) (hz : x ∉ S z) :
      coeff z = 0 ∧ lead z = 0 ∧ err z = 0 := by
    have hzcut : x ∉ tsupport (cutoff z) := fun h ↦ hz (hCutSup z h)
    have hcz : coeff z = 0 := by
      funext d
      exact increments_primary_coefficient_of_notMem_support (phi z) tau (fun _ _ ↦ 1)
        (PF z) (QR z) (S z) (hPFsup z) (hQsup z) x (v d) hz
    have hlz : lead z = 0 := by
      funext d co
      simp [lead, incrementsLeadingCoefficient, (hbZero z hzcut).eq_of_nhds]
    have hez : err z = 0 := by
      funext d co
      have h := congrArg (fun f ↦ f z d co) hCoeff
      change coeff z d co = lead z d co + err z d co at h
      rw [hcz, hlz] at h
      simpa using h.symm
    exact ⟨hcz, hlz, hez⟩
  have hZero : (∑ z, ∑ w, incrementsFourPhaseZeroGermPair
      (fun z y ↦ phi z y / tau) coeff x z w i i') =
      incrementsOppositePrimaryContribution coeff i i' := by
    simp_rw [increments_four_phase_zero_germ_pair_div phi tau htau]
    exact increments_four_phase_zero_germ_eq_opposite phi coeff S x
      (fun z hz d ↦ congrFun (hInactive z hz).1 d) hDouble hInteraction i i'
  have hLeading : incrementsOppositePrimaryContribution lead i i' = (tensor i i' : ℂ) := by
    have hterm (z : Λ) : (1 / 4 : ℂ) *
        ((lead z i ⬝ᵥ (fun co ↦ conj (lead z i' co))) +
          ((fun co ↦ conj (lead z i co)) ⬝ᵥ lead z i')) =
        ((cutoff z x) ^ 2 * L z x (input x) * fderiv ℝ (phi z) x (v i) *
          fderiv ℝ (phi z) x (v i') : ℝ) := by
      by_cases hz : cutoff z x = 0
      · simp [lead, b, hz, incrementsLeadingCoefficient, dotProduct]
      · have hsqrt := Real.sq_sqrt (hReserve z (subset_tsupport (cutoff z) hz)).le
        have he := increments_leading_opposite_coefficient 1 (b z x) (normal z x)
          (hUnit z hz) (fun d : J ↦ fderiv ℝ (phi z) x (v d)) i i'
        simpa only [one_pow, one_mul, b, mul_pow, hsqrt] using he
    unfold incrementsOppositePrimaryContribution
    simp_rw [hterm]
    rw [← Complex.ofReal_sum, hDecomp]
  dsimp only
  refine ⟨?_, ?_⟩
  · intro d
    have hV (z : Λ) :
        DifferentiableAt ℝ (incrementsPrimaryFreeAmplitude 1 tau (b z) (normal z)) x :=
      ((hb z).const_smul (Real.sqrt 2 * (1 : ℝ) * tau)).smul
        (((hNormal z).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
    have hw := increments_primary_wave_grouped_derivative phi tau (fun _ _ _ ↦ 1)
      PF QR x (v d)
      (fun z ↦ ((hPhi z).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
      (fun _ _ ↦ differentiableAt_const 1)
      (fun z a ↦ ((hChi z a).smul (hV z)).add
        (((hPs z a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)))
      (fun z a ↦ ((hQs z a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
    change fderiv ℝ (incrementsPrimaryWave phi tau (fun _ _ _ ↦ 1) PF QR) x (v d) =
      incrementsGroupedRealDerivative (fun z ↦ phi z x / tau) coeff d at hw
    rw [hCoeff] at hw
    exact hw
  · change (∑ z, ∑ w, incrementsFourPhaseZeroGermPair (fun z y ↦ phi z y / tau)
      coeff x z w i i') - (tensor i i' : ℂ) = incrementsMeanRemainder lead err i i'
    rw [hZero, hCoeff, ← hLeading]
    rfl

/-- Directly connect the TRUE all-label zero coefficient to the already accepted
actual single-primary mean endpoints. Native finite summation is the only adapter;
global cardinality-independent estimates are a separate original obligation. -/
theorem increments_actual_full_zero_mean_sum_eq {Λ A J T : Type*}
    [Fintype Λ] [Fintype A] [Fintype J] [NormedAddCommGroup T] [NormedSpace ℝ T]
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (chart : Λ → D → M)
    (L : Λ → D → T →L[ℝ] ℝ) (input : D → T) (cutoff phi : Λ → D → ℝ)
    (normal : Λ → D → V) (chi : Λ → A → D → ℝ)
    (k : Λ → A → D → Cdata) (tau : ℝ) (htau : tau ≠ 0) (p : ℕ)
    (v : J → D) (tensor : J → J → ℝ) (O : Set D) (hO : IsOpen O)
    (hL : ∀ z, ContDiffOn ℝ ∞ (L z) O) (hInput : ContDiffOn ℝ ∞ input O)
    (hCut : ∀ z, ContDiffOn ℝ ∞ (cutoff z) O)
    (hPhi : ∀ z, ContDiffOn ℝ ∞ (phi z) O)
    (hNormal : ∀ z, ContDiffOn ℝ ∞ (normal z) O)
    (hA : ∀ z, ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF (chart z)) O)
    (hB : ∀ z, ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF (chart z)) O)
    (hG : ∀ z, ContDiffOn ℝ ∞
      (fun y ↦ freeGramRightInverse (fderiv ℝ (F ∘ chart z) y)) O)
    (hJ : ∀ z, ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) F (chart z y)).subtypeL.comp
      (incrementsModeCoordinateJ F hF (chart z) y)) O)
    (hT0 : ∀ z, ContDiffOn ℝ ∞ (incrementsModeTransverseValue F (chart z)) O)
    (hk : ∀ z a, ContDiffOn ℝ ∞ (k z a) O)
    (S : Λ → Set D) (hCutSup : ∀ z, tsupport (cutoff z) ⊆ S z)
    (hkSup : ∀ z a, tsupport (k z a) ⊆ S z)
    (x : D) (hx : x ∈ O)
    (hReserve : ∀ z, x ∈ tsupport (cutoff z) → 0 < L z x (input x))
    (hUnit : ∀ z, cutoff z x ≠ 0 → ‖normal z x‖ = 1)
    (hChi : ∀ z a, DifferentiableAt ℝ (chi z a) x)
    (hPartition : ∀ z, x ∈ tsupport (cutoff z) →
      ∀ᶠ y in 𝓝 x, ∑ a, chi z a y = 1)
    (hDecomp : ∀ d e, ∑ z, (cutoff z x) ^ 2 * L z x (input x) *
      fderiv ℝ (phi z) x (v d) * fderiv ℝ (phi z) x (v e) = tensor d e)
    (hDouble : ∀ z, x ∈ S z → fderiv ℝ (fun y ↦ phi z y + phi z y) x ≠ 0)
    (hInteraction : ∀ z w, z ≠ w → x ∈ S z → x ∈ S w →
      fderiv ℝ (fun y ↦ phi z y + phi w y) x ≠ 0 ∧
        fderiv ℝ (fun y ↦ phi z y - phi w y) x ≠ 0) (i i' : J) :
    (incrementsActualFullZeroMeanCoefficient F hF chart L input cutoff phi normal chi
      k tau p v i i' x - (tensor i i' : ℂ) =
        ∑ z, incrementsActualNormalizedMean F hF (chart z) (L z) input (cutoff z)
          (phi z) (normal z) (k z) tau p v i i' x) ∧
    (incrementsMeanRealCoordinate (incrementsActualFullZeroMeanCoefficient F hF chart
      L input cutoff phi normal chi k tau p v i i' x - (tensor i i' : ℂ)) =
        ∑ z, incrementsMeanRealCoordinate (incrementsActualNormalizedMean F hF (chart z)
          (L z) input (cutoff z) (phi z) (normal z) (k z) tau p v i i' x)) := by
  have hm := (increments_actual_full_zero_mean_eq F hF chart L input cutoff phi normal
    chi k tau htau p v tensor O hO hL hInput hCut hPhi hNormal hA hB hG hJ hT0 hk S
    hCutSup hkSup x hx hReserve hUnit hChi hPartition hDecomp hDouble hInteraction i i').2
  have hsum : incrementsMeanRemainder
      (fun z d co ↦ incrementsLeadingCoefficient 1
        (cutoff z x * Real.sqrt (L z x (input x))) (normal z x)
        (fun d : J ↦ fderiv ℝ (phi z) x (v d)) d co)
      (fun z d co ↦ incrementsActualNormalizedPrimaryError F hF (chart z) (L z) input
        (cutoff z) (phi z) (normal z) (k z) tau p (v d) co x) i i' =
        ∑ z, incrementsActualNormalizedMean F hF (chart z) (L z) input (cutoff z)
          (phi z) (normal z) (k z) tau p v i i' x := by
    simp [incrementsMeanRemainder, incrementsOppositePrimaryContribution,
      incrementsActualNormalizedMean, Finset.sum_sub_distrib]
  have heq := hm.trans hsum
  exact ⟨heq, by rw [heq, map_sum]⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.incrementsActualFullZeroMeanCoefficient
#print axioms GlobalEmbedding.Paper.increments_actual_full_zero_mean_eq
#print axioms GlobalEmbedding.Paper.increments_actual_full_zero_mean_sum_eq
