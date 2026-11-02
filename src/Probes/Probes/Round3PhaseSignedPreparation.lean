import Probes.Round3PhaseOriginalNoncritical
import Probes.ActualIncrementOriginalCoreFields

/-! The literal ordered signed phase is prepared from the original smooth
inputs and original Good-on-support hypothesis. The compact carrier can be
the effective intersection of the two primary supports; no condition is
imposed on the inactive remainder of an ordinary partition function. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem round3_actual_original_primary_native_phase_smooth
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    ContDiffOn ℝ ∞
      (fun z : X => Data.phase nu ((Data.parameterChart i.2).symm z.1,
        (Data.atlas.chart i.1).symm z.2))
      (actualOriginalPrimaryNativeOpen Data nu i) := by
  let a := parameterTensorModelEquiv (m+1) d
  have heq : (fun z : X => Data.phase nu ((Data.parameterChart i.2).symm z.1,
      (Data.atlas.chart i.1).symm z.2)) = actualOriginalJointPhase Data nu i ∘ a := by
    funext z
    change _ = Data.phase nu (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (a z))
    rw [actual_original_jointPoint_native]
  rw [heq]
  apply (actualOriginalJointPhase_contDiffOn Data hd hs nu i).comp a.contDiff.contDiffOn
  intro z hz
  exact ⟨hz.1, hz.1.1, hz.2⟩

theorem round3_actual_original_signed_native_phase_smooth
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : (Fin Data.primaryCount × Fin Data.primaryCount) × Fin 4) :
    ContDiffOn ℝ ∞
      (fun z : X => actualOriginalParameterSignedPhase Data i r
        (z.1,(Data.atlas.chart i.1).symm z.2))
      (actualOriginalPrimaryNativeOpen Data r.1.1 i ∩ actualOriginalPrimaryNativeOpen Data r.1.2 i) := by
  have hnu := (round3_actual_original_primary_native_phase_smooth Data hd hs r.1.1 i).mono
    (inter_subset_left (t := actualOriginalPrimaryNativeOpen Data r.1.2 i))
  have hmu := (round3_actual_original_primary_native_phase_smooth Data hd hs r.1.2 i).mono
    (inter_subset_right (s := actualOriginalPrimaryNativeOpen Data r.1.1 i))
  rcases r with ⟨⟨nu,mu⟩,q⟩
  fin_cases q
  · exact hnu.add hmu
  · exact hnu.sub hmu
  · exact hnu.neg.add hmu
  · exact hnu.neg.sub hmu

/-- Original Good on the actual compact interaction carrier produces every
quantitative low-order phase input, on one open neighborhood. -/
theorem round3_actual_original_signed_phase_preparation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUprim : U ⊆ actualOriginalPrimaryNativeOpen Data r.val.1.1 i ∩
      actualOriginalPrimaryNativeOpen Data r.val.1.2 i)
    (hKpair : ∀ z ∈ K, ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈
      incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
        incrementsOriginalRelativeCutoffSupport Data r.val.1.2) :
    let psi := fun z : X => actualOriginalParameterSignedPhase Data i r.val
      (z.1,(Data.atlas.chart i.1).symm z.2)
    ∃ (mu Mb R rho : ℝ) (O : Set X),
      0 < mu ∧ 0 ≤ Mb ∧ 0 < R ∧ 0 < rho ∧
      IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧ K ⊆ closedBall 0 R ∧
      (∀ x ∈ K, ball x rho ⊆ O) ∧ ContDiffOn ℝ ∞ psi O ∧
      (∀ x ∈ K, mu ≤ ‖(fderiv ℝ psi x).comp (ContinuousLinearMap.inr ℝ Ep D)‖) ∧
      (∀ x ∈ O, ‖fderiv ℝ psi x‖ ≤ Mb) ∧
      (∀ x ∈ O, rho * ‖iteratedFDeriv ℝ 2 psi x‖ ≤ Mb) := by
  intro psi
  have hpsi : ContDiffOn ℝ ∞ psi U :=
    (round3_actual_original_signed_native_phase_smooth Data hd hs i r.val).mono hUprim
  apply round3_actual_compact_phase_preparation psi K U hK hU hKU hpsi
  intro z hz
  have hgood := actual_original_parameter_signed_secondary_phase_good Data hd hs hp i r
    (z.1,(Data.atlas.chart i.1).symm z.2) (hKpair z hz)
  have ht : z.2 ∈ (Data.atlas.chart i.1).target := by
    have h := (hUprim (hKU hz)).1.1.1.1
    have he := congrArg Prod.snd ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
    change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z) = z.2 at he
    rwa [he] at h
  exact round3_actual_host_phase_spatial_ne_zero (Data.atlas.chart i.1)
    (hd.atlas_smooth.chart_mem i.1) (actualOriginalParameterSignedPhase Data i r.val) z ht
    ((hpsi.contDiffAt (hU.mem_nhds (hKU hz))).differentiableAt (by simp)) hgood.1

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3_actual_original_signed_phase_preparation
