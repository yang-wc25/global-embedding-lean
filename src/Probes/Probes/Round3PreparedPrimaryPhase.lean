import Probes.Round3PhaseSignedPreparation
import Probes.Round3PreparedOriginalDomains

/-! The literal primary phase obtains its quantitative compact preparation
from the original primary Good condition and the original joint smoothness.
The resulting constants precede every later derivative order. -/

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

theorem round3_actual_original_primary_phase_preparation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUprim : U ⊆ actualOriginalPrimaryNativeOpen Data nu i) :
    let psi := fun z : X => Data.phase nu ((Data.parameterChart i.2).symm z.1,
      (Data.atlas.chart i.1).symm z.2)
    ∃ (mu Mb R rho : ℝ) (O : Set X),
      0 < mu ∧ 0 ≤ Mb ∧ 0 < R ∧ 0 < rho ∧
      IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧ K ⊆ closedBall 0 R ∧
      (∀ x ∈ K, ball x rho ⊆ O) ∧ ContDiffOn ℝ ∞ psi O ∧
      (∀ x ∈ K, mu ≤ ‖(fderiv ℝ psi x).comp (ContinuousLinearMap.inr ℝ Ep D)‖) ∧
      (∀ x ∈ O, ‖fderiv ℝ psi x‖ ≤ Mb) ∧
      (∀ x ∈ O, rho * ‖iteratedFDeriv ℝ 2 psi x‖ ≤ Mb) := by
  intro psi
  have hpsi : ContDiffOn ℝ ∞ psi U :=
    (round3_actual_original_primary_native_phase_smooth Data hd hs nu i).mono hUprim
  apply round3_actual_compact_phase_preparation psi K U hK hU hKU hpsi
  intro z hz
  have hactive := round3_prepared_native_primary_active Data i nu (hUprim (hKU hz))
  have hgood := hp.primary_good nu _ hactive
  have ht : z.2 ∈ (Data.atlas.chart i.1).target := by
    have h := (hUprim (hKU hz)).1.1.1
    have he := congrArg Prod.snd ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
    change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z) = z.2 at he
    rwa [he] at h
  exact round3_actual_host_phase_spatial_ne_zero (Data.atlas.chart i.1)
    (hd.atlas_smooth.chart_mem i.1)
    (fun w : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm w.1,w.2)) z ht
    ((hpsi.contDiffAt (hU.mem_nhds (hKU hz))).differentiableAt (by simp)) hgood.1

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_actual_original_primary_phase_preparation
