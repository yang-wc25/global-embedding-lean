import IncrementsCompletion.AtScaleMeanRaw
import IncrementsCompletion.AtScaleCanonicalRaw
import IncrementsCompletion.OriginalFinitePrimaryAtlas

/-! The same finite input constructs its canonical original primary output
on one actual G, at every observation order, using only current-scale prep.
The output structure is the unchanged existing original primary atlas. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
open SourceCollarsBridge CollarCompletion
variable {m d N : ℕ} {M P Β : Type*}
  [TopologicalSpace M] [TopologicalSpace P] [Fintype Β]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem incrementsCompletion_at_scale_final_primary_atlas
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (V0 : Set P) (hV0 : IsOpen V0) (hKV0 : Data.parameterSet ⊆ V0)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (ell tau c cT : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c) (hcT : 0 < cT)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (q Rsub : ℕ) (Packet Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (hGiven : ∀ j, actualOriginalGivenInputProfile Data j ell ≠ ⊤)
    (hPacket : ∀ j, (actualOriginalGivenInputProfile Data j ell).toReal ≤ Packet j)
    (prep : ∀ i, IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub ell i) :
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W := incrementsOriginalParameterRegion Data
    let hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i :=
      fun _ _ hy => hy.1
    let p := finiteTensorGermSeminorm Data.atlas Data.parameterChart S W hSO ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*Packet 0+1))
    let Bnd := fun s R0 => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) R0 Tinv
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    ∀ (H K : finiteTensorGermSpace Data.atlas Data.parameterChart S W hSO),
      H.val.val = Data.H → p 0 (K-H) < radius →
      ∀ Profile : ℕ → ℝ, (∀ s, p s K ≤ Profile s) →
      Nonempty (IncrementsCompletionOriginalPrimaryAtlas Data hd hs g hTarget V0 K.val.val
        q Rsub rho ell tau (fun s => Bnd s (Profile (s+(q+4)))) Mg Tfixed) := by
  intro S W hSO p radius Bnd Mg Tfixed H K hH hK0 Profile hK
  have hLinearFinite : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hGiven 0) (actualOriginalGivenInputProfile_linear_le Data 0 ell)
  have hLinearBound : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ Packet 0 :=
    (ENNReal.toReal_mono (hGiven 0) (actualOriginalGivenInputProfile_linear_le Data 0 ell)).trans (hPacket 0)
  have hRawBase := incrementsCompletion_at_scale_finite_germ_common_raw Data hd hs hn hp g V0 hV0 hKV0 hImm
    ell c cT hell hell1 hEll hcT hLinear hDecomp rho hReserve (Packet 0) hLinearFinite hLinearBound
    q Rsub Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket prep
  have hRawTarget := hRawBase.2 H hH
  have hRawPair := hRawTarget ⟨K,hK0⟩ ⟨K,hK0⟩
  obtain ⟨G,hG,hGR,hKG,hGV,coverG,hRaw⟩ := hRawPair
  refine ⟨{
    domain := G
    domain_open := hG
    original_region := hGR
    original_parameters := hKG
    prepared_parameters := hGV
    parameter_cover := coverG
    raw := ?_ }⟩
  intro s
  have hRawAt := hRaw tau htau htaul s (Profile (s+(q+4))) (hK _) (hK _)
  have hDiff : p (s+(q+4)) (K-K) = 0 := by
    rw [sub_self]
    exact (p (s+(q+4))).map_zero'
  change IncrementsCompletionAtScaleMeanRawProfiles Data hd hs hn g V0 cT Tinv Forward Meta Rsub ell prep
    G hG K.val.val K.val.val (s+(q+4)) q s (rho/4)
    (Bnd s (Profile (s+(q+4)))) (Mg s) Tfixed tau ell
    (parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Tinv *
      p (s+(q+4)) (K-K)) at hRawAt
  rw [hDiff,mul_zero] at hRawAt
  exact incrementsCompletion_at_scale_canonical_raw_physical_atlas Data hd hs hn g hTarget V0 cT Tinv Forward Meta
    Rsub ell prep G hG K.val.val K.val.val (s+(q+4)) q s (rho/4)
    (Bnd s (Profile (s+(q+4)))) (Mg s) Tfixed tau ell 0 hRawAt

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_at_scale_final_primary_atlas
