import Repair.FullIncrementNovOpenRawAtlas
import Smoothing.Round3ParameterMeanReserveSupply

/-! The actual open-parameter raw producer satisfies the existing global
finite-iteration interface for the internal source-slice model.  This is a
construction from original inputs and the actual prepared family; no computed
mean estimate, extension smoothness assumption, K = univ or global equality
between the auxiliary and original base maps is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
variable {Β : Type*} [Fintype Β]

theorem fullIncrementNov_original_open_legacy_mean_supply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (V0 : Set P) (hV0 : IsOpen V0) (hKV0 : Data.parameterSet ⊆ V0)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (ell c cT : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c) (hcT : 0 < cT)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (ML : ℝ) (hProfile : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ ML)
    (q Rsub : ℕ) (Packet Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (hGiven : ∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤)
    (hPacket : ∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n)
    (prep : ∀ i, FullIncrementNovOpenNativeMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub i) :
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W0 := incrementsOriginalParameterRegion Data
    let p := parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S W0 hS
      (fun _ _ hy => hy.1) ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1))
    let Bnd := fun s R => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) R Tinv
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) Tinv
    let Dinput := fun s => parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    0 < radius ∧ ∀ H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0,
      H.val = Data.H → Round3ParameterMeanRawReserveSupply (Tr := ℝ) Data.atlas Data.parameterChart
        S W0 p H radius q Rsub Data.primaryCount (rho/4) Bnd Mg Dinput Tfixed
        (fullIncrementNovOriginalSourceSlice Data) (fullIncrementNov_original_source_slice_smooth Data hd hs)
        (fullIncrementNovOriginalOpenFamily Data g hTarget) Data.primaryDomain ell := by
  intro S W0 p radius Bnd Mg Dinput Tfixed
  have h := fullIncrementNov_original_open_mean_raw_supply Data hd hs hn hp g V0 hV0 hKV0 hImm
    ell c cT hell hell1 hEll hcT hLinear hDecomp rho hReserve hS ML hProfile hML
    q Rsub Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket prep
  refine ⟨h.1,?_⟩
  intro H hH epsilon he he1 s R K L hK hL
  obtain ⟨G,hG,hGR,hKG,hraw⟩ := h.2 H hH (epsilon*ell) (mul_pos he hell)
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hell.le) s R K L hK hL
  refine ⟨G,hG,hGR,?_,?_⟩
  · intro i y hy
    exact hKG ⟨hy.2.2.2,mem_univ _⟩
  · exact fullIncrementNov_open_raw_physical_atlas Data hd hs hn g hTarget V0 cT Tinv Forward Meta Rsub prep
      G hG K.val.val L.val.val (s+(q+4)) q s (rho/4) (Bnd s R) (Mg s) Tfixed (epsilon*ell) ell
      (Dinput s*p (s+(q+4)) (K.val-L.val)) hraw

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_open_legacy_mean_supply
