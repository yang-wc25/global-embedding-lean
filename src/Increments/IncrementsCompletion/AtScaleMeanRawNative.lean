import IncrementsCompletion.AtScaleMeanRawType
import CollarCompletion.FiniteOpenMeanRawNative

/-! Genuine raw primitives from the current-scale refinement. Every coefficient,
geometry, reserve and unchanged sample follows the existing producer. The only
removed intermediate requirement is refinement at unused scales. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter Bundle
open scoped ContDiff ENNReal Topology BigOperators TensorProduct
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)
variable {Β : Type*} [Fintype Β]

local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

/-- Internal native producer on a previously constructed common reserve
neighborhood. Its local analytic premises are discharged by the finite carrier
in `original_finite_germ_open_mean_common_raw`. -/
theorem incrementsCompletion_at_scale_input_raw_on_common_neighborhood
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (V0 : Set P) (hV0 : IsOpen V0)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (ell c cT : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c) (hcT : 0 < cT)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (rho : ℝ) (hrho : 0 < rho)
    (q Rsub : ℕ) (Packet Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (hGiven : ∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤)
    (hPacket : ∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n)
    (prep : ∀ i, IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub ell i)
    (G : Set (P × M)) (hG : IsOpen G)
    (hGR : G ⊆ incrementsOriginalParameterRegion Data)
    (hKG : Data.parameterSet ×ˢ (univ : Set M) ⊆ G)
    (hGV : G ⊆ V0 ×ˢ (univ : Set M))
    (input : Bool → (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (hSymm : ∀ a p, p ∈ Data.parameterOpen → ∀ x, (input a p x).IsSymm)
    (harg : ∀ a nu, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (fun z : P × M => Data.linearArgument nu z.1 z.2 (input a z.1 z.2)) (G ∩ Data.primaryDomain nu))
    (hdec : ∀ a z, z ∈ G → input a z.1 z.2 =
      incrementsOriginalDecompositionTensor Data z.1 z.2 (input a z.1 z.2))
    (hpos : ∀ a nu z, z ∈ G → z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
      rho/4 < Data.linearArgument nu z.1 z.2 (input a z.1 z.2))
    (tau : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (s : ℕ) (R Delta : ℝ) (hDelta : 0 ≤ Delta) :
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let n := s+(q+4)
    let Bnd := parameterRound2_identityRawBnd m d N n (Packet n)
      c cT (1+Forward n) (Meta n) R Tinv
    let Mg := parameterRound2_identityRawMg m d N n (Packet n) c cT (1+Forward n) Tinv
    let Dinput := parameterRound2_identityRawDinput m d n (Packet n) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    (∀ a i, ∃ U : Set (Fin (m+1+d) → ℝ), IsOpen U ∧ S i ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a) i) U) →
    (∀ a, paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤) →
    (∀ a, (paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ max 0 R) →
    paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input true p x-input false p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ →
    (paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input true p x-input false p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ Delta →
    IncrementsCompletionAtScaleMeanRawProfiles Data hd hs hn g V0 cT Tinv Forward Meta Rsub ell prep
      G hG (input true) (input false) n q s (rho/4) Bnd Mg Tfixed tau ell (Dinput*Delta) := by
  intro S n Bnd Mg Dinput Tfixed hInput hInputFin hInputBound hDiffFin hDiffBound
  have hCore : incrementsOriginalCoreInputProfile Data 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hGiven 0) (actualOriginalGivenInputProfile_core_le Data 0 ell)
  intro i
  let z := prep i
  let eta := (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta
  let F := actualOriginalOpenParameterSlice Data i
  let hFn := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
  let g0 := actualOriginalPrimaryFamily Data hd hs hn i z.host z.native z.slices z.data eta z.active
  let W := actualOriginalParameterNeighborhood Data i.2 G
  let hW := actualOriginalParameterNeighborhood_isOpen Data i.2 G hG
  let gN := parameterRound2_restrictPrimaryFamily F g0 W hW
  have ctrl := round3Parameter_refinement_samples_restrict Data i.2 F g0 z.host z.native
    (actualOriginalParameterNeighborhood Data i.2 (V0 ×ˢ (univ : Set M))) W
    (actualOriginalParameterNeighborhood_isOpen Data i.2 _ (hV0.prod isOpen_univ))
    hW (fun _ hz => ⟨hz.1,hGV hz.2⟩)
    ell Tinv Forward Meta Rsub Data.primaryCount z.refinement
  have hBn : 0 < 1+Forward n := by linarith [hForward n]
  have hprim (a) : ParameterRound2GlobalMeanPrimitives F hFn gN
      (actualOriginalParameterTensorSlice Data i (input a)) W
      (fun nu => W ∩ (fun w : Ep × M => ((Data.parameterChart i.2).symm w.1,w.2)) ⁻¹' Data.primaryDomain nu) :=
    round3Parameter_original_active_mean_primitives Data hd hs hn hp i z.host z.native z.slices z.data
      eta z.active hImm z.native_open ell c cT (1+Forward n) hell hell1 hEll hcT hBn hCore
      z.transverse G hG hGR (input a) (harg a)
      (fun nu w hw hrel => (div_pos hrho (by norm_num : (0:ℝ)<4)).trans (hpos a nu w hw hrel))
      (fun z hz => hSymm a z.1 (hGR hz).1 z.2) (hdec a) ctrl.eta_smooth ctrl.eta_support ctrl.partition
  have raw := round3Parameter_original_active_raw_profiles_from_primitives Data hd hs hn i
    z.host z.native z.slices z.data eta z.active hImm z.native_open G hG hGR
    hKG input hInput
    hSymm hLinear
    n (q+2) s Rsub Data.primaryCount (by dsimp [n]; omega)
    ell tau (Packet n) (max 0 R) Delta (rho/4) c cT
    (1+Forward n) (Forward n) (Meta n) hell hell1 htau
    htaul
    hDelta (div_pos hrho (by norm_num : (0:ℝ)<4)) (hMeta n) (hForward n)
    (hGiven n) (hPacket n) hInputFin hInputBound hDiffFin hDiffBound
    (fun a nu w hw hrel => (hpos a nu w hw hrel).le) hEll hcT hBn (by linarith)
    z.transverse Tinv hTinv i.1 hprim
    (ctrl.sample_inverse i.1)
    (fun nu a k hk _ => ctrl.inverse_jets i.1 nu a k hk)
    (fun nu a k hk hkn => ctrl.forward_jets n i.1 nu a k hk hkn)
    (fun nu a k hkn => ctrl.eta_jets n i.1 nu a k hkn)
    ctrl.eta_count ctrl.primary_count
  let Told := fun k => actualFastChartTransferCost
    (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d n*Packet n) k*Forward n
  have hFixed := actualOriginalPrimaryFamily_raw_profiles_fixed_transition Data hd hs hn i
    z.host z.native z.slices z.data eta z.active G hG i.1 n (q+2) s Rsub Data.primaryCount
    (rho/4) Bnd Mg Told ell tau (Dinput*Delta) hell
    Packet Forward hForward hGiven hPacket
    (actualOriginalParameterTensorSlice Data i (input true)) (actualOriginalParameterTensorSlice Data i (input false))
    (fun r nu a k hk hkr => ctrl.forward_jets r i.1 nu a k hk hkr) (Classical.choice raw.2.2.2)
  have hT : Tfixed = fun k => actualFastChartTransferCost
      (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d k*Packet k) k*Forward k := rfl
  have hPair : (i.1,i.2) = i := rfl
  simpa only [hT,g0,hPair] using hFixed.2


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_at_scale_input_raw_on_common_neighborhood
