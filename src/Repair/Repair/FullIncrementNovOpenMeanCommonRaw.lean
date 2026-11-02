import Repair.FullIncrementNovOpenMeanRawSupply

/-! A single genuine final neighborhood for a fixed input pair, before every
scale and every derivative order. The reserve-ball construction is performed
once. Intersecting with the actual original-chart cover retains the entire
original parameter set and supplies precisely the cover needed by joint
smoothness. All raw profiles use that same G, original fields and norms. -/

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

theorem fullIncrementNov_original_open_mean_common_raw_supply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
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
      H.val = Data.H → ∀
      (K L : {K : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0 // p 0 (K-H) < radius}),
      ∃ G : Set (P × M), ∃ hG : IsOpen G,
        G ⊆ W0 ∧ Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧
        G ⊆ V0 ×ˢ (univ : Set M) ∧
        (∀ z ∈ G, ∃ ip, z.1 ∈ (Data.parameterChart ip).source) ∧
        ∀ tau, 0 < tau → tau ≤ ell → ∀ s R,
        p (s+(q+4)) K.val ≤ R → p (s+(q+4)) L.val ≤ R →
        FullIncrementNovOpenNativeMeanRawProfiles Data hd hs hn g V0 cT Tinv Forward Meta Rsub prep
          G hG K.val.val L.val.val (s+(q+4)) q s (rho/4) (Bnd s R) (Mg s) Tfixed tau ell
          (Dinput s*p (s+(q+4)) (K.val-L.val)) := by
  intro S W0 p radius Bnd Mg Dinput Tfixed
  have hBase := parameterRound2_original_germ_reserve_ball (J := Bool) Data hd hLinear hDecomp
    rho hReserve hS ell ML hProfile hML
  have hCore : incrementsOriginalCoreInputProfile Data 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hGiven 0) (actualOriginalGivenInputProfile_core_le Data 0 ell)
  refine ⟨hBase.1,?_⟩
  intro H hH K L
  let elems : Bool → parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0 :=
    fun a => if a then K.val else L.val
  let input := fun a : Bool => (elems a).val
  have hclose : ∀ a, p 0 (elems a-H) < radius := by
    intro a
    cases a
    · exact L.property
    · exact K.property
  obtain ⟨G0,hG0,hKG0,hGR0,hpos0,hdec0,harg0⟩ := hBase.2 H hH elems hclose
  let C : Set P := ⋃ ip, (Data.parameterChart ip).source
  have hC : IsOpen C := isOpen_iUnion (fun ip => (Data.parameterChart ip).open_source)
  have hKC : Data.parameterSet ⊆ C := by
    intro p hp
    obtain ⟨ip,hip,_⟩ := hd.parameter_cover p hp
    exact mem_iUnion.mpr ⟨ip,hip⟩
  let G := G0 ∩ ((V0 ∩ C) ×ˢ (univ : Set M))
  have hG : IsOpen G := hG0.inter ((hV0.inter hC).prod isOpen_univ)
  have hKG : Data.parameterSet ×ˢ (univ : Set M) ⊆ G :=
    fun z hz => ⟨hKG0 hz,⟨hKV0 hz.1,hKC hz.1⟩,mem_univ _⟩
  have hGR : G ⊆ incrementsOriginalParameterRegion Data := fun _ hz => hGR0 hz.1
  have hpos (a nu z) (hz : z ∈ G) (hrel : z ∈ incrementsOriginalRelativeCutoffSupport Data nu) :
      rho/4 < Data.linearArgument nu z.1 z.2 (input a z.1 z.2) := hpos0 a nu z hz.1 hrel
  have hdec (a z) (hz : z ∈ G) : input a z.1 z.2 =
      incrementsOriginalDecompositionTensor Data z.1 z.2 (input a z.1 z.2) := hdec0 a z hz.1
  have harg (a nu) : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (fun z : P × M => Data.linearArgument nu z.1 z.2 (input a z.1 z.2)) (G ∩ Data.primaryDomain nu) :=
    (harg0 a nu).mono (fun _ hz => ⟨hz.1.1,hz.2⟩)
  refine ⟨G,hG,hGR,hKG,(fun z hz => ⟨hz.2.1.1,hz.2.2⟩),
    (fun z hz => mem_iUnion.mp hz.2.1.2),?_⟩
  intro tau htau htaul s R hK hL
  let n := s+(q+4)
  have hInput (a) : ∀ i, ∃ U : Set (Fin (m+1+d) → ℝ), IsOpen U ∧ S i ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a) i) U :=
    (elems a).property.1
  have hSymm : ∀ a z, z ∈ G → (input a z.1 z.2).IsSymm :=
    fun a z hz => (elems a).property.2 z (hGR hz)
  have hInputFin (a) : paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ :=
    parameterRound2_tensorGerm_weighted_finite Data.atlas Data.parameterChart S W0
      hS (fun _ _ hz => hz.1) (elems a) 0 n ell
  have hInputBound (a) : (paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ max 0 R := by
    cases a
    · exact hL.trans (le_max_right _ _)
    · exact hK.trans (le_max_right _ _)
  have hDiffFin : paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input true p x-input false p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ :=
    parameterRound2_tensorGerm_weighted_finite Data.atlas Data.parameterChart S W0
      hS (fun _ _ hz => hz.1) (K.val-L.val) 0 n ell
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
    hW (fun _ hz => ⟨hz.1,hz.2.2.1.1,hz.2.2.2⟩)
    ell Tinv Forward Meta Rsub Data.primaryCount (z.refinement ell hell.le hell1)
  have hBn : 0 < 1+Forward n := by linarith [hForward n]
  have hprim (a) : ParameterRound2GlobalMeanPrimitives F hFn gN
      (actualOriginalParameterTensorSlice Data i (input a)) W
      (fun nu => W ∩ (fun w : Ep × M => ((Data.parameterChart i.2).symm w.1,w.2)) ⁻¹' Data.primaryDomain nu) :=
    round3Parameter_original_active_mean_primitives Data hd hs hn hp i z.host z.native z.slices z.data
      eta z.active hImm z.native_open ell c cT (1+Forward n) hell hell1 hEll hcT hBn hCore
      z.transverse G hG hGR (input a) (harg a)
      (fun nu w hw hrel => (div_pos hReserve.reserve_pos (by norm_num : (0:ℝ)<4)).trans (hpos a nu w hw hrel))
      (hSymm a) (hdec a) ctrl.eta_smooth ctrl.eta_support ctrl.partition
  have raw := round3Parameter_original_active_raw_profiles_from_primitives Data hd hs hn i
    z.host z.native z.slices z.data eta z.active hImm z.native_open G hG hGR
    hKG input hInput
    (fun a p hp x => (elems a).property.2 (p,x) ⟨hp,mem_univ _⟩) hLinear
    n (q+2) s Rsub Data.primaryCount (by dsimp [n]; omega)
    ell tau (Packet n) (max 0 R) (p n (K.val-L.val)) (rho/4) c cT
    (1+Forward n) (Forward n) (Meta n) hell hell1 htau
    htaul
    (apply_nonneg _ _) (div_pos hReserve.reserve_pos (by norm_num : (0:ℝ)<4)) (hMeta n) (hForward n)
    (hGiven n) (hPacket n) hInputFin hInputBound hDiffFin le_rfl
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
    (rho/4) (Bnd s R) (Mg s) Told ell tau (Dinput s*p n (K.val-L.val)) hell
    Packet Forward hForward hGiven hPacket
    (actualOriginalParameterTensorSlice Data i (input true)) (actualOriginalParameterTensorSlice Data i (input false))
    (fun r nu a k hk hkr => ctrl.forward_jets r i.1 nu a k hk hkr) (Classical.choice raw.2.2.2)
  have hT : Tfixed = fun k => actualFastChartTransferCost
      (fun _ => actualOriginalNativeGivenTransitionJetCost (m+1) d k*Packet k) k*Forward k := rfl
  have hPair : (i.1,i.2) = i := rfl
  simpa only [input,elems,Bool.false_eq_true,ite_false,ite_true,hT,g0,hPair] using hFixed.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_open_mean_common_raw_supply
