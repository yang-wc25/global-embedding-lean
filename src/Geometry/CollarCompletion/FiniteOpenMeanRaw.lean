import CollarCompletion.FiniteOpenMeanRawNative
import CollarCompletion.FiniteReserveBall

/-!
# Actual common raw mean profiles on finite original norm domains

This is the existing original-input producer with only the internal germ
carrier restricted to tensors whose unchanged original norms are finite.
The actual reserve neighborhood and every raw coefficient, geometric field,
cutoff and profile are still manufactured by the original constructors.
No compactness of the original norm domains is assumed. The common G is
selected before all scales and observation orders for each input pair.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter Bundle
open scoped ContDiff ENNReal Topology BigOperators TensorProduct
namespace GlobalEmbedding.Continuation.CollarCompletion
open SourceCollarsBridge

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

theorem original_finite_germ_open_mean_common_raw
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
    let p := finiteTensorGermSeminorm Data.atlas Data.parameterChart S W0
      (fun _ _ hy => hy.1) ell
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1))
    let Bnd := fun s R => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) R Tinv
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT (1+Forward (s+(q+4))) Tinv
    let Dinput := fun s => parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    0 < radius ∧ ∀ H : finiteTensorGermSpace Data.atlas Data.parameterChart S W0 (fun _ _ hy => hy.1),
      H.val.val = Data.H → ∀
      (K L : {K : finiteTensorGermSpace Data.atlas Data.parameterChart S W0 (fun _ _ hy => hy.1) // p 0 (K-H) < radius}),
      ∃ G : Set (P × M), ∃ hG : IsOpen G,
        G ⊆ W0 ∧ Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧
        G ⊆ V0 ×ˢ (univ : Set M) ∧
        (∀ z ∈ G, ∃ ip, z.1 ∈ (Data.parameterChart ip).source) ∧
        ∀ tau, 0 < tau → tau ≤ ell → ∀ s R,
        p (s+(q+4)) K.val ≤ R → p (s+(q+4)) L.val ≤ R →
        FullIncrementNovOpenNativeMeanRawProfiles Data hd hs hn g V0 cT Tinv Forward Meta Rsub prep
          G hG K.val.val.val L.val.val.val (s+(q+4)) q s (rho/4) (Bnd s R) (Mg s) Tfixed tau ell
          (Dinput s*p (s+(q+4)) (K.val-L.val)) := by
  intro S W0 p radius Bnd Mg Dinput Tfixed
  have hBase := original_finite_germ_reserve_ball (J := Bool) Data hd hLinear hDecomp
    rho hReserve ell ML hProfile hML
  refine ⟨hBase.1,?_⟩
  intro H hH K L
  let elems : Bool → finiteTensorGermSpace Data.atlas Data.parameterChart S W0 (fun _ _ hy => hy.1) :=
    fun a => if a then K.val else L.val
  let input := fun a : Bool => (elems a).val.val
  have hclose : ∀ a, p 0 (elems a-H) < radius := by
    intro a
    cases a
    · exact L.property
    · exact K.property
  have hgeometry := hBase.2 H hH elems hclose
  obtain ⟨G0,hG0,hKG0,hGR0,hpos0,hdec0,harg0⟩ := hgeometry
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
    (elems a).val.property.1
  have hInputFin (a) : paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ :=
    finiteTensorGerm_weighted_finite Data.atlas Data.parameterChart S W0 (fun _ _ hz => hz.1) (elems a) 0 n ell
  have hInputBound (a) : (paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (input a))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ max 0 R := by
    cases a
    · exact hL.trans (le_max_right _ _)
    · exact hK.trans (le_max_right _ _)
  have hDiffFin : paperAtlasWeighted 0 n ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart (fun p x => input true p x-input false p x))
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≠ ⊤ :=
    finiteTensorGerm_weighted_finite Data.atlas Data.parameterChart S W0 (fun _ _ hz => hz.1) (K.val-L.val) 0 n ell
  have hRaw := finite_input_raw_on_common_neighborhood Data hd hs hn hp g V0 hV0
    hImm ell c cT hell hell1 hEll hcT hLinear rho hReserve.reserve_pos q Rsub
    Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket prep G hG hGR hKG
    (fun z hz => ⟨hz.2.1.1,hz.2.2⟩) input
    (fun a p hp x => (elems a).val.property.2 (p,x) ⟨hp,mem_univ _⟩)
    harg hdec hpos tau htau htaul s R (p n (K.val-L.val)) (apply_nonneg _ _)
    hInput hInputFin hInputBound hDiffFin le_rfl
  exact hRaw

end GlobalEmbedding.Continuation.CollarCompletion
#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_finite_germ_open_mean_common_raw
