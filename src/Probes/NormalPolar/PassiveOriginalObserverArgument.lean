import NormalPolar.PassiveOriginalObserverCoordinates

/-! The actual original linear tensor argument in an additional spatial
observer. The unchanged original tensor norm supplies its jets; the real
coordinate transition and all its constants are constructed from the fixed
compact geometric sample. No observer argument budget is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem passiveOriginal_observer_argument_germ_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ maximalAtlas IM ∞ M)
    (R : Set X) (hR : IsCompact R)
    (hRO : R ⊆ passiveOriginalObserverDomain (Data.parameterChart i.2) (Data.atlas.chart i.1) host)
    (hSample : MapsTo (passiveOriginalObserverCoordinates (Data.atlas.chart i.1) host) R
      (incrementsOriginalPrimaryEvaluation Data nu i)) :
    ∃ T : ℕ → ℝ, (∀ k, 0 ≤ T k) ∧
    ∀ (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (hInput : ∀ a, ∃ UI : Set (Fin (m+1+d) → ℝ), IsOpen UI ∧
        incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet a ⊆ UI ∧
        ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart input a) UI)
      (hSymm : ∀ p ∈ Data.parameterOpen, ∀ x, (input p x).IsSymm)
      (j : ℕ) (ell ML MA : ℝ), 0 < ell → ell ≤ 1 →
      incrementsOriginalInputProfileWithLinear Data j ell ≠ ⊤ →
      (incrementsOriginalInputProfileWithLinear Data j ell).toReal ≤ ML →
      paperAtlasWeighted 0 j ell
        (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart input)
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet) ≠ ⊤ →
      (paperAtlasWeighted 0 j ell
        (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart input)
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet)).toReal ≤ MA →
    let C := actualFastChartTransferPrefix T j * coordinateDimensionFactor (m+1+d) j
    let arg := fun z : X => Data.linearArgument nu ((Data.parameterChart i.2).symm z.1)
      (host.symm z.2) (input ((Data.parameterChart i.2).symm z.1) (host.symm z.2))
    ∃ V0 : Set X, IsOpen V0 ∧ R ⊆ V0 ∧
      V0 ⊆ passiveOriginalObserverDomain (Data.parameterChart i.2) (Data.atlas.chart i.1) host ∧
      ContDiffOn ℝ ∞ arg V0 ∧
      ∀ k ≤ j, ∀ z ∈ R, ell^k*‖iteratedFDeriv ℝ k arg z‖ ≤
        2^j*(‖actualOriginalCoefficientFunctional (m+1)‖*C*ML)*(C*MA) := by
  let phi := passiveOriginalObserverCoordinates (d := d) (Data.atlas.chart i.1) host
  let O := passiveOriginalObserverDomain (Data.parameterChart i.2) (Data.atlas.chart i.1) host
  have hO : IsOpen O := passiveOriginalObserverDomain_open _ _ _
  have hphi : ContDiffOn ℝ ∞ phi O := passiveOriginalObserverCoordinates_smooth _ _ _
    (hd.atlas_smooth.chart_mem i.1) hhost
  obtain ⟨T,hT,hTbound⟩ := passiveOriginalObserverCoordinates_compact_profiles
    (Data.parameterChart i.2) (Data.atlas.chart i.1) host
    (hd.atlas_smooth.chart_mem i.1) hhost R hR hRO
  refine ⟨T,hT,?_⟩
  intro input hInput hSymm j ell ML MA hell hell1 hProfile hML hInputFinite hMA C arg
  let U := incrementsOriginalPrimaryDifferentiation Data nu i ∩
    (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) ⁻¹'
      incrementsOriginalParameterRegion Data
  have hU : IsOpen U :=
    ((actual_original_jointPoint_continuousOn Data i).mono inter_subset_left).isOpen_inter_preimage
      (actual_original_primaryDifferentiation_open Data hd.primary_open nu i)
      (hd.parameter_open.prod isOpen_univ)
  let V := O ∩ phi ⁻¹' U
  have hV : IsOpen V := hphi.continuousOn.isOpen_inter_preimage hO hU
  have hRV : R ⊆ V := by
    intro z hz
    have hs := hSample hz
    exact ⟨hRO hz,⟨hs.1.1,hs.2⟩,hd.parameter_subset hs.1.2.2.2,mem_univ _⟩
  obtain ⟨V0,hV0,hRV0,hV0V,hreg,hbound⟩ := parameterRound2_original_argument_germ_profiles
    Data hd hLinear input hInput hSymm j T hT ell hell ML MA hProfile hML hInputFinite hMA
    nu i phi V R hV hRV (hphi.mono inter_subset_left) (fun z hz => hz.2) hSample
    (fun z hz k _ _ => hTbound ell hell.le hell1 k z hz)
  let origArg := fun z => Data.linearArgument nu
    (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (phi z)).1
    (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (phi z)).2
    (input (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (phi z)).1
      (incrementsOriginalJointPoint Data.atlas Data.parameterChart i (phi z)).2)
  have heq : EqOn arg origArg O := by
    intro z hz
    dsimp only [origArg,phi]
    rw [passiveOriginalObserverCoordinates_point Data.atlas Data.parameterChart i host z hz]
  refine ⟨V0,hV0,hRV0,fun z hz => (hV0V hz).1,
    hreg.congr (fun z hz => heq (hV0V hz).1),?_⟩
  intro k hk z hz
  have he : arg =ᶠ[nhds z] origArg := by
    filter_upwards [hO.mem_nhds (hRO hz)] with w hw
    exact heq hw
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hbound k hk z hz

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_observer_argument_germ_profiles
