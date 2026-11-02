import Probes.Round3ParameterSecondarySigmaPadding
import Probes.Round4ParameterSecondaryDependentFactory
import Probes.Round3PreparedParameterSecondaryFamilyTransport
import Probes.Round3ParameterNativeFamily

/-! The actual nonempty-atlas branch of the coherent whole-parameter
secondary factory. One physical sigma choice is used in every observer.
Original open slices are transported to their literal canonical pullbacks;
the primary physical geometry is the actual geometry supplied by the mean
preparation. All secondary numerical costs are fixed before the current map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance signedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

 theorem round4Parameter_secondary_canonical_actual_factory
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref) (hsRef : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hdRef hsRef theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
    (hPart : ∀ z, ∑ i, theta i z = 1) (L : ℕ)
    (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ L)
    (q : ℕ) (c : ℝ) (InputBudget Tinv Kcut Tobs : ℕ → ℝ) :
    let Sub := fun r => Sigma (fun i : Fin Ref.atlas.count × Fin Ref.parameterCount => ↥(packet.s r i))
    letI : ∀ r, Fintype (Sub r) := fun r => inferInstance
    ∃ Mrest Cut : ℕ → ℝ,
      (∀ j, Mrest j = round4ParameterSecondaryGeometryProfile m d N q
        (fun a : Sigma Sub => (packet.piece a.1 a.2.1 a.2.2).cT/16)
        InputBudget Tinv Tobs c j) ∧
      (∀ j, 0 ≤ Mrest j) ∧ (∀ j, Cut j = Kcut (actualSecondarySolveOrder q j)) ∧
    ∀ Mnew : ℕ → ℝ, (∀ j, Mrest j ≤ Mnew j) →
    ∀ (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
      (hJoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
      (stable : ∀ r i (a : packet.s r i), Round3PreparedParameterStableSecondaryPiece Ref hdRef hsRef i r _ (packet.piece r i a) F hF)
      (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
      (domain : Fin Ref.primaryCount → Set (P × M))
      (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
    let Data := round3ParameterStageData Ref (Function.uncurry F) H V normal domain neighborhood
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
      (spatialBase : Fin Ref.atlas.count),
    (∀ r i (a : packet.s r i) observer,
      ∃ out : Round3PreparedParameterRawPiece Data hd hs (i.1,observer) r
        ((Ref.parameterChart observer).target ×ˢ (univ : Set M))
        (fun v : Fin Ref.atlas.count => Ref.atlas.chart v)
        (fun v => (parameterTensorModelEquiv (m+1) d) ⁻¹'
          incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet (v,observer)),
        out.choice = ((round3PreparedParameterSecondaryChoice Ref hdRef hsRef i r _ (stable r i a).piece).pullback
          (Ref.parameterChart observer)).toNative ∧
        out.Tinv = Tinv ∧ out.Kcut = Kcut ∧ out.Tobs = Tobs ∧
        out.cT = (packet.piece r i a).cT/16 ∧ out.Bnative = 1+Tobs 1) →
    ∀ ell, 0 < ell → ell ≤ 1 → IncrementsOriginalCoordinateEllipticityInputs Data c →
    (∀ n, incrementsOriginalCoreInputProfile Data n ell ≠ ⊤) →
    (∀ n, (incrementsOriginalCoreInputProfile Data n ell).toReal ≤ InputBudget n) →
    ∀ (Β : Type*) [Fintype Β]
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
        (Λ := Fin Ref.primaryCount) (Β := Β) F),
    (∀ nu, g.phase nu = Ref.phase nu) → (∀ nu, g.cutoff nu = Ref.cutoff nu) →
    (∀ ip, Nonempty (ActualOriginalPrimaryPhysicalGeometry
      (fun p => F ((Ref.parameterChart ip).symm p)) (fun p => hF ((Ref.parameterChart ip).symm p))
      (round3ParameterNativePrimary F g (Ref.parameterChart ip)))) →
    let physical := fun r (a : Sub r) => round3PreparedParameterSecondaryChoice Ref hdRef hsRef a.1 r _ (stable r a.1 a.2).piece
    let choice := round3ParameterSecondarySigmaChoice Sub (fun _ => Ref.atlas.chart spatialBase) physical
    ∃ family : ∀ ip : Fin Ref.parameterCount,
      Round3ParameterPreparedSecondaryFamily (SubSecondary := Sigma Sub) Data
        (fun p => F ((Ref.parameterChart ip).symm p)) (fun p => hF ((Ref.parameterChart ip).symm p))
        (round3ParameterNativePrimary F g (Ref.parameterChart ip)) q ell
        ((Ref.parameterChart ip).target ×ˢ (univ : Set M)) ((Ref.parameterChart ip).target ×ˢ (univ : Set M))
        Mnew Cut Tinv Tobs (L*5^Module.finrank ℝ (Ep × D)) (round3ParameterOriginalNativeSamplesAt Data ip),
      ∀ ip, (family ip).choice = round3ParameterNativeChoices choice (Ref.parameterChart ip) := by
  intro Sub
  letI : ∀ r, Fintype (Sub r) := fun r => inferInstance
  letI : Fintype (Sigma Sub) := inferInstance
  obtain ⟨Mrest,Cut,hMrestExact,hMrest,hCut,hMake⟩ := round4Parameter_secondary_dependent_actual_factory
    Ref hdRef hsRef theta packet hSupport hPart L hCount q c InputBudget Tinv Kcut Tobs
  refine ⟨Mrest,Cut,hMrestExact,hMrest,hCut,?_⟩
  intro Mnew hMnew F hF hJoint stable H V normal domain neighborhood Data hd hs spatialBase hRaw
    ell hell hell1 hEll hFinite hBudget Β _ g hPhase hCutoff hPhysical physical choice
  have hOne (ip : Fin Ref.parameterCount) :
      ∃ family : Round3ParameterPreparedSecondaryFamily (SubSecondary := Sigma Sub) Data
        (fun p => F ((Ref.parameterChart ip).symm p)) (fun p => hF ((Ref.parameterChart ip).symm p))
        (round3ParameterNativePrimary F g (Ref.parameterChart ip)) q ell
        ((Ref.parameterChart ip).target ×ˢ (univ : Set M)) ((Ref.parameterChart ip).target ×ˢ (univ : Set M))
        Mnew Cut Tinv Tobs (L*5^Module.finrank ℝ (Ep × D)) (round3ParameterOriginalNativeSamplesAt Data ip),
        family.choice = round3ParameterNativeChoices choice (Ref.parameterChart ip) := by
    let i : Fin Ref.atlas.count × Fin Ref.parameterCount := (spatialBase,ip)
    let B := Ref.parameterChart ip
    let Fn := fun p => F (B.symm p)
    let hFn := fun p => hF (B.symm p)
    let Fopen := actualOriginalOpenParameterSlice Data i
    let hFopen := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let W := B.target ×ˢ (univ : Set M)
    let gN := round3ParameterNativePrimary F g B
    have hMap : Fopen = Fn := round3Parameter_original_open_slice_eq_global Data hd hAll i
    let gOpen := round3PreparedPrimaryAtMap Data Fopen Fn hMap gN
    have hFields := round3_prepared_primary_at_map_fields Data Fopen Fn hMap gN
    obtain ⟨geometry⟩ := hPhysical ip
    let geomOpen := round3PreparedPrimaryPhysicalAtMap Data Fopen Fn hMap hFopen hFn gN geometry
    have hPhaseOpen (nu) : gOpen.phase nu = fun z : Ep × M => Ref.phase nu (B.symm z.1,z.2) := by
      change (round3PreparedPrimaryAtMap Data Fopen Fn hMap gN).phase nu = _
      rw [hFields.2.1]
      funext z
      exact congrFun (hPhase nu) (B.symm z.1,z.2)
    have hCutoffOpen (nu) : gOpen.cutoff nu = fun z : Ep × M => Ref.cutoff nu (B.symm z.1,z.2) := by
      change (round3PreparedPrimaryAtMap Data Fopen Fn hMap gN).cutoff nu = _
      rw [hFields.2.2]
      funext z
      exact congrFun (hCutoff nu) (B.symm z.1,z.2)
    have hSmoothNative : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞
        (fun y : Ep × M => Fn y.1 y.2) W :=
      hJoint.comp_contMDiffOn (round3ParameterProductChart_symm_smooth B (hdRef.parameter_charts_smooth ip))
    have hOriginal : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞
        (fun y : Ep × M => Fopen y.1 y.2) W := by
      apply hSmoothNative.congr
      intro y hy
      exact congrFun (congrFun hMap y.1) y.2
    obtain ⟨dep,hDep⟩ := hMake Mnew hMnew F hF stable H V normal domain neighborhood hd hs i
      (fun r i a => hRaw r i a ip) ell hell hell1 hEll hFinite hBudget Β gOpen hPhaseOpen hCutoffOpen geomOpen hOriginal
    let common := round3Parameter_coherent_secondary_common_family Data hd Sub i Fopen hFopen gOpen q ell W W
      Mnew Cut Tinv Tobs (L*5^Module.finrank ℝ (Ep × D)) (round3ParameterOriginalNativeSamplesAt Data ip)
      B physical dep hDep
    have hCommon : common.choice = round3ParameterNativeChoices choice B := rfl
    obtain ⟨family,hFamily⟩ := round3_prepared_secondary_family_transport Data Fopen Fn hMap hFopen hFn
      gOpen gN hFields.1 q ell W W Mnew Cut Tinv Tobs (L*5^Module.finrank ℝ (Ep × D))
      (round3ParameterOriginalNativeSamplesAt Data ip) common
    exact ⟨family,hFamily.trans hCommon⟩
  choose family hFamily using hOne
  exact ⟨family,hFamily⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_secondary_canonical_actual_factory
