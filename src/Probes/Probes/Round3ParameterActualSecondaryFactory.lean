import Probes.Round3ParameterSecondaryDomainTransport
import Probes.Round3PreparedParameterCanonicalSecondaryFactory
import Probes.Round3ParameterSecondaryNoBaseChart
import Probes.Round3PreparedParameterDependentActualFactory
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

 theorem round3Parameter_actual_coherent_secondary_factory
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
    ∃ Mrest Cut : ℕ → ℝ, (∀ j, 0 ≤ Mrest j) ∧ (∀ j, Cut j = Kcut (actualSecondarySolveOrder q j)) ∧
    ∀ Mnew : ℕ → ℝ, (∀ j, Mrest j ≤ Mnew j) →
    ∀ (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
      (hJoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
      (stable : ∀ r i (a : packet.s r i), Round3PreparedParameterStableSecondaryPiece Ref hdRef hsRef i r _ (packet.piece r i a) F hF)
      (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
      (domain : Fin Ref.primaryCount → Set (P × M))
      (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
    let Data := round3ParameterStageData Ref (Function.uncurry F) H V normal domain neighborhood
    ∀ (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data),
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
    ∀ (Β : Type*) [Fintype Β] (primaryHost : Β → Fin Ref.atlas.count)
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
        (Λ := Fin Ref.primaryCount) (Β := Β) F),
    (∀ nu, g.phase nu = Ref.phase nu) → (∀ nu, g.cutoff nu = Ref.cutoff nu) →
    (∀ i : Fin Ref.atlas.count × Fin Ref.parameterCount, Nonempty (ActualOriginalPrimaryPhysicalGeometry
      (fun p => F ((Ref.parameterChart i.2).symm p)) (fun p => hF ((Ref.parameterChart i.2).symm p))
      (round3ParameterNativePrimary F g (Ref.parameterChart i.2)))) →
    Round3ParameterCoherentSecondaryOutput (SubSecondary := Sigma Sub) Data F hF g q ell univ
      Mnew Cut Tinv Tobs (L*5^Module.finrank ℝ (Ep × D))
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet) := by
  intro Sub
  letI : ∀ r, Fintype (Sub r) := fun r => inferInstance
  obtain ⟨Mrest,Cut,hMrest,hCut,hMake⟩ := round3_prepared_parameter_canonical_secondary_factory
    Ref hdRef hsRef hAll theta packet hSupport hPart L hCount q c InputBudget Tinv Kcut Tobs
  refine ⟨Mrest,Cut,hMrest,hCut,?_⟩
  intro Mnew hMnew F hF hJoint stable H V normal domain neighborhood Data hd hs hRaw
    ell hell hell1 hEll hFinite hBudget Β _ primaryHost g hPhase hCutoff hPhysical
  apply round3Parameter_secondary_factory_without_base_chart Data primaryHost
    (fun a : Sigma Sub => a.2.1.1) F hF g q ell univ Mnew Cut Tinv Tobs
    (L*5^Module.finrank ℝ (Ep × D))
    (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet)
  intro spatialBase
  let physical := fun r (a : Sub r) => round3PreparedParameterSecondaryChoice Ref hdRef hsRef a.1 r _ (stable r a.1 a.2).piece
  let choice := round3ParameterSecondarySigmaChoice Sub (fun _ => Ref.atlas.chart spatialBase) physical
  have hPreserves : ∀ r a, Round3ParameterChartPreserves (choice r a).chart := by
    intro r ⟨r',a⟩
    by_cases heq : r'=r
    · subst r'
      simpa only [choice,round3ParameterSecondarySigmaChoice,dite_true] using
        round3_prepared_parameter_secondary_preserves Ref hdRef hsRef a.1 r _ (stable r a.1 a.2).piece
    · simpa only [choice,round3ParameterSecondarySigmaChoice,heq,dite_false] using
        round3ParameterSecondaryEmptyChoice_preserves (P := P) (Ref.atlas.chart spatialBase)
  have hOne := hMake Mnew hMnew F hF hJoint stable H V normal domain neighborhood hd hs spatialBase hRaw
    ell hell hell1 hEll hFinite hBudget Β g hPhase hCutoff (fun ip => hPhysical (spatialBase,ip))
  obtain ⟨family,hChoice⟩ := hOne
  have hW (ip : Fin Ref.parameterCount) : round3ParameterNativeDomain (Ref.parameterChart ip)
      (univ : Set (P × M)) = (Ref.parameterChart ip).target ×ˢ (univ : Set M) := by
    ext z
    simp only [round3ParameterNativeDomain,mem_setOf_eq,mem_prod,mem_univ,and_true]
  refine ⟨choice,hPreserves,?_⟩
  change ∃ fam : ∀ ip : Fin Ref.parameterCount,
      Round3ParameterPreparedSecondaryFamily (SubSecondary := Sigma Sub) Data
        (fun p => F ((Ref.parameterChart ip).symm p)) (fun p => hF ((Ref.parameterChart ip).symm p))
        (round3ParameterNativePrimary F g (Ref.parameterChart ip)) q ell
        (round3ParameterNativeDomain (Ref.parameterChart ip) (univ : Set (P × M)))
        (round3ParameterNativeDomain (Ref.parameterChart ip) (univ : Set (P × M)))
        Mnew Cut Tinv Tobs (L*5^Module.finrank ℝ (Ep × D)) (round3ParameterOriginalNativeSamplesAt Data ip),
      ∀ ip, (fam ip).choice=round3ParameterNativeChoices choice (Ref.parameterChart ip)
  have hOne' (ip : Fin Ref.parameterCount) :
      ∃ fam : Round3ParameterPreparedSecondaryFamily (SubSecondary := Sigma Sub) Data
        (fun p => F ((Ref.parameterChart ip).symm p)) (fun p => hF ((Ref.parameterChart ip).symm p))
        (round3ParameterNativePrimary F g (Ref.parameterChart ip)) q ell
        (round3ParameterNativeDomain (Ref.parameterChart ip) (univ : Set (P × M)))
        (round3ParameterNativeDomain (Ref.parameterChart ip) (univ : Set (P × M)))
        Mnew Cut Tinv Tobs (L*5^Module.finrank ℝ (Ep × D)) (round3ParameterOriginalNativeSamplesAt Data ip),
      fam.choice=round3ParameterNativeChoices choice (Ref.parameterChart ip) := by
    obtain ⟨fam,hFam⟩ := round3Parameter_secondary_domain_transport Data
      (fun p => F ((Ref.parameterChart ip).symm p)) (fun p => hF ((Ref.parameterChart ip).symm p))
      (round3ParameterNativePrimary F g (Ref.parameterChart ip)) q ell
      ((Ref.parameterChart ip).target ×ˢ (univ : Set M))
      (round3ParameterNativeDomain (Ref.parameterChart ip) (univ : Set (P × M))) (hW ip).symm
      Mnew Cut Tinv Tobs (L*5^Module.finrank ℝ (Ep × D)) (round3ParameterOriginalNativeSamplesAt Data ip)
      (family ip)
    exact ⟨fam,hFam.trans (hChoice ip)⟩
  choose fam hFam using hOne'
  exact ⟨fam,hFam⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_coherent_secondary_factory
