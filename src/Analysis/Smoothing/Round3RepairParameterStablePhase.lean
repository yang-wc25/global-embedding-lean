import Smoothing.Round3OuterStablePrimaryCrossData
import Smoothing.Round3OuterParameterCarrierCover
import Smoothing.Round3OuterParameterPrimaryLegality
import Probes.Round3PreparedParameterStagePhaseConditions

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Fin (m+1+d) → ℝ
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance repairPhaseFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance repairPhaseFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance repairPhaseFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance repairPhaseFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance

/-- The actual all-parameter stable reference family supplies primary Good
on a genuine common carrier. Together with the true signed Good result it
returns every original phase condition for the SAME current map. -/
theorem round3_repair_parameter_stable_full_phase
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs) (hAll : Ref.parameterSet=univ)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet)
    (R : ℕ) (hPart : ∀ z, ∑ i, theta i z=1)
    (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ R)
    (F : P → M → Ey)
    (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (stable : Round3ParameterWholeStableReference Ref hd hs theta packet profiles F hF)
    (hSigned : ∀ (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) z,
      z ∈ tsupport (Ref.cutoff r.val.1.1) ∩ tsupport (Ref.cutoff r.val.1.2) →
      GoodCovector (F z.1) (hF z.1) z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (round3PreparedPhysicalSignedPhase Ref r z)).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => round3PreparedPhysicalSignedPhase Ref r (z.1,x)) z.2))) :
    ∃ domain : Fin Ref.primaryCount → Set (P × M),
      (∀ nu, domain nu ⊆ Ref.primaryDomain nu) ∧
      (∀ nu, tsupport (Ref.cutoff nu) ⊆ domain nu) ∧
      let E : IncrementsOriginalNativeData (m+1) d N M P :=
        {Ref with F := Function.uncurry F, primaryDomain := domain}
      ∃ hdE : IncrementsOriginalDomainConditions E,
      ∃ hsE : IncrementsOriginalSmoothInputs E,
        IncrementsOriginalPhaseConditions E hdE hsE := by
  let ps := round3OuterStablePrimaryPacket Ref hd hs theta packet profiles F hF stable
  let A := Round3ParameterWholePrimaryIndex Ref theta packet
  let g := round3ParameterWholePrimaryFamily Ref hd hs hn theta ps
  let piece := round3ParameterWholePrimaryPiece Ref hd theta ps
  let host := fun nu (_ : Fin Ref.parameterCount) (a : A) => (piece nu a).host
  let b := fun nu ip (a : A) => round3ParameterCrossNativeChart
    (Ref.parameterChart a.1.2) (Ref.parameterChart ip) (piece nu a).native
  have geom : Round3ParameterOriginalPrimaryGeometry Ref g (R*5^Module.finrank ℝ X) :=
    round3Parameter_whole_primary_family_geometry Ref hd hs hn theta ps hPart R hCount
  obtain ⟨hOpen,hCover,hSub,hActive,hCarrier⟩ := round3_parameter_original_fixed_carrier Ref g _ geom
  let domain := fun nu => round3FixedCarrierDomain (g.eta nu)
  let E : IncrementsOriginalNativeData (m+1) d N M P :=
    {Ref with F := Function.uncurry F, primaryDomain := domain}
  have hDom : ∀ nu, domain nu ⊆ Ref.primaryDomain nu := fun nu _ hz => (hSub nu hz).1
  let hdE : IncrementsOriginalDomainConditions E :=
    { hd with
      primary_open := hOpen
      cutoff_support_local := by
        intro nu z hz
        obtain ⟨w,hw,rfl⟩ := hz
        exact hCover nu (tsupport_comp_subset_preimage (Ref.cutoff nu) continuous_subtype_val hw) }
  let hsE : IncrementsOriginalSmoothInputs E :=
    { F_joint := hFjoint.contMDiffOn
      H_coordinates := hs.H_coordinates
      phase_joint := fun nu => (hs.phase_joint nu).mono (fun _ hz => ⟨hDom nu hz.1,hz.2⟩)
      cutoff_joint := fun nu => (hs.cutoff_joint nu).mono (fun _ hz => ⟨hDom nu hz.1,hz.2⟩)
      normal_joint := fun nu => (hs.normal_joint nu).mono (fun _ hz => ⟨hDom nu hz.1,hz.2⟩) }
  obtain ⟨e,hData,hNative,hActive',hInner,hChart,hFirst,hFrame,hNormal,hInverse⟩ :=
    round3_stable_primary_all_observer_data Ref hd hs hn theta packet profiles F hF stable
  have hCoverNative := round3_parameter_fixed_carrier_native_cover Ref g _ geom host b hChart
  have hSources : ∀ nu ip (w : Ep × M), w.1 ∈ (Ref.parameterChart ip).target →
      ((Ref.parameterChart ip).symm w.1,w.2) ∈ domain nu →
      ∃ a, w ∈ (actualHostAdaptedChart (Ref.atlas.chart (host nu ip a)) (b nu ip a)).source := by
    intro nu ip w hp hw
    obtain ⟨a,ha⟩ := hCoverNative.2.2.1 nu ip w hp hw
    exact ⟨a,hCoverNative.2.1 nu ip a ha⟩
  have hGood := round3_parameter_primary_good_from_actual_cover E hdE hsE hAll hF
    (fun _ => A) host b e hData hSources (profiles.cT/16) (div_pos profiles.cT_pos (by norm_num)) hFrame
  refine ⟨domain,hDom,hCover,hdE,hsE,?_⟩
  exact round3_prepared_parameter_rebound_phase_conditions Ref (Function.uncurry F) hF Ref.H Ref.parameterOpen
    Ref.freeNormal domain Ref.tensorNeighborhood hSigned hdE hsE hGood

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_parameter_stable_full_phase
