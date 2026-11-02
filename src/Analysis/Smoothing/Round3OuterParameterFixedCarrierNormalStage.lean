import Smoothing.Round3OuterParameterCarrierProfiles
import Smoothing.Round3OuterParameterImmersedNormalStage
import Probes.Round3ParameterFixedProfileRebase

/-! A genuine reference primary family supplies the full carrier and all
normal chart budgets for the actual current SF. Constants are fixed before
the current map. The reference g remains attached to its reference map;
the new normal is constructed only after the actual SF reserves are proved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation
universe uA
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

theorem round3_exists_uniform_parameter_fixed_carrier_normal_stage
    (BS0 TS0 BP0 TP0 T Forward Meta Given : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hT : ∀ j, 0 ≤ T j) (hForward : ∀ j, 0 ≤ Forward j) (hGiven : ∀ j, 0 ≤ Given j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (r : ℕ)
    (budget cF cT mu : ℝ) (hbudget : 0 ≤ budget)
    (hcF : 0 < cF) (hcT : 0 < cT) (hmu : 0 < mu) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hdRef : IncrementsOriginalDomainConditions Ref)
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
    let Data := round3ParameterStageData Ref F H Ref.parameterOpen Ref.freeNormal Ref.primaryDomain neighborhood
    ∀ (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius r budget reference givenPacket)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hK : Data.parameterSet = univ)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (hReference : ∀ p ∈ Data.parameterOpen, ∀ x, Data.reference p x ≠ 0)
    (A : Type uA) [Fintype A]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Ref.primaryCount) (Β := A) (fun p x => Ref.F (p,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry Ref g R)
    (profiles : Round3ParameterOriginalChartProfiles Ref g Forward T Meta),
    let domain := fun nu => round3FixedCarrierDomain (g.eta nu)
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference givenPacket stage) p
    let normal := fun nu => parameterRound2_intrinsicUnitFreeNormalField
      (fun p x => Data.F (p,x)) hF (fun p x => Data.phase nu (p,x)) (Data.freeNormal nu)
    ∀ (host : Fin Ref.primaryCount → Fin Ref.parameterCount → A → Fin Ref.atlas.count)
    (b : Fin Ref.primaryCount → Fin Ref.parameterCount → A → OpenPartialHomeomorph X X)
    (e : Fin Ref.primaryCount → Fin Ref.parameterCount → A → Ep → OpenPartialHomeomorph M D),
    (∀ nu ip a, ActualOriginalHostSliceData (Data.atlas.chart (host nu ip a)) (b nu ip a)
      (fun w : Ep × M => Data.phase nu ((Data.parameterChart ip).symm w.1,w.2)) (e nu ip a)) →
    (∀ nu ip a, (b nu ip a).source ⊆ actualOriginalNativeOpen Data (host nu ip a,ip)) →
    (∀ nu ip a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a)).source →
      ((Data.parameterChart ip).symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) →
    (∀ nu ip a w, w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu ip a)) (b nu ip a)).source →
      w.2 ∈ Data.atlas.inner (host nu ip a)) →
    (∀ nu ip a, actualHostAdaptedChart (Ref.atlas.chart (host nu ip a)) (b nu ip a) =
      (round3ParameterNativePrimary (fun p x => Ref.F (p,x)) g (Ref.parameterChart ip)).chart nu a) →
    (∀ nu ip a z, z ∈ (b nu ip a).target → ∀ w : D, cF*‖w‖^2 ≤
      ‖fderiv ℝ ((fun x => Data.F ((Data.parameterChart ip).symm z.1,x)) ∘ (e nu ip a z.1).symm) z.2 w‖^2) →
    (∀ nu ip a z, z ∈ (b nu ip a).target → ∀ w : Tdata, cT*‖w‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (fun x => Data.F ((Data.parameterChart ip).symm z.1,x))
        (hF ((Data.parameterChart ip).symm z.1)) (e nu ip a z.1).symm z.2 w‖^2) →
    (∀ nu ip a z, z ∈ (b nu ip a).target → mu ≤
      ‖actualOriginalFreeNormalFieldRaw (fun p x => Data.F ((Data.parameterChart ip).symm p,x))
        (fun p => hF ((Data.parameterChart ip).symm p)) (e nu ip a)
        (fun z : X => Data.freeNormal nu ((Data.parameterChart ip).symm z.1,(e nu ip a z.1).symm z.2)) z‖) →
    (∀ j, parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤) →
    (∀ j, (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ Given j) →
    ∃ rebound : Round3RepairNormalRebound stage normal domain C,
      let E := round3RepairRebindNormalData Data normal domain
      IncrementsOriginalSliceImmersionInputs E ∧
      (∀ nu z, z ∈ domain nu ∩ incrementsOriginalParameterRegion Data →
        GoodCovector (fun x => Data.F (z.1,x)) (hF z.1) z.2
          (incrementsOriginalPhaseCovector Data nu z.1 z.2)) := by
  obtain ⟨C,hC,hMake⟩ := round3_exists_uniform_parameter_actual_immersed_normal_stage
    (m := m) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 T Forward Given hBS0 hTS0 hBP0 hTP0 hT hForward hGiven
    Ds Dp radius hradius r budget cF cT mu hbudget hcF hcT hmu
  refine ⟨C,hC,?_⟩
  intro Ref hdRef F H neighborhood Data reference givenPacket stage hd hs hK hDecomp hReference
    A _ g R geom profiles domain hF normal host b e hData hNative hActive hInner hChart
    hFirst hFrame hReserve hFixed hFixedBound
  obtain ⟨hOpen,hCovers,hSub,hEffective,hGeom,rest⟩ :=
    round3_parameter_original_fixed_carrier Ref g R geom
  let carrier := fun nu ip a => round3ParameterNativeActiveCarrier (Ref.parameterChart ip) (g.eta nu a)
  have hCarrier := round3_parameter_fixed_carrier_native_cover Ref g R geom host b hChart
  have hSource : ∀ nu ip a, (b nu ip a).source ⊆
      (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart (host nu ip a))).target := by
    intro nu ip a z hz
    exact ⟨mem_univ _,((round3Parameter_originalNativeOpen_iff Data (host nu ip a,ip) z).mp
      (hNative nu ip a hz)).1⟩
  have hJets := round3_parameter_fixed_carrier_normal_profiles Ref hdRef g R geom
    Forward T Meta profiles host b hChart hSource hInner
  have hRelativeCover : ∀ nu, incrementsOriginalRelativeCutoffSupport Data nu ⊆ domain nu := by
    intro nu z hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact hCovers nu (tsupport_comp_subset_preimage (Ref.cutoff nu) continuous_subtype_val hw)
  exact hMake Data reference givenPacket stage hd hs hK hDecomp hReference domain hOpen
    (fun nu z hz => (hSub nu hz).1) hRelativeCover (fun _ => A) host b e carrier
    hData hNative hActive hInner hCarrier.1 hCarrier.2.1 hCarrier.2.2.1
    hFirst hFrame hReserve hFixed hFixedBound hJets.1 hJets.2

#print axioms round3_exists_uniform_parameter_fixed_carrier_normal_stage
end GlobalEmbedding.Continuation
