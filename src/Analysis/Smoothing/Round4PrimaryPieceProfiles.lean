import Probes.Round3PreparedPrimaryPiece
import Smoothing.Round4PrimaryRefinementProfiles

/-! Genuine primary host pieces. The inhabited producer below is the actual
compact refinement from original smooth phases; empty pieces are used only
for zero padding of finite dependent index families. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

/-- Derivative information for the SAME actual primary pieces. No newly
produced chart or cutoff budget is supplied: all bounds follow from the
original phase and parent jets at the displayed samples. -/
structure Round4PrimaryJetSupply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (W : Set (Ep × M)) (theta : Ep × M → ℝ) (s : Finset X)
    (piece : s → Round3PreparedPrimaryPiece Data i.2 nu W) where
  mu : ℝ
  Mb : ℝ
  buffer : ℝ
  O : Set X
  mu_pos : 0 < mu
  Mb_nonneg : 0 ≤ Mb
  buffer_pos : 0 < buffer
  open_domain : IsOpen O
  domain : O ⊆ actualOriginalPrimaryNativeOpen Data nu i
  source : ∀ a : s, (piece a).native.source ⊆ O
  jets : ∀ (S : Set X) (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
    let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
    let Psi := (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) ∘ q.symm
    (∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ O ∩ S,
      weight^k*‖iteratedFDeriv ℝ (k+1) Psi x‖ ≤ Mj) →
    (∀ (a : s) k, 1 ≤ k → k ≤ j → ∀ x ∈ (piece a).native.source ∩ S,
      weight^k*‖iteratedFDeriv ℝ (k+1) (piece a).native x‖ ≤ 2^(j+2)*Mj) ∧
    (∀ (a : s) k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ (piece a).native.target,
      (piece a).native.symm y ∈ S → weight^(k-1)*‖iteratedFDeriv ℝ k (piece a).native.symm y‖ ≤
        actualEuclideanPhaseSampleInverseJetCost mu Mb Mj j) ∧
    ∀ Mt : ℝ, 0 ≤ Mt → weight ≤ buffer →
      (∀ k, k ≤ j → ∀ x ∈ O ∩ S,
        weight^k*‖iteratedFDeriv ℝ k (theta ∘ q.symm) x‖ ≤ Mt) →
      ∀ (a : s) y, y ∈ (piece a).native.target → (piece a).native.symm y ∈ S →
        weight^j*‖iteratedFDeriv ℝ j
          ((piece a).cutoff ∘ (actualHostAdaptedChart (Data.atlas.chart (piece a).host) (piece a).native).symm) y‖ ≤
            actualHostRefinementSampleCutoffCost X mu Mb Mj Mt j

variable [T2Space M]

theorem round4_actual_original_primary_pieces_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hParam : ∀ w ∈ W, w.1 ∈ (Data.parameterChart i.2).target)
    (hOriginal : MapsTo (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2))
      W (incrementsOriginalParameterRegion Data))
    (theta : Ep × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hTheta : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta)
    (hThetaSupport : tsupport theta ⊆ W ∩
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source) :
    ∃ (s : Finset X) (out : s → Round3PreparedPrimaryPiece Data i.2 nu W),
      (∀ a : s, (out a).host = i.1) ∧
      (∀ a : s, tsupport (out a).cutoff ⊆ tsupport theta) ∧
      (∀ y ∈ incrementsGlobalRelativeSupport W
          (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm z.1,z.2)),
        ∀ᶠ w in 𝓝 y, ∑ a : s, (out a).cutoff w = theta w) ∧
      (∀ y, (Finset.univ.filter (fun a : s => y ∈ tsupport (out a).cutoff)).card ≤ 5^Module.finrank ℝ X) ∧
      Nonempty (Round4PrimaryJetSupply Data i nu W theta s out) := by
  obtain ⟨mu,Mb,buffer,O,s,b,e,eta,Bnative,hmu,hMb,hbuffer,hO,hOprim,hB,hData,hNative,
    hSource,hActive,hCompactEta,hSmooth,hSupport,hSum,hGerm,hCount,hFirst,hBO,hJets⟩ :=
    round4_actual_original_primary_refinement_profiles Data hd hs hp i nu W hW hParam hOriginal
      theta hCompact hTheta hThetaSupport
  let out := fun a : s => ({
    host := i.1
    native := b a
    slices := e a
    cutoff := eta a
    data := hData a
    native_source := hNative a
    source_domain := hSource a
    active := hActive a
    compact := hCompactEta a
    smooth := hSmooth a
    support := fun _ hz => (hSupport a hz).1
    Bnative := Bnative
    positive := hB
    native_first := hFirst a } : Round3PreparedPrimaryPiece Data i.2 nu W)
  refine ⟨s,out,fun _ => rfl,fun a _ hz => (hSupport a hz).2,hGerm,hCount,?_⟩
  exact ⟨{
    mu := mu
    Mb := Mb
    buffer := buffer
    O := O
    mu_pos := hmu
    Mb_nonneg := hMb
    buffer_pos := hbuffer
    open_domain := hO
    domain := hOprim
    source := hBO
    jets := hJets }⟩

#print axioms round4_actual_original_primary_pieces_profiles
end GlobalEmbedding.Continuation
