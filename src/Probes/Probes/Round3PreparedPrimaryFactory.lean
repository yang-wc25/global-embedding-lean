import Probes.Round3PreparedPrimarySigma
import Probes.Round3PreparedFiniteAssembly
import Probes.ActualPreparedParentsFromCoordinateBounds

/-! All actual primary pieces are constructed from the original packet.
The same compact parameter cutoff and squared source parents supply one
finite common index, an ordinary partition of germs, true source containment,
and the dimensional local overlap bound. The packet precedes all later jet
orders and solver inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_actual_original_primary_preparation
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart baseIndex.2 = OpenPartialHomeomorph.refl Ep)
    (B0 Ts : ℕ → ℝ) (hB0 : ∀ j, 0 ≤ B0 j) (hTs : ∀ j, 0 ≤ Ts j) (degree : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas B0 Ts degree)
    (centers : Fin Data.atlas.count → D) (radius : ℝ)
    (hBound : ∀ i, (Data.atlas.chart i) '' Data.atlas.inner i ⊆ closedBall (centers i) radius) :
    ∃ V : Set Ep, IsOpen V ∧ Data.parameterSet ⊆ V ∧ V ⊆ Data.parameterOpen ∧
    ∃ (s : Fin Data.primaryCount → Fin Data.atlas.count → Finset X)
      (piece : ∀ nu : Fin Data.primaryCount,
        Sigma (fun nu : Fin Data.primaryCount => Sigma (fun host : Fin Data.atlas.count => ↥(s nu host))) →
        Round3PreparedPrimaryPiece Data baseIndex.2 nu (Data.parameterOpen ×ˢ (univ : Set M))),
      (∀ nu a y, y ∈ tsupport (piece nu a).cutoff → y.2 ∈ Data.atlas.inner (piece nu a).host) ∧
      (∀ nu y, y ∈ incrementsGlobalRelativeSupport (V ×ˢ (univ : Set M))
          (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart baseIndex.2).symm z.1,z.2)) →
        ∀ᶠ w in 𝓝 y, ∑ a, (piece nu a).cutoff w = 1) ∧
      ∀ nu y, (Finset.univ.filter (fun a => y ∈ tsupport (piece nu a).cutoff)).card ≤
        (degree+1)*5^Module.finrank ℝ X := by
  obtain ⟨beta,V,C,Bbeta,Bjoint,hBeta,hV,hKV,hVO,hC,hSupportBeta,hCO,hBetaOne,hRange,
      hBbeta,hBetaJets,hBjoint,hParents⟩ :=
    actual_original_compact_parameter_parents_from_coordinates (m := m) (d := d) (M := M)
      Data.parameterSet Data.parameterOpen hd.parameter_compact hd.parameter_open hd.parameter_subset
      B0 Ts hB0 hTs degree
  let chi := squareNormalizedCutoff RS.raw
  let theta := fun host (z : Ep × M) => beta z.1*chi host z.2^2
  obtain ⟨hTheta,hSum,hParentGerm,hParentSupport,hCompact,hJets⟩ :=
    hParents Data.atlas hd.atlas_smooth RS centers radius hBound
  let W := Data.parameterOpen ×ˢ (univ : Set M)
  have hW : IsOpen W := hd.parameter_open.prod isOpen_univ
  have hParam : ∀ z ∈ W, z.1 ∈ (Data.parameterChart baseIndex.2).target := by
    intro z hz
    rw [hId]
    exact Set.mem_univ _
  have hOriginal : MapsTo (fun z : Ep × M => ((Data.parameterChart baseIndex.2).symm z.1,z.2))
      W (incrementsOriginalParameterRegion Data) := by
    intro z hz
    simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq,
      W,incrementsOriginalParameterRegion] using hz
  have hThetaSupport (host : Fin Data.atlas.count) : tsupport (theta host) ⊆ W ∩
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart host)).source := by
    intro z hz
    have hh := hParentSupport host hz
    exact ⟨⟨hCO hh.1,Set.mem_univ _⟩,Set.mem_univ _,Data.atlas.inner_subset host hh.2⟩
  have hLocal (nu : Fin Data.primaryCount) (host : Fin Data.atlas.count) :=
    round3_actual_original_primary_pieces Data hd hs hp (host,baseIndex.2) nu W hW hParam hOriginal
      (theta host) (hCompact host) (hTheta host) (hThetaSupport host)
  choose s localPiece hHost hParent hGerm hLocalCount using hLocal
  let Sub := fun nu : Fin Data.primaryCount => Sigma (fun host : Fin Data.atlas.count => ↥(s nu host))
  let dep := fun (nu : Fin Data.primaryCount) (a : Sub nu) => localPiece nu a.1 a.2
  let piece := round3PreparedPrimarySigmaPiece Data hd baseIndex W Sub dep
  have hThetaChi (host : Fin Data.atlas.count) : tsupport (theta host) ⊆
      (fun z : Ep × M => z.2) ⁻¹' tsupport (chi host) := by
    apply closure_minimal _ ((isClosed_tsupport _).preimage continuous_snd)
    intro z hz
    apply subset_tsupport
    intro hzero
    apply hz
    change beta z.1*chi host z.2^2 = 0
    rw [hzero]
    simp
  have hChiCount (y : Ep × M) : (activeCutoffIndices chi y.2).card ≤ degree+1 :=
    squareNormalizedCutoff_card_le_enlarged_degree Data.atlas.support RS.raw RS.enlarged_support
      degree (fun i => (tensorSupportDegree_le_original Data.atlas i).trans RS.degree) y.2
  have hParentCount (y : Ep × M) :
      (Finset.univ.filter (fun host => y ∈ tsupport (theta host))).card ≤ degree+1 := by
    apply (Finset.card_le_card ?_).trans (hChiCount y)
    intro host hh
    exact (mem_activeCutoffIndices chi y.2 host).2 (hThetaChi host (Finset.mem_filter.mp hh).2)
  refine ⟨V,hV,hKV,hVO,s,piece,?_,?_,?_⟩
  · intro nu ⟨mu,a⟩ y hy
    by_cases h : mu = nu
    · subst mu
      simp only [piece,round3PreparedPrimarySigmaPiece_active,dep] at hy ⊢
      rw [hHost nu a.1 a.2]
      exact (hParentSupport a.1 (hParent nu a.1 a.2 hy)).2
    · simp only [piece,round3PreparedPrimarySigmaPiece,h,dite_false,
        round3PreparedPrimaryEmpty_cutoff,tsupport_zero,mem_empty_iff_false] at hy
  · intro nu y hy
    have hG : IsOpen (V ×ˢ (univ : Set M)) := hV.prod isOpen_univ
    rw [parameterRound2_global_relativeSupport_eq _ hG] at hy
    have hyW : y ∈ incrementsGlobalRelativeSupport W
        (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart baseIndex.2).symm z.1,z.2)) := by
      rw [parameterRound2_global_relativeSupport_eq W hW]
      exact ⟨⟨hVO hy.1.1,hy.1.2⟩,hy.2⟩
    have hall : ∀ᶠ w in 𝓝 y, ∀ host : Fin Data.atlas.count,
        ∑ a : ↥(s nu host), (localPiece nu host a).cutoff w = theta host w :=
      eventually_all.mpr (fun host => hGerm nu host y hyW)
    filter_upwards [hall,hParentGerm y hy.1.1] with w hw hpw
    change (∑ a : Sigma Sub, (round3PreparedPrimarySigmaPiece Data hd baseIndex W Sub dep nu a).cutoff w) = 1
    rw [round3_prepared_primary_sigma_cutoff_sum,Fintype.sum_sigma]
    exact (Finset.sum_congr rfl (fun host _ => hw host)).trans hpw
  · intro nu y
    change (Finset.univ.filter (fun a : Sigma Sub => y ∈ tsupport
      (round3PreparedPrimarySigmaPiece Data hd baseIndex W Sub dep nu a).cutoff)).card ≤ _
    rw [round3_prepared_primary_sigma_support_card]
    exact round3_prepared_sigma_local_count (fun host : Fin Data.atlas.count => ↥(s nu host))
      (fun host => tsupport (theta host))
      (fun host a => tsupport (localPiece nu host a).cutoff) (fun host a => hParent nu host a)
      (degree+1) (5^Module.finrank ℝ X) y (hParentCount y) (fun host => hLocalCount nu host y)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_actual_original_primary_preparation
