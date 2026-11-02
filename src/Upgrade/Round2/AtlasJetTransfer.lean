import Round2.AtlasJetComposition

/-!
# Transfer the original Cʲ probe bounds between fixed compact atlases

The source and output coordinate representatives, evaluation supports and
open differentiation domains are exactly those in `probeAtlasCj`.  This
applies to every fixed finite order, especially the C¹/C² parameter-response
bounds and the spatial C³ bound of one and the same actual probe family.

The primary theorem assumes coordinate smoothness only, so no unproved global
smoothness premise is imposed on a parameter-response field.  A convenience
theorem supplies those coordinate hypotheses for globally smooth maps.
-/

noncomputable section
open Function Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

omit [ChartedSpace E M] [IsManifold IM ∞ M] [T2Space M] in
/-- Native coordinate smoothness of the actual map gives exactly the paper
coordinate smoothness used in the unchanged atlas norm.  No map regularity
outside the original chart target is required. -/
theorem probeAtlas_paper_coordinate_smooth_of_native
    (A : BufferedAtlas M E) (F : M → V) (i : Fin A.count)
    (hF : ContDiffOn ℝ ∞ (F ∘ (A.chart i).symm) (A.chart i).target) :
    ContDiffOn ℝ ∞
      (fun y ↦ (EuclideanSpace.equiv (Fin N) ℝ)
        (F ((A.chart i).symm ((EuclideanSpace.equiv (Fin n) ℝ).symm y))))
      ((EuclideanSpace.equiv (Fin n) ℝ) '' (A.chart i).target) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  apply (EuclideanSpace.equiv (Fin N) ℝ).contDiff.comp_contDiffOn
  apply hF.comp e.symm.contDiff.contDiffOn
  rintro y ⟨z, hz, rfl⟩
  simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using hz

/-- A constant chosen before the field and its budget transfers the original
finite-order atlas gauge.  This coordinate-smooth form is directly usable for
the actual native parameter-response fields.  Empty sources and supports,
order zero and source/target dimension zero are retained. -/
theorem exists_probeAtlasCj_transfer_bound_of_coordinate_smooth
    (order : ℕ) (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i))
    (hBc : ∀ j, IsCompact (B.support j))
    (hcover : ∀ x : M, ∃ i, x ∈ A.support i) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : M → V,
      (∀ i, ContDiffOn ℝ ∞
        (fun y ↦ (EuclideanSpace.equiv (Fin N) ℝ)
          (F ((A.chart i).symm ((EuclideanSpace.equiv (Fin n) ℝ).symm y))))
        ((EuclideanSpace.equiv (Fin n) ℝ) '' (A.chart i).target)) →
      (∀ j, ContDiffOn ℝ ∞
        (fun y ↦ (EuclideanSpace.equiv (Fin N) ℝ)
          (F ((B.chart j).symm ((EuclideanSpace.equiv (Fin n) ℝ).symm y))))
        ((EuclideanSpace.equiv (Fin n) ℝ) '' (B.chart j).target)) →
      ∀ b : ℝ, 0 ≤ b → probeAtlasCj A order F ≤ ENNReal.ofReal b →
        probeAtlasCj B order F ≤ ENNReal.ofReal (C * b) := by
  classical
  choose D hD htransition using fun p : Fin A.count × Fin B.count ↦
    exists_atlasNormTransition_finiteJet_bound order A B hA hB hAc hBc p.1 p.2
  obtain ⟨Dmax, hDmax⟩ := Finite.exists_le D
  let Dtotal := |Dmax| + 1
  have hDtotal : 1 ≤ Dtotal := by dsimp only [Dtotal]; linarith [abs_nonneg Dmax]
  have htrans (i : Fin A.count) (j : Fin B.count)
      (z) (hz : z ∈ atlasNormOverlapSupport A B i j) (a : ℕ) (ha : a ≤ order) :
      ‖iteratedFDeriv ℝ a (atlasNormTransition A B i j) z‖ ≤ Dtotal := by
    exact (htransition (i,j) z hz a ha).trans ((hDmax (i,j)).trans (by
      dsimp only [Dtotal]; linarith [le_abs_self Dmax]))
  let C := (order.factorial : ℝ) * ((n : ℝ) + 1) ^ order * Dtotal ^ order
  have hC : 0 < C := by
    have hfac : 0 < (order.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos order)
    have hdim : 0 < (n : ℝ) + 1 := by positivity
    have hDpos : 0 < Dtotal := by linarith
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro F hFA hFB b hb hbound
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let v := EuclideanSpace.equiv (Fin N) ℝ
  change (⨆ j, paperCoordinateCj order
    (fun y ↦ v (F ((B.chart j).symm (e.symm y))))
    (e '' (B.chart j).target) (e '' ((B.chart j) '' B.support j))) ≤ _
  refine iSup_le fun j ↦ ?_
  have hO : IsOpen (e '' (B.chart j).target) :=
    e.toHomeomorph.isOpenMap _ (B.chart j).open_target
  have hSO : e '' ((B.chart j) '' B.support j) ⊆ e '' (B.chart j).target := by
    rintro y ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨B.chart j x, (B.chart j).map_source (hB.support_subset j hx), rfl⟩
  rw [paperCoordinateCj_eq_coordinateJetGauge order _ _ _ hO hSO (hFB j)]
  refine iSup_le fun k ↦ iSup_le fun z ↦ iSup_le fun σ ↦ iSup_le fun c ↦ ?_
  apply ENNReal.ofReal_le_ofReal
  rcases z with ⟨z, hz⟩
  rcases hz with ⟨w, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨i, hi⟩ := hcover x
  have hz : e (B.chart j x) ∈ atlasNormOverlapSupport A B i j :=
    ⟨B.chart j x, ⟨x, ⟨hx, hi⟩, rfl⟩, rfl⟩
  exact (coordinate_jet_coefficient_le _ _ σ c).trans
    (atlasNormOverlap_coordinate_finiteJet_bound order A B hA hB i j hDtotal
      (htrans i j) F (hFA i) hb hbound (by omega : k.val ≤ order) hz)

/-- The same finite-order transfer for globally smooth actual maps.  This
does not require another probes family or a provider on the output atlas. -/
theorem exists_probeAtlasCj_transfer_bound
    (order : ℕ) (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i))
    (hBc : ∀ j, IsCompact (B.support j))
    (hcover : ∀ x : M, ∃ i, x ∈ A.support i) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : M → V, ContMDiff IM 𝓘(ℝ, V) ∞ F →
      ∀ b : ℝ, 0 ≤ b → probeAtlasCj A order F ≤ ENNReal.ofReal b →
        probeAtlasCj B order F ≤ ENNReal.ofReal (C * b) := by
  obtain ⟨C, hC, htransfer⟩ := exists_probeAtlasCj_transfer_bound_of_coordinate_smooth
    (N := N) order A B hA hB hAc hBc hcover
  exact ⟨C, hC, fun F hF b hb hbound ↦ htransfer F
    (probeAtlas_coordinate_smooth A hA F hF)
    (probeAtlas_coordinate_smooth B hB F hF) b hb hbound⟩

end GlobalEmbedding.Upgrade
