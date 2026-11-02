import Round2.AtlasNormComposition

/-!
# Uniform transfer between actual compact smooth atlas C² norms

There are finitely many pairs of charts.  Their actual compact support
intersections supply finite transition bounds, including empty intersections.
Every point of an outer support belongs to an inner support, so these finite
bounds control every coefficient of the original outer C² gauge.

The resulting constant is chosen before the smooth ambient map and its norm
budget.  No equality of atlas norms, no global tangent frame, and no regularity
or boundedness of a map outside a true chart domain is assumed.
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

/-- A finite geometric constant transfers the original paper C² norm from
one compact smooth atlas whose supports cover to any other compact smooth
atlas.  In particular the outer supports need not cover or have interior.
The theorem also includes empty sources, empty chart lists and n = 0. -/
theorem exists_probeAtlasC2_transfer_bound
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i))
    (hBc : ∀ j, IsCompact (B.support j))
    (hcover : ∀ x : M, ∃ i, x ∈ A.support i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : M → V), ContMDiff IM 𝓘(ℝ, V) ∞ F →
      ∀ b : ℝ, 0 ≤ b → probeAtlasCj A 2 F ≤ ENNReal.ofReal b →
        probeAtlasCj B 2 F ≤ ENNReal.ofReal (C * b) := by
  classical
  choose D hD htransition using fun p : Fin A.count × Fin B.count ↦
    exists_atlasNormTransition_twoJet_bound A B hA hB hAc hBc p.1 p.2
  obtain ⟨Dmax, hDmax⟩ := Finite.exists_le D
  let Dtotal := |Dmax| + 1
  have hDtotal : 1 ≤ Dtotal := by dsimp only [Dtotal]; linarith [abs_nonneg Dmax]
  have htrans (i : Fin A.count) (j : Fin B.count)
      (z) (hz : z ∈ atlasNormOverlapSupport A B i j) :
      ‖iteratedFDeriv ℝ 1 (atlasNormTransition A B i j) z‖ ≤ Dtotal ∧
      ‖iteratedFDeriv ℝ 2 (atlasNormTransition A B i j) z‖ ≤ Dtotal := by
    have hle : D (i, j) ≤ Dtotal := (hDmax (i, j)).trans (by
      dsimp only [Dtotal]; linarith [le_abs_self Dmax])
    exact ⟨((htransition (i,j) z hz).1).trans hle,
      ((htransition (i,j) z hz).2).trans hle⟩
  let C := 2 * ((n : ℝ) + 1) ^ 2 * Dtotal ^ 2
  have hC : 0 < C := by
    have hdim : 0 < (n : ℝ) + 1 := by positivity
    have hDpos : 0 < Dtotal := by linarith
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro F hF b hb hbound
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let v := EuclideanSpace.equiv (Fin N) ℝ
  change (⨆ j, paperCoordinateCj 2
    (fun y ↦ v (F ((B.chart j).symm (e.symm y))))
    (e '' (B.chart j).target) (e '' ((B.chart j) '' B.support j))) ≤ _
  refine iSup_le fun j ↦ ?_
  have hO : IsOpen (e '' (B.chart j).target) :=
    e.toHomeomorph.isOpenMap _ (B.chart j).open_target
  have hSO : e '' ((B.chart j) '' B.support j) ⊆ e '' (B.chart j).target := by
    rintro y ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨B.chart j x, (B.chart j).map_source (hB.support_subset j hx), rfl⟩
  rw [paperCoordinateCj_eq_coordinateJetGauge 2 _ _ _ hO hSO
    (probeAtlas_coordinate_smooth B hB F hF j)]
  refine iSup_le fun k ↦ iSup_le fun z ↦ iSup_le fun σ ↦ iSup_le fun c ↦ ?_
  apply ENNReal.ofReal_le_ofReal
  rcases z with ⟨z, hz⟩
  rcases hz with ⟨w, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨i, hi⟩ := hcover x
  have hz : e (B.chart j x) ∈ atlasNormOverlapSupport A B i j :=
    ⟨B.chart j x, ⟨x, ⟨hx, hi⟩, rfl⟩, rfl⟩
  exact (coordinate_jet_coefficient_le _ _ σ c).trans
    (atlasNormOverlap_coordinate_twoJet_bound A B hA hB i j hDtotal
      (htrans i j) F hF hb hbound (by omega : k.val ≤ 2) hz)

end GlobalEmbedding.Upgrade
