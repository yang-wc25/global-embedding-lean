import NormalPolar.PassiveOriginalData
import NormalPolar.PassiveParameterPrimary
import NormalPolar.PassiveParameterGlobalSupport
import Probes.Round3ParameterOriginalPrimaryGeometry

/-! The actual original primary geometry on the full compact parameter
manifold. The seed phase, cutoffs, free normals, linear arguments, spatial
inverse and subordinate partition are retained. The original subordinate
count is unchanged, with compact support proved on the whole new P. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M S P Β : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace S] [Subsingleton S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) S]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin 0)) ∞ S]
  [TopologicalSpace P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

theorem passiveOriginal_primary_geometry
    (s₀ : S) (seed : IncrementsOriginalNativeData (m+1) 0 N M S)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m)
      (Λ := Fin seed.primaryCount) (Β := Β) (fun s x => seed.F (s,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry seed g R) :
    Round3ParameterOriginalPrimaryGeometry (passiveOriginalData s₀ seed B Q)
      (passiveParameterPrimary s₀ (fun s x => seed.F (s,x)) g) R := by
  let κ : P × M → S × M := fun z => (s₀,z.2)
  have hκ : ContMDiff
      ((𝓘(ℝ,EuclideanSpace ℝ (Fin d))).prod IM)
      ((𝓘(ℝ,EuclideanSpace ℝ (Fin 0))).prod IM) ∞ κ :=
    contMDiff_const.prodMk contMDiff_snd
  refine {
    phase := ?_
    cutoff := ?_
    normal := ?_
    linear := ?_
    preserves := passiveParameterPrimary_chart_preserves s₀ _ g
    inverse := ?_
    phase_coordinate := ?_
    inverse_active := ?_
    smooth := fun nu a => (geom.smooth nu a).comp hκ
    compact := fun nu a => passiveParameter_tsupport_compact s₀ (g.eta nu a) (geom.compact nu a)
    support := ?_
    partition := ?_
    count := ?_ }
  · funext nu z
    exact congrFun (congrFun geom.phase nu) (s₀,z.2)
  · funext nu z
    exact congrFun (congrFun geom.cutoff nu) (s₀,z.2)
  · funext nu z
    exact congrFun (congrFun geom.normal nu) (s₀,z.2)
  · funext nu p x
    exact congrFun (congrFun (congrFun geom.linear nu) s₀) x
  · intro nu a z hz
    have hh := geom.inverse nu a (s₀,z.2) hz
    apply Prod.ext
    · rfl
    · exact congrArg (fun y : S × M => y.2) hh
  · intro nu a z hz
    exact geom.phase_coordinate nu a (s₀,z.2) hz
  · intro nu a z hz
    have hh := geom.inverse_active nu a (s₀,z.2) hz
    exact ⟨hh.1,mem_univ _,mem_univ _⟩
  · intro nu a z hz
    exact geom.support nu a ((passiveParameter_tsupport_iff s₀ (g.eta nu a) z.1 z.2).mp hz)
  · intro nu z hz
    have hz' := (passiveParameter_tsupport_iff s₀ (seed.cutoff nu) z.1 z.2).mp hz
    have hh : ContinuousAt κ z :=
      (continuous_const.prodMk continuous_snd : Continuous κ).continuousAt
    exact hh.eventually (geom.partition nu (s₀,z.2) hz')
  · intro nu z
    change (Finset.univ.filter (fun a => z ∈ tsupport
      (fun w : P × M => g.eta nu a (s₀,w.2)))).card ≤ R
    rw [passiveParameter_tsupport_overlap s₀ (g.eta nu) z]
    exact geom.count nu (s₀,z.2)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_primary_geometry
