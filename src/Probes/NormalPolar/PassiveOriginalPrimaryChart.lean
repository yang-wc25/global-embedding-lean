import NormalPolar.PassiveOriginalPrimaryGeometry
import Probes.Round3ParameterObserverChartProfiles

/-! Both sides of the actual passive primary chart are jointly smooth on
their true domains. The physical parameter manifold remains arbitrary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace S] [Subsingleton S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) S]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
local notation "IS" => 𝓘(ℝ,EuclideanSpace ℝ (Fin 0))
local notation "IP" => 𝓘(ℝ,EuclideanSpace ℝ (Fin d))

theorem passiveOriginal_primary_chart_smooth
    (s₀ : S) (a : OpenPartialHomeomorph (S × M) (S × D))
    (ha : ContMDiffOn ((IS).prod IM) ((IS).prod IM) ∞ a a.source)
    (hai : ContMDiffOn ((IS).prod IM) ((IS).prod IM) ∞ a.symm a.target) :
    ContMDiffOn ((IP).prod IM) ((IP).prod IM) ∞
      (passiveParameterChart (P := P) s₀ a) (passiveParameterChart (P := P) s₀ a).source ∧
    ContMDiffOn ((IP).prod IM) ((IP).prod IM) ∞
      (passiveParameterChart (P := P) s₀ a).symm (passiveParameterChart (P := P) s₀ a).target := by
  constructor
  · let κ : P × M → S × M := fun z => (s₀,z.2)
    have hκ : ContMDiff ((IP).prod IM) ((IS).prod IM) ∞ κ :=
      contMDiff_const.prodMk contMDiff_snd
    have hcomp := ha.comp hκ.contMDiffOn (fun _ h => h)
    exact contMDiffOn_fst.prodMk (contMDiff_snd.comp_contMDiffOn hcomp)
  · let κ : P × D → S × D := fun z => (s₀,z.2)
    have hκ : ContMDiff ((IP).prod IM) ((IS).prod IM) ∞ κ :=
      contMDiff_const.prodMk contMDiff_snd
    have hcomp := hai.comp hκ.contMDiffOn (fun _ h => h)
    exact contMDiffOn_fst.prodMk (contMDiff_snd.comp_contMDiffOn hcomp)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_primary_chart_smooth
