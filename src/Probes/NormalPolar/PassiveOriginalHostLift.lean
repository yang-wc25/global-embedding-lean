import NormalPolar.PassiveParameterChart
import Probes.ActualIncrementHostGeometryInputs

/-! A genuine zero-parameter host realization lifts to all native parameter
values before any parameter is selected. The native chart is the literal
passive extension of the original one; genuine slices are reconstructed,
and every slice inverse is the same original spatial function. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "E₀" => EuclideanSpace ℝ (Fin 0)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem passiveOriginal_host_lift
    (c : OpenPartialHomeomorph M D) (hc : c ∈ maximalAtlas IM ∞ M)
    (b₀ : OpenPartialHomeomorph (E₀ × D) (E₀ × D))
    (psi₀ : E₀ × M → ℝ) (e₀ : E₀ → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData c b₀ psi₀ e₀) :
    let b := passiveParameterChart (P := Ep) (0 : E₀) b₀
    let psi := fun z : Ep × M => psi₀ (0,z.2)
    ∃ e : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData c b psi e ∧
      (∀ p, ((e p).symm : D → M) = (e₀ 0).symm) ∧
      (∀ p x, e p x = e₀ 0 x) := by
  intro b psi
  have hg := actual_host_slice_geometry_inputs c hc b₀ psi₀ e₀ hdata
  have hsource : b.source ⊆ (actualOriginalHostJointChart («Ep» := Ep) c).target :=
    fun z hz => ⟨mem_univ _,(hg.1 hz).2⟩
  have hb : ContDiffOn ℝ ∞ b b.source :=
    contDiffOn_fst.prodMk ((hg.2.1.comp
      (contDiffOn_const.prodMk contDiffOn_snd) (fun z hz => hz)).snd)
  have hbi : ContDiffOn ℝ ∞ b.symm b.target :=
    contDiffOn_fst.prodMk ((hg.2.2.1.comp
      (contDiffOn_const.prodMk contDiffOn_snd) (fun z hz => hz)).snd)
  rcases hdata with ⟨hat₀,ha₀,hai₀,hforw₀,he₀,hes₀,het₀,hef₀,hei₀,hpair₀,
    hadapt₀,hback₀,hforward₀,hbj₀,hfj₀⟩
  have hphase : ∀ z ∈ b.source, (b z).2 0 = psi (z.1,c.symm z.2) := by
    intro z hz
    have ht : z.2 ∈ c.target := (hg.1 hz).2
    have hs : ((0 : E₀),c.symm z.2) ∈ (actualHostAdaptedChart c b₀).source := by
      refine ⟨⟨mem_univ _,c.map_target ht⟩,?_⟩
      change ((0 : E₀),c (c.symm z.2)) ∈ b₀.source
      rwa [c.right_inv ht]
    have hh := (hforw₀ ((0 : E₀),c.symm z.2) hs).2
    change (b₀ ((0 : E₀),c (c.symm z.2))).2 0 = psi₀ (0,c.symm z.2) at hh
    rw [c.right_inv ht] at hh
    exact hh
  obtain ⟨hat,ha,hai,hforw,e,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩ :=
    actual_adapted_chart_original_host c hc psi b hsource hb hbi (fun z _ => rfl) hphase
  refine ⟨e,⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩,?_,?_⟩
  · intro p
    funext y
    rw [hei,hei₀]
    rfl
  · intro p x
    rw [hef,hef₀]
    rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_host_lift
