import Probes.ActualQuantitativeAdaptedRefinement
import Probes.ActualNormalHessianTransition
import GlobalEmbedding.Paper.IncrementsParametricChartSlices

/-!
# Actual produced phase charts in the original manifold chart

The quantitative native chart is composed with the actual original host chart.
The same joint chart is sliced; both genuine source-chart transitions and all
of their ambient joint derivatives are identified with the produced native
chart and its inverse. No supplied slice or transition identity is required.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

def actualOriginalHostJointChart (c : OpenPartialHomeomorph M D) :
    OpenPartialHomeomorph (Ep × M) X := (OpenPartialHomeomorph.refl Ep).prod c

def actualHostAdaptedChart (c : OpenPartialHomeomorph M D)
    (b : OpenPartialHomeomorph X X) : OpenPartialHomeomorph (Ep × M) X :=
  (actualOriginalHostJointChart c).trans b

theorem actual_adapted_chart_original_host
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (psi : Ep × M → ℝ) (b : OpenPartialHomeomorph X X)
    (hsource : b.source ⊆ (actualOriginalHostJointChart (Ep := Ep) c).target)
    (hb : ContDiffOn ℝ ∞ b b.source) (hbi : ContDiffOn ℝ ∞ b.symm b.target)
    (hparam : ∀ z ∈ b.source, (b z).1 = z.1)
    (hphase : ∀ z ∈ b.source, (b z).2 0 = psi (z.1,c.symm z.2)) :
    let a := actualHostAdaptedChart c b
    a.target = b.target ∧
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ a a.source ∧
    ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ a.symm a.target ∧
    (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = psi z) ∧
    ∃ e : Ep → OpenPartialHomeomorph M D,
      (∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M) ∧
      (∀ p, (e p).source = {x | (p,x) ∈ a.source}) ∧
      (∀ p, (e p).target = {y | (p,y) ∈ b.target}) ∧
      (∀ p x, e p x = (a (p,x)).2) ∧
      (∀ p y, (e p).symm y = (a.symm (p,y)).2) ∧
      (∀ z ∈ b.target, a.symm z = (z.1,(e z.1).symm z.2)) ∧
      (∀ z ∈ b.target, psi (z.1,(e z.1).symm z.2) = z.2 0) ∧
      EqOn (actualSourceChartTransition (fun _ => c) e) b.symm b.target ∧
      EqOn (actualSourceChartTransition e (fun _ => c)) b b.source ∧
      (∀ k z, z ∈ b.target →
        iteratedFDeriv ℝ k (actualSourceChartTransition (fun _ => c) e) z =
          iteratedFDeriv ℝ k b.symm z) ∧
      (∀ k z, z ∈ b.source →
        iteratedFDeriv ℝ k (actualSourceChartTransition e (fun _ => c)) z =
          iteratedFDeriv ℝ k b z) := by
  let q := actualOriginalHostJointChart (Ep := Ep) c
  let a := actualHostAdaptedChart c b
  have hatarget : a.target = b.target := by
    ext z
    change (z ∈ b.target ∧ b.symm z ∈ q.target) ↔ z ∈ b.target
    exact ⟨fun h => h.1,fun hz => ⟨hz,hsource (b.map_target hz)⟩⟩
  have hq : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ q q.source := by
    have hcs : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓙 ∞
        (fun z : Ep × M => c z.2) q.source :=
      (contMDiffOn_of_mem_maximalAtlas hc).comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2)
    exact contMDiffOn_fst.prodMk_space hcs
  have hqi : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ q.symm q.target := by
    have hcs : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞ (fun z : X => c.symm z.2) q.target :=
      (contMDiffOn_symm_of_mem_maximalAtlas hc).comp contDiff_snd.contMDiff.contMDiffOn
        (fun _ hz => hz.2)
    exact contDiff_fst.contMDiff.contMDiffOn.prodMk hcs
  have ha : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ a a.source :=
    hb.contMDiffOn.comp (hq.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  have hai : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ a.symm a.target :=
    hqi.comp (hbi.contMDiffOn.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  have hforw : ∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = psi z := by
    intro z hz
    refine ⟨hparam (q z) hz.2,?_⟩
    change (b (q z)).2 0 = psi z
    rw [hphase (q z) hz.2]
    change psi (z.1,c.symm (c z.2)) = psi z
    rw [c.left_inv hz.1.2]
  obtain ⟨e,hes,het,hef,hei,he,hjoint,hpair,hmap,hadapt⟩ :=
    incrementsParametricChart_slices a (fun p x => psi (p,x))
      (fun z hz => (hforw z hz).1) (fun z hz => (hforw z hz).2) ha hai
  have hbackparam (z : X) (hz : z ∈ b.target) : (b.symm z).1 = z.1 := by
    rw [← hparam (b.symm z) (b.map_target hz),b.right_inv hz]
  have heback : EqOn (actualSourceChartTransition (fun _ => c) e) b.symm b.target := by
    intro z hz
    have hhost := hsource (b.map_target hz)
    apply Prod.ext
    · exact (hbackparam z hz).symm
    · change c ((e z.1).symm z.2) = (b.symm z).2
      rw [hei]
      change c (c.symm (b.symm z).2) = (b.symm z).2
      exact c.right_inv hhost.2
  have heforward : EqOn (actualSourceChartTransition e (fun _ => c)) b b.source := by
    intro z hz
    have hhost := hsource hz
    apply Prod.ext
    · exact (hparam z hz).symm
    · change e z.1 (c.symm z.2) = (b z).2
      rw [hef]
      change (b (z.1,c (c.symm z.2))).2 = (b z).2
      rw [c.right_inv hhost.2]
  refine ⟨hatarget,ha,hai,hforw,e,he,hes,?_,hef,hei,?_,?_,heback,heforward,?_,?_⟩
  · intro p
    rw [het,hatarget]
  · intro z hz
    exact hpair z (by rwa [hatarget])
  · intro z hz
    exact hadapt z (by rwa [hatarget])
  · intro k z hz
    exact ((heback.eventuallyEq_of_mem (b.open_target.mem_nhds hz)).iteratedFDeriv ℝ k).eq_of_nhds
  · intro k z hz
    exact ((heforward.eventuallyEq_of_mem (b.open_source.mem_nhds hz)).iteratedFDeriv ℝ k).eq_of_nhds

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_adapted_chart_original_host
