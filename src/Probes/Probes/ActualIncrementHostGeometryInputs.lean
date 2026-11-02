import Probes.ActualOriginalHostRefinement
import Probes.ActualIncrementReserveAdmissibility

/-! Consume the SAME actual host refinement and its literal slices. Smooth
transitions, overlap domains and phase adaptation are derived, rather than
supplied a second time as unrelated geometry assumptions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

theorem actual_host_slice_geometry_inputs
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D) (hdata : ActualOriginalHostSliceData c b psi e) :
    b.source ⊆ (actualOriginalHostJointChart (Ep := Ep) c).target ∧
    ContDiffOn ℝ ∞ b b.source ∧ ContDiffOn ℝ ∞ b.symm b.target ∧
    (∀ z ∈ b.target, z.2 ∈ (e z.1).target ∧ (e z.1).symm z.2 ∈ c.source) ∧
    ContDiffOn ℝ ∞ (actualSourceChartTransition (fun _ => c) e) b.target ∧
    ContDiffOn ℝ ∞ (actualSourceChartTransition e (fun _ => c)) b.source ∧
    MapsTo (actualSourceChartTransition (fun _ => c) e) b.target b.source ∧
    (∀ z ∈ b.target, psi (z.1,(e z.1).symm z.2) = z.2 0) := by
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  let q := actualOriginalHostJointChart (Ep := Ep) c
  let a := actualHostAdaptedChart c b
  have hsource : b.source ⊆ q.target := by
    intro z hz
    have ht : b z ∈ a.target := by rw [hat]; exact b.map_source hz
    have hh : b.symm (b z) ∈ q.target := ht.2
    simpa only [b.left_inv hz] using hh
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
  have hqa : MapsTo q.symm b.source a.source := by
    intro z hz
    refine ⟨q.map_target (hsource hz),?_⟩
    change q (q.symm z) ∈ b.source
    rwa [q.right_inv (hsource hz)]
  have hb : ContDiffOn ℝ ∞ b b.source := by
    have hh := (ha.comp (hqi.mono hsource) hqa).contDiffOn
    apply hh.congr
    intro z hz
    change b z = b (q (q.symm z))
    rw [q.right_inv (hsource hz)]
  have hbi : ContDiffOn ℝ ∞ b.symm b.target := by
    have hh := (hq.comp (hai.mono (by rw [hat]))
      (fun z (hz : z ∈ b.target) => (a.map_target (by rwa [hat])).1)).contDiffOn
    apply hh.congr
    intro z hz
    change b.symm z = q (q.symm (b.symm z))
    rw [q.right_inv (hsource (b.map_target hz))]
  refine ⟨hsource,hb,hbi,?_,hbi.congr hback,hb.congr hforward,?_,hadapt⟩
  · intro z hz
    refine ⟨?_,?_⟩
    · rw [het]
      exact hz
    · rw [hei]
      exact c.map_target (hsource (b.map_target hz)).2
  · intro z hz
    rw [hback hz]
    exact b.map_target hz

theorem actual_host_slice_source_point
    (c : OpenPartialHomeomorph M D) (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D) (hdata : ActualOriginalHostSliceData c b psi e)
    (z : X) (hz : z ∈ b.target) :
    (z.1,(e z.1).symm z.2) ∈ (actualHostAdaptedChart c b).source := by
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  rw [← hpair z hz]
  exact (actualHostAdaptedChart c b).map_target (by rwa [hat])

theorem actual_joint_spatial_jacobian_norm_le
    (b : X → X) (O : Set X) (hO : IsOpen O) (hb : ContDiffOn ℝ ∞ b O)
    (z : X) (hz : z ∈ O) :
    ‖actualJointSpatialJacobian b z‖ ≤ ‖fderiv ℝ b z‖ := by
  have hs := spatial_first_jet_le hO hb.snd hz 0
  simp only [norm_iteratedFDeriv_zero] at hs
  rw [norm_iteratedFDeriv_one] at hs
  have hp := (ContinuousLinearMap.snd ℝ Ep D).norm_iteratedFDeriv_comp_left
    (hb.contDiffAt (hO.mem_nhds hz)) (n := 1) (by simp)
  rw [norm_iteratedFDeriv_one,norm_iteratedFDeriv_one] at hp
  exact hs.trans (hp.trans (mul_le_of_le_one_left (norm_nonneg _)
    (ContinuousLinearMap.norm_snd_le ℝ Ep D)))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_host_slice_geometry_inputs
#print axioms GlobalEmbedding.Continuation.actual_host_slice_source_point
#print axioms GlobalEmbedding.Continuation.actual_joint_spatial_jacobian_norm_le
