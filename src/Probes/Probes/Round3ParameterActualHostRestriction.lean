import Probes.ActualIncrementOriginalHostGeometry
import Probes.Round3ParameterCrossHostConjugation

/-! Restrict an actual host chart to a proved PHYSICAL open carrier and
reconstruct its genuine native host/slices. Forward, inverse and every slice
inverse function remain literal. The entire host chart equals the original
chart restricted to that carrier, including actual source and target sets.
No cutoff is changed by this operation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m : ℕ} {Ep M : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_actual_host_source_restriction
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D) (hdata : ActualOriginalHostSliceData c b psi e)
    (G : Set (Ep × M)) (hG : IsOpen G) :
    ∃ (b' : OpenPartialHomeomorph X X) (e' : Ep → OpenPartialHomeomorph M D),
      ActualOriginalHostSliceData c b' psi e' ∧
      (b' : X → X) = b ∧ (b'.symm : X → X) = b.symm ∧
      (∀ p, ((e' p).symm : D → M) = (e p).symm) ∧
      b'.source ⊆ b.source ∧ b'.target ⊆ b.target ∧
      actualHostAdaptedChart c b' = (actualHostAdaptedChart c b).restrOpen G hG ∧
      (∀ w ∈ (actualHostAdaptedChart c b').source, w ∈ G) := by
  let q := actualOriginalHostJointChart (Ep := Ep) c
  let a := actualHostAdaptedChart c b
  let U := q.target ∩ q.symm ⁻¹' G
  have hU : IsOpen U := q.continuousOn_symm.isOpen_inter_preimage q.open_target hG
  let b' := b.restrOpen U hU
  have hGeom := actual_host_slice_geometry_inputs c hc b psi e hdata
  have hSource : b'.source ⊆ q.target := fun z hz => hGeom.1 hz.1
  have hSourcePoint (z : X) (hz : z ∈ b.source) : q.symm z ∈ a.source := by
    refine ⟨q.map_target (hGeom.1 hz),?_⟩
    change q (q.symm z) ∈ b.source
    rwa [q.right_inv (hGeom.1 hz)]
  have hParam : ∀ z ∈ b'.source, (b' z).1 = z.1 := by
    intro z hz
    have hh := (hdata.2.2.2.1 (q.symm z) (hSourcePoint z hz.1)).1
    change (b (q (q.symm z))).1 = z.1 at hh
    rwa [q.right_inv (hGeom.1 hz.1)] at hh
  have hPhase : ∀ z ∈ b'.source, (b' z).2 0 = psi (z.1,c.symm z.2) := by
    intro z hz
    have hh := (hdata.2.2.2.1 (q.symm z) (hSourcePoint z hz.1)).2
    change (b (q (q.symm z))).2 0 = psi (z.1,c.symm z.2) at hh
    rwa [q.right_inv (hGeom.1 hz.1)] at hh
  obtain ⟨hat,ha,hai,hforw,e',he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩ :=
    actual_adapted_chart_original_host c hc psi b' hSource
      (hGeom.2.1.mono (fun _ hz => hz.1)) (hGeom.2.2.1.mono (fun _ hz => hz.1)) hParam hPhase
  have hChart : actualHostAdaptedChart c b' = a.restrOpen G hG := by
    apply OpenPartialHomeomorph.ext
    · intro w; rfl
    · intro w; rfl
    · ext w
      constructor
      · rintro ⟨hwq,hwb⟩
        refine ⟨⟨hwq,hwb.1⟩,?_⟩
        have hh : q.symm (q w) ∈ G := hwb.2.2
        rwa [q.left_inv hwq] at hh
      · rintro ⟨⟨hwq,hwb⟩,hwG⟩
        refine ⟨hwq,hwb,q.map_source hwq,?_⟩
        change q.symm (q w) ∈ G
        rwa [q.left_inv hwq]
  refine ⟨b',e',⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩,
    rfl,rfl,?_,(fun _ hz => hz.1),(fun _ hz => hz.1),hChart,?_⟩
  · intro p
    funext x
    rw [hei]
    rcases hdata with ⟨_,_,_,_,_,_,_,_,hei0,_,_,_,_,_,_⟩
    exact (hei0 p x).symm
  · intro w hw
    rw [hChart] at hw
    exact hw.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_host_source_restriction
