import Probes.ActualFirstFramePerturbation

/-! Fixed numerical reserves extend from the active carrier to an open set.
Only domains are selected after the field. The reserve loses exactly a
fixed factor four, so no field-dependent positive constant is introduced. -/

noncomputable section
open Set Function
namespace GlobalEmbedding.Continuation

theorem round3_prepared_fixed_reserve_open
    {Z E V : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : Z → E →L[ℝ] V) (O K : Set Z) (hO : IsOpen O) (hKO : K ⊆ O)
    (hA : ContinuousOn A O) (c : ℝ) (hc : 0 < c)
    (hReserve : ∀ z ∈ K, ∀ v : E, c*‖v‖^2 ≤ ‖A z v‖^2) :
    ∃ U : Set Z, IsOpen U ∧ K ⊆ U ∧ U ⊆ O ∧
      ∀ z ∈ U, ∀ v : E, (c/4)*‖v‖^2 ≤ ‖A z v‖^2 := by
  let neighborhood := fun x : K => O ∩ {z | ‖A z-A x.val‖ < Real.sqrt c/2}
  have hNeighborhood (x : K) : IsOpen (neighborhood x) :=
    ((hA.sub continuousOn_const).norm).isOpen_inter_preimage hO isOpen_Iio
  let U := ⋃ x : K, neighborhood x
  refine ⟨U,isOpen_iUnion hNeighborhood,?_,?_,?_⟩
  · intro x hx
    apply mem_iUnion.mpr
    refine ⟨⟨x,hx⟩,hKO hx,?_⟩
    change ‖A x-A x‖ < Real.sqrt c/2
    rw [sub_self,norm_zero]
    positivity
  · intro z hz
    obtain ⟨x,hx⟩ := mem_iUnion.mp hz
    exact hx.1
  · intro z hz
    obtain ⟨x,hx⟩ := mem_iUnion.mp hz
    exact actual_first_frame_reserve_perturbation (A x.val) (A z) c hc
      (hReserve x.val x.property) hx.2.le

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_fixed_reserve_open
