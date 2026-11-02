import Probes.Round3PreparedParameterSecondaryLift

/-! The actual two supported pullbacks of the produced secondary cutoff
are exactly the original physical parent times the literal scalar cutoff
in its original product chart. This equality includes the zero extension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

theorem increment_actual_secondary_cutoff_literal
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Ref hd hs i r W)
    (theta : P × M → ℝ) (phi : X → ℝ)
    (hSupport : tsupport theta ⊆ (Ref.parameterChart i.2).source ×ˢ (Ref.atlas.chart i.1).source)
    (hCutoff : piece.cutoff = actualHostRefinementCutoff
      (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1))
      (round3ParameterNativeParent (Ref.parameterChart i.2) theta) phi) :
    (round3PreparedParameterSecondaryChoice Ref hd hs i r W piece).cutoff =
      fun z => theta z*phi (Ref.parameterChart i.2 z.1,Ref.atlas.chart i.1 z.2) := by
  funext z
  change round3ParameterSupportedPullback (round3ParameterProductChart (Ref.parameterChart i.2))
    piece.cutoff z = _
  rw [hCutoff]
  by_cases hp : z.1 ∈ (Ref.parameterChart i.2).source
  · have hps : z ∈ (round3ParameterProductChart (M := M) (Ref.parameterChart i.2)).source :=
      ⟨hp,mem_univ _⟩
    rw [round3ParameterSupportedPullback,ite_eq_left hps]
    change actualHostRefinementCutoff _ _ _ (Ref.parameterChart i.2 z.1,z.2) = _
    by_cases hx : z.2 ∈ (Ref.atlas.chart i.1).source
    · have hxs : (Ref.parameterChart i.2 z.1,z.2) ∈
          (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)).source := ⟨mem_univ _,hx⟩
      rw [actualHostRefinementCutoff,ite_eq_left hxs,round3ParameterNativeParent_eq _ _ z hp]
      rfl
    · have hxs : (Ref.parameterChart i.2 z.1,z.2) ∉
          (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1)).source := fun h => hx h.2
      have hzero : theta z = 0 := image_eq_zero_of_notMem_tsupport (fun hz => hx (hSupport hz).2)
      rw [actualHostRefinementCutoff,ite_eq_right hxs,hzero,zero_mul]
  · have hps : z ∉ (round3ParameterProductChart (M := M) (Ref.parameterChart i.2)).source := fun h => hp h.1
    have hzero : theta z = 0 := image_eq_zero_of_notMem_tsupport (fun hz => hp (hSupport hz).1)
    rw [round3ParameterSupportedPullback,ite_eq_right hps,hzero,zero_mul]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_secondary_cutoff_literal
