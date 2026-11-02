import Probes.Round3PreparedParameterSecondaryStablePiece

/-! One C2 tolerance for the entire fixed all-parameter signed packet. The
current stage selects one family of stable domains; every later observer
and derivative order uses these same choices and unchanged reference costs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance signedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

private theorem round3_secondary_stable_finite_positive {A : Type*} [Fintype A]
    (f : A → ℝ) (hf : ∀ a, 0 < f a) : ∃ e : ℝ, 0 < e ∧ ∀ a, e ≤ f a := by
  let s := insert 1 (Finset.univ.image f)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  refine ⟨s.min' hs,?_,fun a => Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ a)))⟩
  have hm := Finset.min'_mem s hs
  rcases Finset.mem_insert.mp hm with h | h
  · rw [h]; norm_num
  · obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp h
    rw [← heq]
    exact hf a

 theorem round3_prepared_parameter_secondary_stable_family
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (hParam : ∀ r i a y, y ∈ (packet.piece r i a).carrier → y.1 ∈ Ref.parameterNormDomain i.2)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (F : P → M → Ey)
      (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ epsilon →
    Nonempty (∀ r i (a : packet.s r i),
      Round3PreparedParameterStableSecondaryPiece Ref hd hs i r _ (packet.piece r i a) F hF) := by
  let A := Sigma (fun r : ActualSecondarySignedRecord (Fin Ref.primaryCount) =>
    Sigma (fun i : Fin Ref.atlas.count × Fin Ref.parameterCount => ↥(packet.s r i)))
  have hEach (a : A) := round3_prepared_parameter_secondary_C2_pointwise Ref hd hs a.2.1 a.1 _
    (packet.piece a.1 a.2.1 a.2.2) hAll (hParam a.1 a.2.1 a.2.2) hF0joint
  choose eps hEps hPoint using hEach
  obtain ⟨epsilon,hepsilon,hEpsilon⟩ := round3_secondary_stable_finite_positive eps hEps
  refine ⟨epsilon,hepsilon,?_⟩
  intro F hFjoint hF S hFinite hBound
  exact ⟨fun r i a => Classical.choice (round3_prepared_parameter_secondary_stable_piece Ref hd hs i r _
    (packet.piece r i a) F hF hFjoint
    (hPoint ⟨r,⟨i,a⟩⟩ F hFjoint hF hFinite (hBound.trans (hEpsilon ⟨r,⟨i,a⟩⟩))))⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_stable_family
