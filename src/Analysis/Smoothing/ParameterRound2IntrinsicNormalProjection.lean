import Probes.ActualOriginalReferenceNormalPreparation

/-! The actual pair of orthogonal frame projections is the intrinsic
projection onto the normal vectors free on the original phase kernel.
Consequently the constructed raw and unit normal use one physical field,
independently of the chosen adapted chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

section Projection
variable {N : ℕ} {E T : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem parameterRound2_actual_free_normal_projection_eq_intrinsic
    (A : E →L[ℝ] V) (B : T →L[ℝ] V) (v : V)
    (hRange : LinearMap.range B.toLinearMap ≤ (LinearMap.range A.toLinearMap)ᗮ) :
    actualFreeNormalProjectionRaw A B v =
      ((LinearMap.range A.toLinearMap)ᗮ ⊓ (LinearMap.range B.toLinearMap)ᗮ).starProjection v := by
  let PA := (LinearMap.range A.toLinearMap)ᗮ.starProjection v
  have hm := actual_free_normal_projection_mem A B v hRange
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hm
  intro w hw
  have ha := (LinearMap.range A.toLinearMap)ᗮ.starProjection_inner_eq_zero v w hw.1
  have hb := (LinearMap.range B.toLinearMap)ᗮ.starProjection_inner_eq_zero PA w hw.2
  change inner ℝ (PA-actualFreeNormalProjectionRaw A B v) w = 0 at hb
  calc
    inner ℝ (v-actualFreeNormalProjectionRaw A B v) w =
        inner ℝ (v-PA) w + inner ℝ (PA-actualFreeNormalProjectionRaw A B v) w := by
      rw [← inner_add_left]
      congr 1
      abel
    _ = 0 := by rw [ha,hb,add_zero]
end Projection

variable {m N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

def parameterRound2_intrinsicPhaseCovector (psi : M → ℝ) (x : M) :
    TangentSpace 𝓙 x →L[ℝ] ℝ :=
  (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi x)).toContinuousLinearMap.comp
    (mfderiv 𝓙 𝓘(ℝ,ℝ) psi x)

def parameterRound2_intrinsicPhaseFreeSpace
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F) (psi : M → ℝ) (x : M) : Submodule ℝ V where
  carrier := {v | v ∈ normalSpace (I := 𝓙) F x ∧
    ∀ u w : (parameterRound2_intrinsicPhaseCovector psi x).ker,
      inner ℝ ((trueSecondForm F hF x
        (symmetricSquareProduct (TangentSpace 𝓙 x) u.val w.val)) : V) v = 0}
  zero_mem' := ⟨Submodule.zero_mem _,by simp⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨Submodule.add_mem _ ha.1 hb.1,?_⟩
    intro u w
    rw [inner_add_right,ha.2 u w,hb.2 u w,add_zero]
  smul_mem' := by
    intro r a ha
    refine ⟨Submodule.smul_mem _ r ha.1,?_⟩
    intro u w
    rw [inner_smul_right,ha.2 u w,mul_zero]

theorem parameterRound2_intrinsic_phase_free_space_eq_chart
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F)
    (psi : M → ℝ) (e : OpenPartialHomeomorph M D)
    (he : e ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ e.target)
    (x : D) (hx : x ∈ O)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) psi (e.symm x))
    (hadapt : ∀ y ∈ O, psi (e.symm y) = y 0) :
    parameterRound2_intrinsicPhaseFreeSpace F hF psi (e.symm x) =
      (LinearMap.range (fderiv ℝ (F ∘ e.symm) x).toLinearMap)ᗮ ⊓
      (LinearMap.range (incrementsModeAmbientTransverseFrame F hF e.symm x).toLinearMap)ᗮ := by
  let beta := incrementsTransversePairing F hF (e.symm x)
    (fun a : Fin m => incrementsModeCoordinateDirections e.symm x a.succ)
  have hn := actual_increment_normalSpace_eq_chart_range F hF e he x (hOt hx)
  ext v
  constructor
  · intro hv
    have hnormal : v ∈ normalSpace (I := 𝓙) F (e.symm x) := hv.1
    let normal : normalSpace (I := 𝓙) F (e.symm x) := ⟨v,hnormal⟩
    have hb : beta normal = 0 := actual_increment_transverse_kernel_of_phase_free
      F hF psi e he O hO hOt x hx hpsi hadapt normal hv.2
    refine ⟨?_,?_⟩
    · rwa [← hn]
    · apply (Submodule.mem_orthogonal _ _).mpr
      rintro w ⟨t,rfl⟩
      rw [incrementsModeAmbientTransverseFrame_eq]
      change inner ℝ (beta.adjoint t) normal = 0
      rw [beta.adjoint_inner_left,hb,inner_zero_right]
  · intro hv
    have hnormal : v ∈ normalSpace (I := 𝓙) F (e.symm x) := by
      rw [hn]
      exact hv.1
    let normal : normalSpace (I := 𝓙) F (e.symm x) := ⟨v,hnormal⟩
    have hb : beta normal = 0 := actual_original_normal_beta_of_frame_orthogonal
      F hF e.symm x normal hv.2
    exact ⟨hnormal,actual_increment_phase_free_of_transverse_kernel F hF psi e he O hO hOt
      x hx hpsi hadapt normal hb⟩

theorem parameterRound2_actual_normal_raw_eq_intrinsic
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F)
    (psi : M → ℝ) (e : OpenPartialHomeomorph M D)
    (he : e ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ e.target)
    (x : D) (hx : x ∈ O)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) psi (e.symm x))
    (hadapt : ∀ y ∈ O, psi (e.symm y) = y 0) (v : V) :
    actualFreeNormalProjectionRaw (fderiv ℝ (F ∘ e.symm) x)
      (incrementsModeAmbientTransverseFrame F hF e.symm x) v =
      (parameterRound2_intrinsicPhaseFreeSpace F hF psi (e.symm x)).starProjection v := by
  have hRange : LinearMap.range (incrementsModeAmbientTransverseFrame F hF e.symm x).toLinearMap ≤
      (LinearMap.range (fderiv ℝ (F ∘ e.symm) x).toLinearMap)ᗮ := by
    rintro w ⟨t,rfl⟩
    rw [← actual_increment_normalSpace_eq_chart_range F hF e he x (hOt hx)]
    rw [incrementsModeAmbientTransverseFrame_eq]
    exact ((incrementsTransversePairing F hF (e.symm x)
      (fun a : Fin m => incrementsModeCoordinateDirections e.symm x a.succ)).adjoint t).property
  rw [parameterRound2_actual_free_normal_projection_eq_intrinsic _ _ v hRange]
  exact congrArg (fun U : Submodule ℝ V => U.starProjection v)
    (parameterRound2_intrinsic_phase_free_space_eq_chart F hF psi e he O hO hOt x hx hpsi hadapt).symm

#print axioms parameterRound2_actual_free_normal_projection_eq_intrinsic
#print axioms parameterRound2_intrinsic_phase_free_space_eq_chart
#print axioms parameterRound2_actual_normal_raw_eq_intrinsic
end GlobalEmbedding.Continuation
