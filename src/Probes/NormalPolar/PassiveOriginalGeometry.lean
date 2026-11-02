import NormalPolar.PassiveOriginalData
import GlobalEmbedding.Paper.IncrementsOriginalImmersionInputs
import GlobalEmbedding.Paper.IncrementsOriginalDecompositionInputs
import GlobalEmbedding.Paper.IncrementsOriginalReserveInputs

/-! The original immersion, Euclidean ellipticity, positive decomposition
and uniform square-root reserve survive the actual passive construction with
their original numerical constants and supplied tensor neighborhood. -/

noncomputable section
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {n d₀ d N : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [TopologicalSpace P]

variable (s₀ : S) (seed : IncrementsOriginalNativeData n d₀ N M S)
  (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
  (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))

theorem passiveOriginalData_immersion (h : IncrementsOriginalSliceImmersionInputs seed)
    (hs₀ : s₀ ∈ seed.parameterOpen) :
    IncrementsOriginalSliceImmersionInputs (passiveOriginalData s₀ seed B Q) where
  immersion := fun _ _ => h.immersion s₀ hs₀

theorem passiveOriginalData_ellipticity (c : ℝ)
    (h : IncrementsOriginalCoordinateEllipticityInputs seed c)
    (hs₀ : s₀ ∈ seed.parameterSet) :
    IncrementsOriginalCoordinateEllipticityInputs (passiveOriginalData s₀ seed B Q) c where
  lower_pos := h.lower_pos
  lower := fun _ _ => h.lower s₀ hs₀

theorem passiveOriginalData_decompositionTensor (b : P) (x : M)
    (A : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)) :
    incrementsOriginalDecompositionTensor (passiveOriginalData s₀ seed B Q) b x A =
      incrementsOriginalDecompositionTensor seed s₀ x A := rfl

theorem passiveOriginalData_decomposition
    (h : IncrementsOriginalQualitativeDecompositionInputs seed)
    (hs₀ : s₀ ∈ seed.parameterOpen) :
    IncrementsOriginalQualitativeDecompositionInputs (passiveOriginalData s₀ seed B Q) where
  fiber_open := fun _ _ => h.fiber_open s₀ hs₀
  H_symmetric := fun _ _ => h.H_symmetric s₀ hs₀
  reference_symmetric := fun _ _ => h.reference_symmetric s₀ hs₀
  H_mem := fun _ _ => h.H_mem s₀ hs₀
  reference_mem := fun _ _ => h.reference_mem s₀ hs₀
  decomposition := fun _ _ => h.decomposition s₀ hs₀
  argument_positive := fun _ _ => h.argument_positive s₀ hs₀

theorem passiveOriginalData_reserve [Subsingleton S] (rho : ℝ)
    (h : IncrementsOriginalDecompositionReserveInputs seed rho)
    (hs₀ : s₀ ∈ seed.parameterOpen) (hK : s₀ ∈ seed.parameterSet) :
    IncrementsOriginalDecompositionReserveInputs (passiveOriginalData s₀ seed B Q) rho where
  reserve_pos := h.reserve_pos
  lower := by
    intro l z hz _ A hA
    exact h.lower l (s₀,z.2)
      ((passiveOriginalData_support_iff s₀ seed B Q hs₀ l z.1 z.2).mp hz) hK A hA

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginalData_ellipticity
#print axioms GlobalEmbedding.Continuation.passiveOriginalData_decomposition
#print axioms GlobalEmbedding.Continuation.passiveOriginalData_reserve
