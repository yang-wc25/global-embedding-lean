import NormalPolar.PassiveOriginalProfile
import GlobalEmbedding.Paper.IncrementsOriginalReserveInputs

/-! The actual linear tensor functionals are evaluated on the same genuine
symmetric coordinate tensors after passive extension. Their original joint
smoothness and weighted core budget follow from this identity; no skew
extension or independently supplied coefficients are introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {n d N : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S] [TopologicalSpace P]

variable (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
  (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
  (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
  (b₀ : Fin seed.parameterCount)

theorem passiveOriginal_linearArgumentCoordinates (l : Fin seed.primaryCount)
    (i : Fin seed.atlas.count × Fin B.count) (y : Fin (n+d) → ℝ) :
    incrementsOriginalLinearArgumentCoordinates (passiveOriginalData s₀ seed B Q) l i y =
      incrementsOriginalLinearArgumentCoordinates seed l (i.1,b₀)
        (passiveOriginalSourceProjection y) := by
  unfold incrementsOriginalLinearArgumentCoordinates
  rw [passiveOriginal_jointPoint s₀ seed B b₀]
  rfl

theorem passiveOriginalData_linearSmooth
    (h : IncrementsOriginalLinearSmoothInputs seed) (hs₀ : s₀ ∈ seed.parameterOpen)
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target) :
    IncrementsOriginalLinearSmoothInputs (passiveOriginalData s₀ seed B Q) := by
  constructor
  intro l i
  change Fin seed.primaryCount at l
  change Fin seed.atlas.count × Fin B.count at i
  let L := passiveOriginalSourceProjection (n := n) (d := d)
  have hmap : MapsTo L
      (incrementsOriginalPrimaryDifferentiation (passiveOriginalData s₀ seed B Q) l i ∩
        (incrementsOriginalJointPoint seed.atlas B.chart i) ⁻¹'
          incrementsOriginalParameterRegion (passiveOriginalData s₀ seed B Q))
      (incrementsOriginalPrimaryDifferentiation seed l (i.1,b₀) ∩
        (incrementsOriginalJointPoint seed.atlas seed.parameterChart (i.1,b₀)) ⁻¹'
          incrementsOriginalParameterRegion seed) := by
    intro y hy
    refine ⟨passiveOriginal_primaryDifferentiation_projection s₀ seed B Q b₀ hb₀ l i hy.1,?_⟩
    change incrementsOriginalJointPoint seed.atlas seed.parameterChart (i.1,b₀)
      (passiveOriginalSourceProjection (d := d) y)
      ∈ incrementsOriginalParameterRegion seed
    rw [passiveOriginal_jointPoint s₀ seed B b₀ i y]
    exact ⟨hs₀,mem_univ _⟩
  have hh := (h.linear_coordinates l (i.1,b₀)).comp L.contDiff.contDiffOn hmap
  apply hh.congr
  intro y hy
  exact passiveOriginal_linearArgumentCoordinates s₀ seed B Q b₀ l i y

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) S]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin 0)) ∞ S]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem passiveOriginal_linear_profile_le
    (hb₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ (seed.parameterChart b₀).target)
    (hQ₀ : (0 : EuclideanSpace ℝ (Fin 0)) ∈ seed.parameterNormDomain b₀)
    (hs₀ : s₀ ∈ seed.parameterSet) (hPrimary : ∀ l, IsOpen (seed.primaryDomain l))
    (j : ℕ) (ell : ℝ) :
    incrementsOriginalInputProfileWithLinear (passiveOriginalData s₀ seed B Q) j ell ≤
      incrementsOriginalInputProfileWithLinear seed j ell := by
  apply max_le_max
  · exact passiveOriginal_core_profile_le s₀ seed B Q b₀ hb₀ hQ₀ hs₀ hPrimary j ell
  · apply iSup_mono
    intro l
    change Fin seed.primaryCount at l
    have he : incrementsOriginalLinearArgumentCoordinates (passiveOriginalData s₀ seed B Q) l =
        fun i => incrementsOriginalLinearArgumentCoordinates seed l (i.1,b₀)
          ∘ passiveOriginalSourceProjection (d := d) := by
      funext i y
      exact passiveOriginal_linearArgumentCoordinates s₀ seed B Q b₀ l i y
    rw [he]
    exact passiveOriginal_primary_weighted_le s₀ seed B Q b₀ hb₀ hQ₀ hs₀ hPrimary l 0 j ell _

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginalData_linearSmooth
#print axioms GlobalEmbedding.Continuation.passiveOriginal_linear_profile_le
