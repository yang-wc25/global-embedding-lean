import Main.GeneralLegalWaveRefinement

/-!
# The precise one-bump absorption reduction

An arbitrary smooth cutoff can be absorbed into its normal field when an
actual permitted bump is one on the whole cutoff support and has a legal
chart domain. These geometric conditions are explicit; this file does not
claim that a single such bump exists for every paper legal wave.

The resulting frozen `LocalLegalWave` has exactly the same phase, global
value field and legal tensor. There is no split of an original parameter
label and no change of weight or fast frequency.
-/

noncomputable section
open Set Function Manifold
open scoped ContDiff Topology Classical

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)

namespace OpenSupportedLegalWave
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}

/-- The actual original tensor, without a bump-shape restriction. -/
def tensor (w : OpenSupportedLegalWave (n := n) F hF) (x : M) :
    SymmetricSquare E →L[ℝ] V :=
  LinearMap.toContinuousLinearMap
    (w.cutoff x • supportedRankLegalVariation
      (mfderiv IM 𝓘(ℝ,ℝ) w.phase x).toLinearMap (w.normal x : V))

/-- Multiplication by the supported smooth cutoff gives a globally smooth
actual value field, even though the normal is only locally smooth. -/
theorem value_contMDiff (w : OpenSupportedLegalWave (n := n) F hF) :
    ContMDiff IM 𝓘(ℝ,V) ∞ w.value := by
  intro x
  by_cases hx : x ∈ tsupport w.cutoff
  · have hdom := w.support_subset hx
    exact (w.cutoff_smooth x).smul
      ((w.normal_smooth x hdom).contMDiffAt (w.domain_open.mem_nhds hdom))
  · apply (contMDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport w.cutoff).isOpen_compl.mem_nhds hx] with y hy
    simp only [value,image_eq_zero_of_notMem_tsupport hy,zero_smul]

/-- This is a conditional reduction with its genuine one-bump geometric
premise displayed, not an existence assertion for that premise. -/
def absorbIntoOneBump (w : OpenSupportedLegalWave (n := n) F hF)
    (center : M) (bump : SmoothBumpFunction IM center)
    (U : Set M) (hU : IsOpen U) (hcenter : center ∈ U)
    (hchart : U ⊆ (chartAt E center).source)
    (hsupport : tsupport (bump : M → ℝ) ⊆ U)
    (hlegal : U ⊆ w.domain) : LocalLegalWave (n := n) F hF where
  center := center
  domain := U
  phase := w.phase
  normal := fun x => w.cutoff x • w.normal x
  cutoff := bump
  domain_open := hU
  center_mem := hcenter
  domain_chart := hchart
  support_subset := hsupport
  phase_smooth := w.phase_smooth.mono hlegal
  normal_smooth := w.value_contMDiff.contMDiffOn
  legal := by
    intro x hx
    exact ⟨(w.legal x (hlegal hx)).1,
      (supportedRankLegalValueSpace (trueSecondForm F hF x)
        (mfderiv IM 𝓘(ℝ,ℝ) w.phase x).toLinearMap).smul_mem
          (w.cutoff x) (w.legal x (hlegal hx)).2⟩

theorem absorbed_phase (w : OpenSupportedLegalWave (n := n) F hF)
    (center : M) (bump : SmoothBumpFunction IM center)
    (U : Set M) (hU : IsOpen U) (hcenter : center ∈ U)
    (hchart : U ⊆ (chartAt E center).source)
    (hsupport : tsupport (bump : M → ℝ) ⊆ U)
    (hlegal : U ⊆ w.domain) :
    (w.absorbIntoOneBump center bump U hU hcenter hchart hsupport hlegal).phase = w.phase := rfl

/-- The extra bump disappears from the complete global value field. -/
theorem absorbed_value (w : OpenSupportedLegalWave (n := n) F hF)
    (center : M) (bump : SmoothBumpFunction IM center)
    (U : Set M) (hU : IsOpen U) (hcenter : center ∈ U)
    (hchart : U ⊆ (chartAt E center).source)
    (hsupport : tsupport (bump : M → ℝ) ⊆ U)
    (hlegal : U ⊆ w.domain)
    (hone : ∀ x ∈ tsupport w.cutoff, bump x = 1) (x : M) :
    (w.absorbIntoOneBump center bump U hU hcenter hchart hsupport hlegal).value x =
      w.value x := by
  by_cases hx : x ∈ tsupport w.cutoff
  · change bump x • (w.cutoff x • (w.normal x : V)) = w.cutoff x • (w.normal x : V)
    rw [hone x hx,one_smul]
  · have hz := image_eq_zero_of_notMem_tsupport (f := w.cutoff) hx
    change bump x • (w.cutoff x • (w.normal x : V)) = w.cutoff x • (w.normal x : V)
    simp only [hz,zero_smul,smul_zero]

/-- The principal second-form tensor also agrees exactly; no frequency
or scalar normalization is changed by absorbing the cutoff. -/
theorem absorbed_tensor (w : OpenSupportedLegalWave (n := n) F hF)
    (center : M) (bump : SmoothBumpFunction IM center)
    (U : Set M) (hU : IsOpen U) (hcenter : center ∈ U)
    (hchart : U ⊆ (chartAt E center).source)
    (hsupport : tsupport (bump : M → ℝ) ⊆ U)
    (hlegal : U ⊆ w.domain)
    (hone : ∀ x ∈ tsupport w.cutoff, bump x = 1) (x : M) :
    (w.absorbIntoOneBump center bump U hU hcenter hchart hsupport hlegal).tensor x =
      w.tensor x := by
  apply ContinuousLinearMap.ext
  intro q
  change bump x • (supportedRankCovectorSquare
      (mfderiv IM 𝓘(ℝ,ℝ) w.phase x).toLinearMap q •
        (w.cutoff x • (w.normal x : V))) =
    w.cutoff x • (supportedRankCovectorSquare
      (mfderiv IM 𝓘(ℝ,ℝ) w.phase x).toLinearMap q • (w.normal x : V))
  by_cases hx : x ∈ tsupport w.cutoff
  · rw [hone x hx,one_smul]
    exact smul_comm _ _ _
  · have hz := image_eq_zero_of_notMem_tsupport (f := w.cutoff) hx
    simp only [hz,zero_smul,smul_zero]

end OpenSupportedLegalWave
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.OpenSupportedLegalWave.value_contMDiff
#print axioms GlobalEmbedding.Continuation.OpenSupportedLegalWave.absorbIntoOneBump
#print axioms GlobalEmbedding.Continuation.OpenSupportedLegalWave.absorbed_value
#print axioms GlobalEmbedding.Continuation.OpenSupportedLegalWave.absorbed_tensor
