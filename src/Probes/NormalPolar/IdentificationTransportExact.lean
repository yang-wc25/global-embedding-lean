import NormalPolar.IdentificationTransportProbe

/-!
# Exact transport when the same actual Q has two presentations

Equality is required only on the admitted open parameter domain.  The native
parameter derivative is transported by neighborhood equality of the actual
identified forms in the original fixed chart frame.  The total extensions
outside that domain need not agree.
-/

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The ambient operator determines the actual normal-fiber isometry.
This includes zero-dimensional normal spaces. -/
theorem normalIdentification_eq_of_operator_eq
    (F₀ F : M → V)
    (Q₁ Q₂ : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M)
    (heq : normalIdentificationOperator (n := n) F₀ F Q₁ z =
      normalIdentificationOperator (n := n) F₀ F Q₂ z) :
    Q₁ z = Q₂ z := by
  apply LinearIsometryEquiv.ext
  intro v
  apply Subtype.ext
  have h := congrArg (fun T : V →L[ℝ] V ↦ T (v : V)) heq
  change ((Q₁ z) ((normalSpace (I := IM) F z).orthogonalProjectionOnto (v : V)) : V) =
    ((Q₂ z) ((normalSpace (I := IM) F z).orthogonalProjectionOnto (v : V)) : V) at h
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at h
  exact h

/-- Equality of the actual ambient operators gives equality of the actual
identified true forms, without assumptions on any model of the form. -/
theorem identifiedTrueSecondForm_eq_of_operator_eq
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (Q₁ Q₂ : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M)
    (heq : normalIdentificationOperator (n := n) F₀ F Q₁ z =
      normalIdentificationOperator (n := n) F₀ F Q₂ z) :
    identifiedTrueSecondForm (n := n) F₀ F hF Q₁ z =
      identifiedTrueSecondForm (n := n) F₀ F hF Q₂ z := by
  rw [identifiedTrueSecondForm_eq_normalIdentification_comp,
    identifiedTrueSecondForm_eq_normalIdentification_comp, heq]

/-- A neighborhood equality of actual Qops transports the native derivative
of the same true form in the same fixed source frame. No derivative response
of either Q is assumed. -/
theorem fderiv_framed_identifiedTrueSecondForm_eq_of_eventually_operator_eq
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F₀ : M → V) (F : P → M → V)
    (hF : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (F u))
    (Q₁ Q₂ : ∀ u z, normalSpace (I := IM) (F u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (u : P) (z : M) (frame : E →L[ℝ] E)
    (heq : (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Q₁ v) z) =ᶠ[𝓝 u]
      (fun v ↦ normalIdentificationOperator (n := n) F₀ (F v) (Q₂ v) z)) :
    fderiv ℝ (fun v ↦ probeTensorInFrame frame
      (identifiedTrueSecondForm (n := n) F₀ (F v) (hF v) (Q₁ v) z)) u =
    fderiv ℝ (fun v ↦ probeTensorInFrame frame
      (identifiedTrueSecondForm (n := n) F₀ (F v) (hF v) (Q₂ v) z)) u := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [heq] with v hv
  rw [identifiedTrueSecondForm_eq_of_operator_eq F₀ (F v) (hF v) (Q₁ v) (Q₂ v) z hv]

/-- The same operator on the original admitted domain. The new total normal
field is still an actual normal-space isometry of the very same maps. -/
def SameNormalOperatorOnProbeDomain
    {F₀ : M → V} {r : ℕ} (p : ProbeGeometry (n := n) F₀ r)
    (Q : ∀ t u z, normalSpace (I := IM) (p.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z) : Prop :=
  ∀ t, 0 < t → t < p.threshold → ∀ u, ‖u‖ < p.radius → ∀ z,
    normalIdentificationOperator (n := n) F₀ (p.map t u) (Q t u) z =
      normalIdentificationOperator (n := n) F₀ (p.map t u) (p.normalIdentification t u) z

/-- Joint smoothness is inherited from the same actual operator on the
unchanged product domain, with no regularity premise on its outside extension. -/
theorem sameNormalOperatorOnProbeDomain_smooth
    {F₀ : M → V} {r : ℕ} (p : ProbeGeometry (n := n) F₀ r)
    (Q : ∀ t u z, normalSpace (I := IM) (p.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (hsame : SameNormalOperatorOnProbeDomain p Q) :
    ∀ t, 0 < t → t < p.threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
        (fun w : ProbeParameters r × M ↦ normalIdentificationOperator (n := n) F₀
          (p.map t w.1) (Q t w.1) w.2) (Metric.ball 0 p.radius ×ˢ univ) := by
  intro t ht htt
  apply (p.normalIdentification_smooth t ht htt).congr
  intro w hw
  exact hsame t ht htt w.1 (by simpa using hw.1) w.2

/-- Equality on the open parameter ball gives equality of full native
parameter derivatives in every fixed frame, using only a neighborhood. -/
theorem sameNormalOperatorOnProbeDomain_fderiv
    {F₀ : M → V} {r : ℕ} (p : ProbeGeometry (n := n) F₀ r)
    (Q : ∀ t u z, normalSpace (I := IM) (p.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (hsame : SameNormalOperatorOnProbeDomain p Q)
    (t : ℝ) (ht : 0 < t) (htt : t < p.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < p.radius) (z : M) (frame : E →L[ℝ] E) :
    fderiv ℝ (fun v ↦ probeTensorInFrame frame
      (identifiedTrueSecondForm (n := n) F₀ (p.map t v) (p.slice_smooth t v) (Q t v) z)) u =
    fderiv ℝ (fun v ↦ probeTensorInFrame frame
      (identifiedTrueSecondForm (n := n) F₀ (p.map t v) (p.slice_smooth t v)
        (p.normalIdentification t v) z)) u := by
  apply fderiv_framed_identifiedTrueSecondForm_eq_of_eventually_operator_eq
  have hu' : u ∈ Metric.ball (0 : ProbeParameters r) p.radius := by simpa using hu
  filter_upwards [Metric.isOpen_ball.mem_nhds hu'] with v hv
  exact hsame t ht htt v (by simpa using hv) z

/-- A full original probe with another presentation of precisely the same
admitted normal operator. Its original second-form response and etaB are
transported by the proved local equality of the native derivative. -/
def exactProbeFamilyWithSameNormalOperator
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (Q : ∀ t u z, normalSpace (I := IM) (p.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (hsame : SameNormalOperatorOnProbeDomain p.toProbeGeometry Q) :
    ExactProbeFamily F₀ hF₀ A waves :=
  { p with
    normalIdentification := Q
    normalIdentification_smooth := sameNormalOperatorOnProbeDomain_smooth p.toProbeGeometry Q hsame
    secondForm_response := by
      intro t ht htt u hu l b i x hx
      rw [sameNormalOperatorOnProbeDomain_fderiv p.toProbeGeometry Q hsame
        t ht htt u hu x (probeAtlasFrame A i x)]
      exact p.secondForm_response t ht htt u hu l b i x hx }

/-- Every quantitative datum, including the original etaB and constant,
is retained for an exactly equal operator on the original domain. -/
theorem exactProbeFamilyWithSameNormalOperator_preserves
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (p : ExactProbeFamily F₀ hF₀ A waves)
    (Q : ∀ t u z, normalSpace (I := IM) (p.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (hsame : SameNormalOperatorOnProbeDomain p.toProbeGeometry Q) :
    let pnew := exactProbeFamilyWithSameNormalOperator p Q hsame
    pnew.map = p.map ∧ pnew.radius = p.radius ∧ pnew.threshold = p.threshold ∧
      pnew.weight = p.weight ∧ pnew.constant = p.constant ∧ pnew.etaB = p.etaB ∧
      pnew.etaV = p.etaV ∧ pnew.normalIdentification = Q := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GlobalEmbedding.NormalPolar
