import Probes.Round4PrescribedGlobalWaveSmooth

/-! Actual spatial Hessians of the literal global complete sine/cosine field,
and their native external-parameter derivatives. Smoothness of the actual
columns is derived from primitive chart/source data by the imported endpoint.
The nested continuous-linear-map Hessian is the one consumed by trueSecondForm.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Pspace" => Fin p → ℝ

private local instance globalHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance globalHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance globalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

theorem round4_prescribed_global_hessian_parameter_response
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) W)
    (b : Ep) (obs : D → M) (O : Set D) (hO : IsOpen O)
    (hobs : ContMDiffOn 𝓘(ℝ,D) I ∞ obs O) (hOW : ∀ y ∈ O, (b,obs y) ∈ W)
    (u : Pspace) (x : D) (hx : x ∈ O) :
    let wave := fun v y => round4PrescribedGlobalWave label F hF c vf phase tau length a v (b,obs y)
    let J := probeColumnMap (fun q => fderiv ℝ (fderiv ℝ (wave (Pi.single q 1))) x)
    fderiv ℝ (fderiv ℝ (wave u)) x = J u ∧
      HasFDerivAt (fun v => fderiv ℝ (fderiv ℝ (wave v)) x) J u := by
  intro wave J
  have hj (v : Pspace) := (round4_prescribed_global_observed_jet_response label F hF c vf phase tau length a W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase
    b obs O hO hobs hOW 2 v x hx).1
  have heq (v : Pspace) : fderiv ℝ (fderiv ℝ (wave v)) x = J v := by
    apply ContinuousLinearMap.ext
    intro d
    apply ContinuousLinearMap.ext
    intro e
    have hh := congrArg (fun T => T ![d,e]) (hj v)
    simpa [wave,J,probeColumnMap_apply,ContinuousMultilinearMap.sum_apply,
      ContinuousMultilinearMap.smul_apply,iteratedFDeriv_two_apply,
      Fin.sum_univ_two,sum_apply,smul_apply] using hh
  refine ⟨heq u,?_⟩
  have hf : (fun v => fderiv ℝ (fderiv ℝ (wave v)) x) = J := funext heq
  rw [hf]
  exact J.hasFDerivAt

theorem round4_prescribed_global_hessian_response_column
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (K : Fin r → Set (Ep × M)) (hW : IsOpen W)
    (hK : ∀ l, IsClosed (Subtype.val ⁻¹' K l : Set W)) (hKsource : ∀ l, K l ⊆ (a l).source)
    (hchart : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,X) ∞ (a l) (a l).source)
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hG : ∀ l, ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ c l z.1) z.2)) (a l).target)
    (hJ : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (c l z.1 z.2)).subtypeL.comp
      (incrementsModeCoordinateJ (F z.1) (hF z.1) (c l z.1) z.2)) (a l).target)
    (hT : ∀ l, ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : X => fun k : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 k : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : X => (vf l z.1 z.2 : V)) (a l).target)
    (hinput : ∀ l z, z ∈ (a l).target → z ∈ tsupport (fun w : X => (vf l w.1 w.2 : V)) → (a l).symm z ∈ K l)
    (hphase : ∀ l, ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,ℝ) ∞ (phase l) W)
    (b : Ep) (obs : D → M) (O : Set D) (hO : IsOpen O)
    (hobs : ContMDiffOn 𝓘(ℝ,D) I ∞ obs O) (hOW : ∀ y ∈ O, (b,obs y) ∈ W)
    (u : Pspace) (x : D) (hx : x ∈ O) (q : Fin p) :
    let wave := fun v y => round4PrescribedGlobalWave label F hF c vf phase tau length a v (b,obs y)
    fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (wave v)) x) u (Pi.single q 1) =
      fderiv ℝ (fderiv ℝ (wave (Pi.single q 1))) x := by
  intro wave
  have hh := (round4_prescribed_global_hessian_parameter_response label F hF c vf phase tau length a W K hW hK hKsource hchart hA hB hG hJ hT hBR hvf hinput hphase
    b obs O hO hobs hOW u x hx).2
  rw [hh.fderiv,probeColumnMap_apply]
  simp [Pi.single_apply,wave]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_hessian_parameter_response
#print axioms GlobalEmbedding.Continuation.round4_prescribed_global_hessian_response_column
