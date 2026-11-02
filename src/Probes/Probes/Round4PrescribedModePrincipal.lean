import Probes.Round4PrescribedHessianPrincipal
import Probes.Round4PrescribedModeHessian

/-! The primitive principal/slow budget specialized to the actual ONE mode.
This keeps the constant local to the selected legal wave, and serves as the
quantitative input to the genuine global-mode identification. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

private local instance singleHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance singleHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private local instance singleHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := ContinuousLinearMap.toNormedSpace

def round4SingleProbeLabel (label : (Fin r × Bool) ↪ Fin p) (i : Fin r) : (Fin 1 × Bool) ↪ Fin p where
  toFun q := label (i,q.2)
  inj' := by
    intro q q' h
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact congrArg (fun t : Fin r × Bool => t.2) (label.injective h)

theorem round4_singleton_firstBlock_eq_mode
    (label : (Fin r × Bool) ↪ Fin p) (i : Fin r) (delta tau weight : ℝ) (phase : D → ℝ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (chart : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
    (length : ℕ) (b : Ep) :
    actualPrescribedProbeFirstBlock (round4SingleProbeLabel label i) delta tau (fun _ : Fin 1 => weight)
      (fun _ => phase) F hF chart (fun _ => chi) (fun _ => nu) length b =
    round4ActualProbeMode label i (F b) (hF b) (chart b)
      (actualProbeNormalAmplitude F chart chi nu delta tau weight b) (fun y => weight*phase y) tau length := by
  funext u x
  rw [actualPrescribedProbeFirstBlock_eq_sum_actual_modes]
  simp only [Fin.sum_univ_one]
  rfl

theorem round4_actual_single_mode_hessian_principal_error
    (label : (Fin r × Bool) ↪ Fin p) (i : Fin r) (delta tau ell weight : ℝ)
    (phase : D → ℝ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ, V) ∞ (F b))
    (chart : Ep → D → M) (chi : X → ℝ)
    (nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
    (order : ℕ) (b : Ep) (Ojoint : Set X) (S : Set D)
    (hOjoint : IsOpen Ojoint) (hS : ∀ x ∈ S, (b, x) ∈ Ojoint)
    (hphaseSmooth : ContDiffOn ℝ ∞ phase ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hBrow : ContDiffOn ℝ ∞ (fun z : X ↦ fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V)) Ojoint)
    (hchi : ContDiffOn ℝ ∞ chi Ojoint)
    (hnu : ContDiffOn ℝ ∞ (fun z : X ↦ (nu z.1 z.2 : V)) Ojoint)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA (F b) (hF b) (chart b))
      ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB (F b) (hF b) (chart b))
      ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hG : ContDiffOn ℝ ∞ (fun y ↦ freeGramRightInverse (fderiv ℝ (F b ∘ chart b) y))
      ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hJ : ContDiffOn ℝ ∞ (fun y ↦ (normalSpace (I := I) (F b) (chart b y)).subtypeL.comp
      (incrementsModeCoordinateJ (F b) (hF b) (chart b) y)) ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hT0 : ContDiffOn ℝ ∞ (incrementsModeTransverseValue (F b) (chart b))
      ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (MB Mg Bchi Bnu Mphase : ℝ)
    (hdelta : 0 ≤ delta) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (htau : 0 < tau) (htauell : tau ≤ ell) (hMB : 0 ≤ MB) (hMg : 0 ≤ Mg)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hBrowb : ∀ a ≤ 2 + order + 1, ∀ z ∈ Ojoint, ell ^ a * ‖iteratedFDeriv ℝ a
      (fun y : X ↦ fun i : Fin (m + 1) ↦
        (incrementsModeSecondForm (F y.1) (hF y.1) (chart y.1) y.2 0 i : V)) z‖ ≤ MB)
    (hchib : ∀ a, a ≤ 2 + order + 1 → ∀ z ∈ Ojoint,
      ell ^ a * ‖iteratedFDeriv ℝ a chi z‖ ≤ Bchi)
    (hnub : ∀ a, a ≤ 2 + order + 1 → ∀ z ∈ Ojoint,
      ell ^ a * ‖iteratedFDeriv ℝ a (fun y : X ↦ (nu y.1 y.2 : V)) z‖ ≤ Bnu)
    (hAb : ∀ a ≤ 2 + order + 1, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (incrementsModeComplexFirstOrderA (F b) (hF b) (chart b)) y‖ ≤ Mg)
    (hBb : ∀ a ≤ 2 + order + 1, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (incrementsModeComplexFirstOrderB (F b) (hF b) (chart b)) y‖ ≤ Mg)
    (hGb : ∀ a ≤ 2, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (fun z ↦ freeGramRightInverse (fderiv ℝ (F b ∘ chart b) z)) y‖ ≤ Mg)
    (hJb : ∀ a ≤ 2, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (fun z ↦ (normalSpace (I := I) (F b) (chart b z)).subtypeL.comp
        (incrementsModeCoordinateJ (F b) (hF b) (chart b) z)) y‖ ≤ Mg)
    (hT0b : ∀ a ≤ 2, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (incrementsModeTransverseValue (F b) (chart b)) y‖ ≤ Mg)
    (hphase : ∀ a, a < 2 → ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ (a + 1) (fun z ↦ weight * phase z) y‖ ≤ Mphase) 
    (x : D) (hx : x ∈ S) (hw : 0 < weight) :
    let amplitude := fun y => chi (b,y) • (nu b y : V)
    let vf := actualProbeNormalAmplitude F chart chi nu delta tau weight b
    let W := round4ActualProbeMode label i (F b) (hF b) (chart b) vf
      (fun y => weight*phase y) tau order
    let C := round4PrescribedHessianErrorConstant m N order
      (fun _ : Fin 1 => weight) (fun _ => Mphase) (fun _ => Bchi) (fun _ => Bnu) MB Mg 0
    ∀ u : Fin p → ℝ,
      (‖fderiv ℝ (fun w => fderiv ℝ (fderiv ℝ (W w)) x) u
        (Pi.single (label (i,false)) 1)-
        ((delta/tau)*Real.cos (weight*phase x/tau)) • phaseRankOneHessian phase amplitude x‖ ≤
          (delta/tau)*(tau/ell)*C) ∧
      (‖fderiv ℝ (fun w => fderiv ℝ (fderiv ℝ (W w)) x) u
        (Pi.single (label (i,true)) 1)-
        ((delta/tau)*Real.sin (weight*phase x/tau)) • phaseRankOneHessian phase amplitude x‖ ≤
          (delta/tau)*(tau/ell)*C) := by
  intro amplitude vf W C
  have hh := round4_actual_prescribed_hessian_principal_error (round4SingleProbeLabel label i)
    delta tau ell (fun _ : Fin 1 => weight) (fun _ => phase) F hF chart (fun _ => chi) (fun _ => nu)
    order b Ojoint S hOjoint hS (fun _ => hphaseSmooth) hBrow (fun _ => hchi) (fun _ => hnu)
    hA hB hG hJ hT0 MB Mg (fun _ => Bchi) (fun _ => Bnu) (fun _ => Mphase)
    hdelta hell hell1 htau htauell hMB hMg (fun _ => hBchi) (fun _ => hBnu)
    hBrowb (fun _ => hchib) (fun _ => hnub) hAb hBb hGb hJb hT0b (fun _ => hphase) x hx 0 hw
  have hW := round4_singleton_firstBlock_eq_mode label i delta tau weight phase F hF chart chi nu order b
  dsimp only at hh
  rw [hW] at hh
  exact hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_singleton_firstBlock_eq_mode
#print axioms GlobalEmbedding.Continuation.round4_actual_single_mode_hessian_principal_error
