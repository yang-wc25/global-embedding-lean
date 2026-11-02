import Probes.Round4PrescribedModePrincipal
import Probes.ActualPrescribedProbeValue

/-! The actual complete single-mode value response retains the original negative
cosine/sine principal term and the primitive a*(tau/ell) slow error. It reuses
the original full value theorem with the exact singleton-mode source identity. -/
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

theorem round4_actual_single_mode_value_principal_error
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
    let C := actualRealHomogeneousConstant m N 2 order Mg
      (homogeneousSourceConstant m N (2+order+1) MB
        (probeNormalAmplitudeConstant (2+order+1) weight Bchi Bnu)) Mphase
    ∀ (u : Fin p → ℝ) (sine : Bool),
      ‖fderiv ℝ (fun v => W v x) u (Pi.single (label (i,sine)) 1)-
        (if sine then actualProbeSinColumn delta tau weight phase amplitude x
          else actualProbeCosColumn delta tau weight phase amplitude x)‖ ≤
        (delta*tau)*(tau/ell)*C := by
  intro amplitude vf W C u sine
  have hh := actualPrescribedProbe_value_response_bound (round4SingleProbeLabel label i)
    delta tau ell (fun _ : Fin 1 => weight) (fun _ => phase) F hF chart (fun _ => chi) (fun _ => nu)
    order b Ojoint S hOjoint hS (fun _ => hphaseSmooth) hBrow (fun _ => hchi) (fun _ => hnu)
    hA hB hG hJ hT0 MB Mg (fun _ => Bchi) (fun _ => Bnu) (fun _ => Mphase)
    hdelta hell hell1 htau htauell hMB hMg (fun _ => hBchi) (fun _ => hBnu)
    hBrowb (fun _ => hchib) (fun _ => hnub) hAb hBb hGb hJb hT0b (fun _ => hphase) u x hx 0 sine
  have hW := round4_singleton_firstBlock_eq_mode label i delta tau weight phase F hF chart chi nu order b
  rw [hW] at hh
  have hemb : round4SingleProbeLabel label i (0, sine) = label (i, sine) := rfl
  rw [hemb] at hh
  simpa only [Fin.sum_univ_one, W, vf, amplitude, C] using hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_single_mode_value_principal_error
