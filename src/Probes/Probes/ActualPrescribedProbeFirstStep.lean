import Probes.ActualFullProbeHigherBounds
import Probes.ActualPrescribedProbeSource
import Probes.ActualProbeProfileBounds

/-!
# The prescribed actual paired first block, with primitive uniform jets

This single family uses the exact normal amplitude of (8.3), its literal
original real/imaginary mode source, and both channels of the original finite
reconstruction. Primitive true-B, cutoff and normal-field jets produce the
source budgets; the theorem does not assume bounds on a desired source or
correction. It retains all finite dictionary, parameter dimension, solver
order, coordinate norm and original weight factors in one uniform constant.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Manifold Set
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Offline

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-- Free paired values plus the original finite homogeneous corrections for
the actual normal amplitude -(delta*tau)/lambda² chi nu (u₁-i u₂). -/
def actualPrescribedProbeFirstBlock
    (label : (Fin r × Bool) ↪ Fin p) (delta tau : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ, V) ∞ (F b))
    (chart : Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
    (order : ℕ) (b : Ep) (u : Fin p → ℝ) : D → V :=
  actualFiniteProbeWithReconstruction label delta tau weight phase
    (fun l x ↦ chi l (b, x) • (nu l b x : V)) (F b) (hF b) (chart b) order
    (fun l ↦ actualPrescribedProbeSource label l F hF chart (chi l) (nu l) delta tau (weight l) b) u

/-- Literal identification with the two original source channels. -/
theorem actualPrescribedProbeFirstBlock_eq
    (label : (Fin r × Bool) ↪ Fin p) (delta tau : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ, V) ∞ (F b))
    (chart : Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
    (order : ℕ) (b : Ep) (u : Fin p → ℝ) (x : D) :
    actualPrescribedProbeFirstBlock label delta tau weight phase F hF chart chi nu order b u x =
      actualFiniteProbeDisplacement label delta tau weight phase
        (fun l y ↦ chi l (b, y) • (nu l b y : V)) u x +
      ∑ l, actualRealHomogeneousProbe (fun y ↦ weight l * phase l y) (F b) (hF b) (chart b)
        tau order (actualPairedNormalSource label l (F b) (hF b) (chart b)
          (actualProbeNormalAmplitude F chart (chi l) (nu l) delta tau (weight l) b) u) x := by
  simp only [actualPrescribedProbeFirstBlock, actualFiniteProbeWithReconstruction,
    finiteProbeSource_actualPrescribedProbeSource]

/-- The explicit scale-independent constant for the prescribed actual family. -/
def actualPrescribedProbeJetConstant (m N p j order : ℕ)
    (weight Mphase Bchi Bnu : Fin r → ℝ) (MB Mg : ℝ) : ℝ :=
  actualFullProbeJetConstant m N p j order weight Mphase
    (fun l ↦ 2 ^ (j + order + 1) * Bchi l * Bnu l)
    (fun l ↦ homogeneousSourceConstant m N (j + order + 1) MB
      (probeNormalAmplitudeConstant (j + order + 1) (weight l) (Bchi l) (Bnu l))) Mg

/-- Uniform actual jets of the prescribed complete homogeneous first block.
The only source estimates are derived from primitive true-B/chi/nu profiles.
The same constant controls every n≤j and the native parameter derivative
after each such spatial jet, uniformly in the actual parameter u. -/
theorem actualPrescribedProbe_uniform_weighted_jets
    (label : (Fin r × Bool) ↪ Fin p) (delta tau ell : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → D → ℝ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ, V) ∞ (F b))
    (chart : Ep → D → M) (chi : Fin r → X → ℝ)
    (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
    (j order : ℕ) (b : Ep) (Ojoint : Set X) (S : Set D)
    (hOjoint : IsOpen Ojoint) (hS : ∀ x ∈ S, (b, x) ∈ Ojoint)
    (hphaseSmooth : ∀ l, ContDiffOn ℝ ∞ (phase l) ((fun x ↦ (b, x)) ⁻¹' Ojoint))
    (hBrow : ContDiffOn ℝ ∞ (fun z : X ↦ fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V)) Ojoint)
    (hchi : ∀ l, ContDiffOn ℝ ∞ (chi l) Ojoint)
    (hnu : ∀ l, ContDiffOn ℝ ∞ (fun z : X ↦ (nu l z.1 z.2 : V)) Ojoint)
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
    (MB Mg : ℝ) (Bchi Bnu Mphase : Fin r → ℝ)
    (hdelta : 0 ≤ delta) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (htau : 0 < tau) (htauell : tau ≤ ell) (hMB : 0 ≤ MB) (hMg : 0 ≤ Mg)
    (hBchi : ∀ l, 0 ≤ Bchi l) (hBnu : ∀ l, 0 ≤ Bnu l)
    (hBrowb : ∀ a ≤ j + order + 1, ∀ z ∈ Ojoint, ell ^ a * ‖iteratedFDeriv ℝ a
      (fun y : X ↦ fun i : Fin (m + 1) ↦
        (incrementsModeSecondForm (F y.1) (hF y.1) (chart y.1) y.2 0 i : V)) z‖ ≤ MB)
    (hchib : ∀ l a, a ≤ j + order + 1 → ∀ z ∈ Ojoint,
      ell ^ a * ‖iteratedFDeriv ℝ a (chi l) z‖ ≤ Bchi l)
    (hnub : ∀ l a, a ≤ j + order + 1 → ∀ z ∈ Ojoint,
      ell ^ a * ‖iteratedFDeriv ℝ a (fun y : X ↦ (nu l y.1 y.2 : V)) z‖ ≤ Bnu l)
    (hAb : ∀ a ≤ j + order + 1, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (incrementsModeComplexFirstOrderA (F b) (hF b) (chart b)) y‖ ≤ Mg)
    (hBb : ∀ a ≤ j + order + 1, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (incrementsModeComplexFirstOrderB (F b) (hF b) (chart b)) y‖ ≤ Mg)
    (hGb : ∀ a ≤ j, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (fun z ↦ freeGramRightInverse (fderiv ℝ (F b ∘ chart b) z)) y‖ ≤ Mg)
    (hJb : ∀ a ≤ j, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (fun z ↦ (normalSpace (I := I) (F b) (chart b z)).subtypeL.comp
        (incrementsModeCoordinateJ (F b) (hF b) (chart b) z)) y‖ ≤ Mg)
    (hT0b : ∀ a ≤ j, ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ a (incrementsModeTransverseValue (F b) (chart b)) y‖ ≤ Mg)
    (hphase : ∀ l a, a < j → ∀ y ∈ S, ell ^ a *
      ‖iteratedFDeriv ℝ (a + 1) (fun z ↦ weight l * phase l z) y‖ ≤ Mphase l) :
    let C := actualPrescribedProbeJetConstant m N p j order weight Mphase Bchi Bnu MB Mg
    ∀ n ≤ j, ∀ x ∈ S, ∀ u : Fin p → ℝ,
      (tau ^ n * ‖fderiv ℝ (fun w ↦ iteratedFDeriv ℝ n
        (actualPrescribedProbeFirstBlock label delta tau weight phase F hF chart chi nu order b w) x) u‖ ≤
        (delta * tau) * C) ∧
      (tau ^ n * ‖iteratedFDeriv ℝ n
        (actualPrescribedProbeFirstBlock label delta tau weight phase F hF chart chi nu order b u) x‖ ≤
        ‖u‖ * (delta * tau) * C) := by
  let q := j + order + 1
  let O := (fun x ↦ (b, x)) ⁻¹' Ojoint
  have hO : IsOpen O := hOjoint.preimage (continuous_const.prodMk continuous_id)
  have hsource l := actualPrescribedProbeSource_weighted_jets label l F hF chart (chi l) (nu l)
    Ojoint hOjoint hBrow (hchi l) (hnu l) q ell delta tau (weight l) MB (Bchi l) (Bnu l)
    hell.le hdelta htau.le hMB (hBchi l) (hBnu l) hBrowb (hchib l) (hnub l) b
  have hprofile l := actualProbeProfile_weighted_jets (chi l) (fun z : X ↦ (nu l z.1 z.2 : V))
    Ojoint hOjoint (hchi l) (hnu l) q ell (Bchi l) (Bnu l) hell.le (hBchi l) (hBnu l)
    (hchib l) (hnub l)
  have hslice l := fixed_parameter_slice_weighted_jets
    (fun z : X ↦ chi l z • (nu l z.1 z.2 : V)) Ojoint hOjoint (hprofile l).1 q ell
      (2 ^ q * Bchi l * Bnu l) hell.le (hprofile l).2 b
  apply actualFullProbe_uniform_weighted_jets label delta tau ell weight phase
    (fun l x ↦ chi l (b, x) • (nu l b x : V)) (F b) (hF b) (chart b) j order
    (fun l ↦ actualPrescribedProbeSource label l F hF chart (chi l) (nu l) delta tau (weight l) b)
    O S hO hS hphaseSmooth (fun l ↦ (hslice l).1) hA hB hG hJ hT0
    (fun l a ↦ (hsource l).1 a) Mg
    (fun l ↦ 2 ^ q * Bchi l * Bnu l)
    (fun l ↦ homogeneousSourceConstant m N q MB
      (probeNormalAmplitudeConstant q (weight l) (Bchi l) (Bnu l))) Mphase
    hdelta hell hell1 htau htauell hMg
    (fun l ↦ mul_nonneg (mul_nonneg (by positivity) (hBchi l)) (hBnu l))
    (fun l ↦ homogeneousSourceConstant_nonneg m N q hMB
      (probeNormalAmplitudeConstant_nonneg q (weight l) (hBchi l) (hBnu l)))
    hAb hBb hGb hJb hT0b
  · intro l a n hn x hx
    simpa only [mul_assoc] using (hsource l).2 a n hn x (hS x hx)
  · exact hphase
  · intro l n hn x hx
    exact (hslice l).2 n (by dsimp [q]; omega) x (hS x hx)

#print axioms actualPrescribedProbeFirstBlock_eq
#print axioms actualPrescribedProbe_uniform_weighted_jets
end GlobalEmbedding.Offline
