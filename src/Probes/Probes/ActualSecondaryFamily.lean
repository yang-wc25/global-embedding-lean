import Probes.ActualSecondaryModulation
import Probes.ActualSecondarySupport
import Probes.ActualJointHomogeneousParameter

/-!
# One literal actual secondary family

These names expose the same original source, finite polynomial, two full
reconstructions and real oscillatory displacement. They preserve the entire
auxiliary parameter variable. No alternative solver or approximate wave is
introduced; the exponential and sine/cosine presentations agree exactly.
-/

noncomputable section
open Manifold Set GlobalEmbedding.Paper
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ
local notation "Cdata" => Fin (m + 1) → ℂ

def actualSecondaryComplexSource
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) : X → Cdata := fun z =>
  incrementsModeComplexInclude (incrementsModeSource (F z.1) (hF z.1) (c z.1)
    (fun x => hR (z.1, x)) (fun _ => 0) z.2) +
  Complex.I • incrementsModeComplexInclude (incrementsModeSource (F z.1) (hF z.1) (c z.1)
    (fun x => hI (z.1, x)) (fun _ => 0) z.2)

def actualSecondarySolution
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) (tau : ℝ) (length : ℕ) : Ep → D → Cdata :=
  fun p => incrementsActualModeSum
    (incrementsModeComplexFirstOrderA (F p) (hF p) (c p))
    (incrementsModeComplexFirstOrderB (F p) (hF p) (c p)) ((tau : ℂ) / Complex.I) length
    (fun x => actualSecondaryComplexSource F hF c hR hI (p, x))

def actualSecondaryRealChannel
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) (tau : ℝ) (length : ℕ) : X → V := fun z =>
  incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
    (incrementsModeRealPart ∘ actualSecondarySolution F hF c hR hI tau length z.1)
    (fun x => hR (z.1, x)) (fun _ => 0) z.2

def actualSecondaryImagChannel
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) (tau : ℝ) (length : ℕ) : X → V := fun z =>
  incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
    (incrementsModeImagPart ∘ actualSecondarySolution F hF c hR hI tau length z.1)
    (fun x => hI (z.1, x)) (fun _ => 0) z.2

def actualSecondaryWave
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) (phase : X → ℝ)
    (tau : ℝ) (length : ℕ) : X → V :=
  actualSecondaryModulation phase tau
    (actualSecondaryRealChannel F hF c hR hI tau length)
    (actualSecondaryImagChannel F hF c hR hI tau length)

def actualSecondaryComplexRealWave
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) (phase : X → ℝ)
    (tau : ℝ) (length : ℕ) : X → V := fun z => WithLp.toLp 2 (fun a : Fin N =>
  (Complex.exp (((phase z / tau : ℝ) : ℂ) * Complex.I) *
    ((actualSecondaryRealChannel F hF c hR hI tau length z a : ℂ) +
      Complex.I * (actualSecondaryImagChannel F hF c hR hI tau length z a : ℂ))).re)

def actualSecondaryComplexImagWave
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) (phase : X → ℝ)
    (tau : ℝ) (length : ℕ) : X → V := fun z => WithLp.toLp 2 (fun a : Fin N =>
  (Complex.exp (((phase z / tau : ℝ) : ℂ) * Complex.I) *
    ((actualSecondaryRealChannel F hF c hR hI tau length z a : ℂ) +
      Complex.I * (actualSecondaryImagChannel F hF c hR hI tau length z a : ℂ))).im)

theorem actualSecondaryComplexRealWave_eq
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) (phase : X → ℝ)
    (tau : ℝ) (length : ℕ) :
    actualSecondaryComplexRealWave F hF c hR hI phase tau length =
      actualSecondaryWave F hF c hR hI phase tau length := by
  funext z
  exact congrFun (increments_primary_real_mode_eq (fun x => phase (z.1, x)) tau
    (fun x => actualSecondaryRealChannel F hF c hR hI tau length (z.1, x))
    (fun x => actualSecondaryImagChannel F hF c hR hI tau length (z.1, x))) z.2

theorem actualSecondaryComplexSource_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) (O : Set X)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O) :
    ContDiffOn ℝ ∞ (actualSecondaryComplexSource F hF c hR hI) O := by
  have hr := incrementsModeComplexInclude.contDiff.comp_contDiffOn
    (actual_joint_zeroFree_source_contDiffOn F hF c hR O hBR hJ hhR)
  have hi := incrementsModeComplexInclude.contDiff.comp_contDiffOn
    (actual_joint_zeroFree_source_contDiffOn F hF c hI O hBR hJ hhI)
  exact hr.add (hi.const_smul Complex.I)

theorem actualSecondarySolution_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) (tau : ℝ) (length : ℕ)
    (O : Set X) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hk : ContDiffOn ℝ ∞ (actualSecondaryComplexSource F hF c hR hI) O) :
    ContDiffOn ℝ ∞ (fun z : X => actualSecondarySolution F hF c hR hI tau length z.1 z.2) O :=
  actual_joint_mode_sum_contDiffOn F hF c (actualSecondaryComplexSource F hF c hR hI)
    tau length O hO hA hB hk

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualSecondaryComplexRealWave_eq
#print axioms GlobalEmbedding.Continuation.actualSecondaryComplexSource_contDiffOn
#print axioms GlobalEmbedding.Continuation.actualSecondarySolution_contDiffOn
