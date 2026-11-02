import GlobalEmbedding.Paper.IncrementsModeFullReconstruction
import GlobalEmbedding.Paper.IncrementsActualReconstructionSupport
import GlobalEmbedding.Paper.IncrementsJointSpatialJets

/-!
# Stage 2: the SAME original finite reconstruction is jointly smooth

Source: `main.tex`, lem:increments594–609,617–650. Exclusive worker W5.
This is a proposed statement ONLY, for ROOT lock. Its single named proof hole
is expected and must not be mistaken for a completed proof or landed provider.
W2 alone owns the joint-to-slice spatial-jet bridge and actual joint geometry.
No new R, Z, J, differential operator, norm or section carrier is defined here.
-/

noncomputable section
open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Cdata" => Fin (m + 1) → ℂ
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ

/-- The literal SAME finite-mode full reconstruction is jointly smooth on the
ORIGINAL open parameter/spatial domain O. Geometry hypotheses refer to actual
per-parameter F/c fields. The source is the original real/imaginary mode source
computed from h/vf, not an arbitrary solution or a supplied output estimate.

Source: main.tex617–650 and the finite-auxiliary-parameter clause607–609.

Natural-language proof, pending ROOT lock: let the native spatial inclusion be
inr : D ->L Ep×D. Apply W2's sole incrementsJointSpatialJets_bridge to actual
jointly smooth iterands, identifying each slice fderiv with full fderiv followed
by inr. Restrict full first jets by fixed CLM composition and then apply the
literal actual A(p,x); B(p,x) and the original computed source are unchanged.
Native CLM composition gives smooth joint coefficients for this full-source
first-order expression. Reuse increments_actual_mode_sum_contDiffOn on Ep×D.
Induction on the SAME finite iterate, using W2's slice identity only on O and
openness to compare derivative germs, identifies this joint finite sum with
the per-parameter incrementsActualModeSum appearing below. This derives joint
u smoothness; it is never a hypothesis. Native fixed real/imaginary channel
CLMs give the two actual tangent inputs. W2's bridge gives joint smoothness
of their literal spatial slice derivatives. The accepted exact transverse T
split and actual G/J/T0 fields then give joint smoothness of the original R.
Native addition/subtraction and the actual fixed h_H selector give the literal
full Z with original free-normal data and factor minus one half. No cutoff is
multiplied onto the output. All identities and derivatives are local to O;
no assertion of joint regularity of arbitrary outside values is used.

This local normed-parameter statement does not construct adapted charts, prove
original joint geometry/admissibility, add a global parameter extension, or
perform the subsequent closed-support pullback. Those remain separate original
input/consumer obligations. Per-p hF is spatial smoothness only, not joint F
regularity outside O. Empty O, parameter dimension zero, m=0, N=0, length zero
and tau=0 are allowed for this regularity statement. -/
theorem incrementsModeFullReconstruction_joint_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : Ep × D → Source)
    (vfR vfI : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (c p x))
    (length : ℕ) (tau : ℝ) (O : Set (Ep × D)) (_hO : IsOpen O)
    (_hG : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (_hJ : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (_hT0 : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (_hA : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (_hB : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (_hhR : ContDiffOn ℝ ∞ hR O) (_hhI : ContDiffOn ℝ ∞ hI O)
    (_hvfR : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ (vfR z.1 z.2 : V)) O)
    (_hvfI : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ (vfI z.1 z.2 : V)) O) :
    let source : Ep × D → Cdata := fun z ↦
      incrementsModeComplexInclude
          (incrementsModeSource (F z.1) (hF z.1) (c z.1)
            (fun x ↦ hR (z.1, x)) (vfR z.1) z.2) +
        Complex.I • incrementsModeComplexInclude
          (incrementsModeSource (F z.1) (hF z.1) (c z.1)
            (fun x ↦ hI (z.1, x)) (vfI z.1) z.2)
    ContDiffOn ℝ ∞ source O →
      let finiteU : Ep → D → Cdata := fun p ↦
        incrementsActualModeSum
          (incrementsModeComplexFirstOrderA (F p) (hF p) (c p))
          (incrementsModeComplexFirstOrderB (F p) (hF p) (c p))
          ((tau : ℂ) / Complex.I) length (fun x ↦ source (p, x))
      ContDiffOn ℝ ∞ (fun z : Ep × D ↦
        incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
          (fun x ↦ incrementsModeRealPart (finiteU z.1 x))
          (fun x ↦ hR (z.1, x)) (vfR z.1) z.2) O ∧
      ContDiffOn ℝ ∞ (fun z : Ep × D ↦
        incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
          (fun x ↦ incrementsModeImagPart (finiteU z.1 x))
          (fun x ↦ hI (z.1, x)) (vfI z.1) z.2) O := by
  let source : Ep × D → Cdata := fun z ↦
    incrementsModeComplexInclude
        (incrementsModeSource (F z.1) (hF z.1) (c z.1)
          (fun x ↦ hR (z.1, x)) (vfR z.1) z.2) +
      Complex.I • incrementsModeComplexInclude
        (incrementsModeSource (F z.1) (hF z.1) (c z.1)
          (fun x ↦ hI (z.1, x)) (vfI z.1) z.2)
  change ContDiffOn ℝ ∞ source O → _
  intro hs
  let A := fun p ↦ incrementsModeComplexFirstOrderA (F p) (hF p) (c p)
  let B := fun p ↦ incrementsModeComplexFirstOrderB (F p) (hF p) (c p)
  let α := (tau : ℂ) / Complex.I
  let finiteU : Ep → D → Cdata := fun p ↦
    incrementsActualModeSum (A p) (B p) α length (fun x ↦ source (p, x))
  have hit (q : ℕ) : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      ((incrementsActualModeStep (A z.1) (B z.1) α)^[q]
        (fun x ↦ source (z.1, x))) z.2) O := by
    induction q with
    | zero => exact hs
    | succ q ih =>
      have hd := (incrementsJointSpatialJets_bridge _ O _hO ih).2.1
      simpa only [Function.iterate_succ_apply', incrementsActualModeStep,
        incrementsActualFirstOrder] using
        ((_hB.clm_apply ih).add (_hA.clm_apply hd)).const_smul (-α)
  have hu : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ finiteU z.1 z.2) O := by
    exact (ContDiffOn.sum fun q _ ↦ hit q).const_smul α
  have hz (u : Ep → D → D)
      (hus : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ u z.1 z.2) O)
      (h : Ep × D → Source) (hh : ContDiffOn ℝ ∞ h O)
      (vf : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (c p x))
      (hvf : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ (vf z.1 z.2 : V)) O) :
      ContDiffOn ℝ ∞ (fun z : Ep × D ↦
        incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
          (u z.1) (fun x ↦ h (z.1, x)) (vf z.1) z.2) O := by
    have hd := (incrementsJointSpatialJets_bridge _ O _hO hus).2.1
    have ht : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
        incrementsModeTransverseTensor (F z.1) (c z.1) (u z.1) z.2) O := by
      exact ((_hT0.clm_apply hus).add (contDiffOn_const.clm_apply hd)).congr
        (fun z _ ↦ incrementsModeTransverseTensor_split (F z.1) (c z.1) (u z.1) z.2)
    have hr : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
        incrementsModeReconstruction (F z.1) (hF z.1) (c z.1) (u z.1) z.2) O :=
      (_hG.clm_apply hus).add (_hJ.clm_apply ht)
    have hsel := incrementsModeTransverseSourceCLM.contDiff.comp_contDiffOn hh
    exact (hr.add hvf).sub ((_hJ.clm_apply hsel).const_smul (1 / 2 : ℝ))
  exact ⟨hz (fun p x ↦ incrementsModeRealPart (finiteU p x))
    (incrementsModeRealPart.contDiff.comp_contDiffOn hu) hR _hhR vfR _hvfR,
    hz (fun p x ↦ incrementsModeImagPart (finiteU p x))
      (incrementsModeImagPart.contDiff.comp_contDiffOn hu) hI _hhI vfI _hvfI⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.incrementsModeFullReconstruction_joint_contDiffOn
