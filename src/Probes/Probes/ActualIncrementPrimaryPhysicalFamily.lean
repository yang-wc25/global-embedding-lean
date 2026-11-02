import Probes.ActualIncrementPrimaryPhysicalTensor
import Probes.ActualHomogeneousSource
import Probes.ActualJointHomogeneousParameter
import Probes.ActualSecondaryResidualRegularity

/-! Full joint physical primary residual, with actual free-normal channels.
The literal original oscillatory metric variation equals the fixed native row
operator of the same original finite residual. Joint smoothness is a conclusion;
all spatial normal regularity is produced by the pointwise chosen-chart bridge. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)

theorem actual_primary_physical_error_eq_reduced
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F b))
    (chart : Ep → OpenPartialHomeomorph M D)
    (hchart : ∀ b, chart b ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hOt : ∀ z ∈ O, z.2 ∈ (chart z.1).target)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((chart z.1).symm z.2)))
    (hfree : ∀ z ∈ O,
      let β := incrementsTransversePairing (F z.1) (hF z.1) ((chart z.1).symm z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1).symm z.2 a.succ)
      (β.comp β.adjoint).IsInvertible)
    (vfR vfI : (b : Ep) → (x : D) → normalSpace (I := 𝓙) (F b) ((chart b).symm x))
    (hvfR : ContDiffOn ℝ ∞ (fun z : X => (vfR z.1 z.2 : V)) O)
    (hvfI : ContDiffOn ℝ ∞ (fun z : X => (vfI z.1 z.2 : V)) O)
    (hkernelR : ∀ z ∈ O, incrementsTransversePairing (F z.1) (hF z.1) ((chart z.1).symm z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1).symm z.2 a.succ) (vfR z.1 z.2) = 0)
    (hkernelI : ∀ z ∈ O, incrementsTransversePairing (F z.1) (hF z.1) ((chart z.1).symm z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1).symm z.2 a.succ) (vfI z.1 z.2) = 0)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1).symm z.2 0 i : V)) O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (chart z.1).symm z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (chart z.1).symm z.2) O)
    (tau : ℝ) (htau : 0 < tau) (length : ℕ) :
    let c : Ep → D → M := fun b => (chart b).symm
    let k := fun z : X => actualHomogeneousSource F hF c vfR z +
      Complex.I • actualHomogeneousSource F hF c vfI z
    let alpha := (tau : ℂ)/Complex.I
    let U := fun b => incrementsActualModeSum
      (incrementsModeComplexFirstOrderA (F b) (hF b) (c b))
      (incrementsModeComplexFirstOrderB (F b) (hF b) (c b)) alpha length (fun x => k (b,x))
    let ZR := fun b => incrementsModeFullReconstruction (F b) (hF b) (c b)
      (fun x => incrementsModeRealPart (U b x)) (fun _ _ _ => 0) (vfR b)
    let ZI := fun b => incrementsModeFullReconstruction (F b) (hF b) (c b)
      (fun x => incrementsModeImagPart (U b x)) (fun _ _ _ => 0) (vfI b)
    let WR := fun b x => WithLp.toLp 2 (fun a : Fin N =>
      (Complex.exp (((x 0/tau : ℝ) : ℂ)*Complex.I)*
        ((ZR b x a : ℂ)+Complex.I*(ZI b x a : ℂ))).re)
    let WI := fun b x => WithLp.toLp 2 (fun a : Fin N =>
      (Complex.exp (((x 0/tau : ℝ) : ℂ)*Complex.I)*
        ((ZR b x a : ℂ)+Complex.I*(ZI b x a : ℂ))).im)
    let residual := fun z : X => alpha⁻¹ • U z.1 z.2 +
      incrementsModeComplexReducedOperator (F z.1) (hF z.1) (c z.1) (U z.1) z.2-k z
    let err := fun (z : X) i j => Complex.exp (-((z.2 0/tau : ℝ) : ℂ)*Complex.I)*
      ((incrementsCoordinateMetricVariation (F z.1 ∘ c z.1) (WR z.1) z.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ)+Complex.I*
        (incrementsCoordinateMetricVariation (F z.1 ∘ c z.1) (WI z.1) z.2
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ))
    EqOn err (fun z => actualModeResidualRows (residual z)) O ∧ ContDiffOn ℝ ∞ err O := by
  intro c k alpha U ZR ZI WR WI residual err
  have sourceSmooth (vf : (b : Ep) → (x : D) → normalSpace (I := 𝓙) (F b) (c b x))
      (hvf : ContDiffOn ℝ ∞ (fun z : X => (vf z.1 z.2 : V)) O) :
      ContDiffOn ℝ ∞ (actualHomogeneousSource F hF c vf) O := by
    have hs := (incrementsModeForcingSourcePairing.contDiff.comp_contDiffOn hBR).clm_apply hvf
    have hc := ((2 : ℝ) • incrementsModeComplexInclude).contDiff.comp_contDiffOn hs
    apply hc.congr
    intro z hz
    exact actualHomogeneousSource_eq F hF c vf z
  have hk : ContDiffOn ℝ ∞ k O :=
    (sourceSmooth vfR hvfR).add ((sourceSmooth vfI hvfI).const_smul Complex.I)
  have hU : ContDiffOn ℝ ∞ (fun z : X => U z.1 z.2) O :=
    actual_joint_mode_sum_contDiffOn F hF c k tau length O hO hA hB hk
  have hres : ContDiffOn ℝ ∞ residual O :=
    actual_joint_reduced_residual_contDiffOn F hF c (fun z => U z.1 z.2) k O hO hA hB hU hk alpha
  have heq : EqOn err (fun z => actualModeResidualRows (residual z)) O := by
    intro z hz
    let Ω := (fun x : D => (z.1,x)) ⁻¹' O
    have hΩ : IsOpen Ω := hO.preimage (continuous_const.prodMk continuous_id)
    have ht : Ω ⊆ (chart z.1).target := fun x hx => hOt (z.1,x) hx
    have hi : ∀ x ∈ Ω, Function.Injective
        (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) ((chart z.1).symm x)) := fun x hx => hinj (z.1,x) hx
    have hf : ∀ x ∈ Ω,
        let β := incrementsTransversePairing (F z.1) (hF z.1) ((chart z.1).symm x)
          (fun a : Fin m => incrementsModeCoordinateDirections (chart z.1).symm x a.succ)
        (β.comp β.adjoint).IsInvertible := fun x hx => hfree (z.1,x) hx
    have hr := actual_joint_contDiffOn_slice (fun w : X => (vfR w.1 w.2 : V)) O hvfR z.1
    have hii := actual_joint_contDiffOn_slice (fun w : X => (vfI w.1 w.2 : V)) O hvfI z.1
    have hphys := actual_primary_physical_tensor_eq_reduced (F z.1) (hF z.1) (chart z.1) (hchart z.1)
      Ω hΩ ht hi hf (vfR z.1) (vfI z.1) hr hii
      (fun x hx => hkernelR (z.1,x) hx) (fun x hx => hkernelI (z.1,x) hx)
      (U z.1) (actual_joint_contDiffOn_slice (fun w : X => U w.1 w.2) O hU z.1) tau z.2 hz
    funext i j
    change err z i j = actualModeResidualRows (residual z) i j
    rw [actualModeResidualRows_apply]
    dsimp only at hphys
    simpa only [err,WR,WI,ZR,ZI,residual,k,c,alpha,actualHomogeneousSource] using hphys i j
  exact ⟨heq,(actualModeResidualRows.contDiff.comp_contDiffOn hres).congr heq⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_primary_physical_error_eq_reduced
