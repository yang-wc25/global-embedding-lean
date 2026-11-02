import NormalPolar.OriginalWaveSeedPieceGeometry
import Probes.ActualOscillatoryRemainder

/-! Two-channel extraction keeps the original paired parameter space. Every
piece of one original label uses the same contractive projection. Finite
recovery of the original principal value/tensor is exact. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline

def originalProbePairProjection {r : ℕ} (l : Fin r) :
    ProbeParameters r →L[ℝ] ProbeParameters 1 :=
  ContinuousLinearMap.pi (fun q : Fin 1 × Bool => ContinuousLinearMap.proj (l,q.2))

theorem originalProbePairProjection_apply {r : ℕ} (l : Fin r)
    (u : ProbeParameters r) (q : Fin 1 × Bool) :
    originalProbePairProjection l u q = u (l,q.2) := rfl

theorem originalProbePairProjection_norm {r : ℕ} (l : Fin r) :
    ‖originalProbePairProjection l‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro q
  exact norm_le_pi_norm u (l,q.2)

theorem originalProbePairProjection_single {r : ℕ} (l : Fin r) (sine : Bool) :
    originalProbePairProjection l (Pi.single (l,sine) 1) =
      Pi.single ((0 : Fin 1),sine) 1 := by
  ext q
  have hq : q = ((0 : Fin 1),q.2) := Prod.ext (Subsingleton.elim _ _) rfl
  rw [hq]
  change (Pi.single (l,sine) (1:ℝ) : ProbeParameters r) (l,q.2) =
    (Pi.single ((0:Fin 1),sine) (1:ℝ) : ProbeParameters 1) (0,q.2)
  simp [Pi.single_apply]

theorem originalProbePairProjection_single_other {r : ℕ} (l k : Fin r)
    (hk : k ≠ l) (sine : Bool) :
    originalProbePairProjection l (Pi.single (k,sine) 1) = 0 := by
  ext q
  change (Pi.single (k,sine) (1:ℝ) : ProbeParameters r) (l,q.2) = 0
  simp [Pi.single_apply,hk]

theorem originalProbePairProjection_response {r : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (l : Fin r) (f : ProbeParameters 1 → Y) (u : ProbeParameters r)
    (hf : DifferentiableAt ℝ f (originalProbePairProjection l u)) (sine : Bool) :
    fderiv ℝ (fun v => f (originalProbePairProjection l v)) u (Pi.single (l,sine) 1) =
      fderiv ℝ f (originalProbePairProjection l u) (Pi.single ((0:Fin 1),sine) 1) := by
  have h := (hf.hasFDerivAt.comp u (originalProbePairProjection l).hasFDerivAt).fderiv
  have he := congrArg (fun L : ProbeParameters r →L[ℝ] Y => L (Pi.single (l,sine) 1)) h
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,originalProbePairProjection_single] using he

theorem originalProbePairProjection_response_other {r : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (l k : Fin r) (hk : k ≠ l) (f : ProbeParameters 1 → Y) (u : ProbeParameters r)
    (hf : DifferentiableAt ℝ f (originalProbePairProjection l u)) (sine : Bool) :
    fderiv ℝ (fun v => f (originalProbePairProjection l v)) u (Pi.single (k,sine) 1) = 0 := by
  have h := (hf.hasFDerivAt.comp u (originalProbePairProjection l).hasFDerivAt).fderiv
  have he := congrArg (fun L : ProbeParameters r →L[ℝ] Y => L (Pi.single (k,sine) 1)) h
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,originalProbePairProjection_single_other l k hk,map_zero] using he

theorem phaseRankOneHessian_finite_sum {E Y J : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [Fintype J] (theta : E → ℝ) (amplitude : J → E → Y) (x : E) :
    phaseRankOneHessian theta (fun y => ∑ j, amplitude j y) x =
      ∑ j, phaseRankOneHessian theta (amplitude j) x := by
  ext v w
  simp [phaseRankOneHessian,ContinuousLinearMap.smulRight_apply,Finset.smul_sum]

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}

theorem OriginalWaveSeedRefinement.sum_piece_principal
    (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (obs : D → M) (y : D) :
    ∑ s, phaseRankOneHessian (w.phase ∘ obs) (d.pieceValue s ∘ obs) y =
      phaseRankOneHessian (w.phase ∘ obs) (w.value ∘ obs) y := by
  rw [← phaseRankOneHessian_finite_sum]
  have he : (fun x => ∑ s, (d.pieceValue s ∘ obs) x) = w.value ∘ obs :=
    funext (fun x => d.sum_pieceValue (obs x))
  rw [he]

theorem OriginalWaveSeedRefinement.sum_piece_value_error
    (d : OriginalWaveSeedRefinement (m := m) F hF w weight)
    (x : M) (response : Fin d.count → V) (c : ℝ) (errors : Fin d.count → ℝ)
    (herror : ∀ s, ‖response s-c • d.pieceValue s x‖ ≤ errors s) :
    ‖(∑ s, response s)-c • w.value x‖ ≤ ∑ s, errors s := by
  rw [← d.sum_pieceValue x,Finset.smul_sum,← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun s _ => herror s))

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.originalProbePairProjection_response
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRefinement.sum_piece_principal
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRefinement.sum_piece_value_error

