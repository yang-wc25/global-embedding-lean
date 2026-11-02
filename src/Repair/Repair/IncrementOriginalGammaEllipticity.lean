import Smoothing.Round4OriginalNativeTensor
import Smoothing.ParameterRound2MetricRegularity

/-!
# Original ellipticity supplies the actual reference tensor lower bound

The original ordered tensor coefficients reconstruct the induced metric
on the real inverse-chart tangent vectors.  The resulting quadratic form is
exactly the squared norm of the source derivative of the same map.  Thus the
reference factory's tensor lower bound is supplied by the original source
ellipticity; no lower bound for an already constructed tensor is assumed.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {n d N c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]

local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "I" => 𝓘(ℝ,Es)

/-- Bilinear equality on the literal spatial chart target.  The parameter
coordinate is unchanged and no parameter differentiability is used. -/
theorem increment_original_gamma_native_apply
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (F : P × M → Ey)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,Ey) ∞ (fun x => F (p,x)))
    (i : Fin A.count × Fin c) (z : Ep × Es)
    (hz : z.2 ∈ (A.chart i.1).target) (v w : Es) :
    round4OriginalNativeTensorCoordinates A B
      (fun p x => inducedMetric («I» := I) (fun y => F (p,y)) x) i z v w =
    inner ℝ
      (fderiv ℝ (fun x => F ((B i.2).symm z.1,(A.chart i.1).symm x)) z.2 v)
      (fderiv ℝ (fun x => F ((B i.2).symm z.1,(A.chart i.1).symm x)) z.2 w) := by
  have hpair :
      (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z),
       incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z)) = z :=
    (parameterTensorModelEquiv n d).symm_apply_apply z
  have hp : incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z) = z.1 :=
    congrArg Prod.fst hpair
  have hx : incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z) = z.2 :=
    congrArg Prod.snd hpair
  have h := congrArg (fun Q : LinearMap.BilinForm ℝ Es => Q v w)
    (round4_original_tensor_coordinates_pullback A B
      (fun p x => inducedMetric («I» := I) (fun y => F (p,y)) x) i
      (parameterTensorModelEquiv n d z))
  change round4OriginalNativeTensorCoordinates A B
      (fun p x => inducedMetric («I» := I) (fun y => F (p,y)) x) i z v w =
    inducedMetric («I» := I)
      (fun x => F ((B i.2).symm
        (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z)),x))
      ((A.chart i.1).symm (incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z)))
      (mfderiv I I (A.chart i.1).symm
        (incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z))
        ((tangentSpaceCastModel I
          (incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z))).symm v))
      (mfderiv I I (A.chart i.1).symm
        (incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z))
        ((tangentSpaceCastModel I
          (incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z))).symm w)) at h
  have htarget : incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z) ∈
      (A.chart i.1).target := hx.symm ▸ hz
  have heq := h.trans (parameterRound2_inducedMetric_inverseChart_apply
    (A.chart i.1) (hA.chart_mem i.1)
    (fun x => F ((B i.2).symm
      (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z)),x))
    (hF ((B i.2).symm (incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z))))
    (incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z)) htarget v w)
  simpa only [hp,hx,Function.comp_def] using heq

/-- The actual diagonal metric coefficient is the squared norm of the
original spatial derivative, with precisely the same coordinate point. -/
theorem increment_original_gamma_native_diag
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (F : P × M → Ey)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,Ey) ∞ (fun x => F (p,x)))
    (i : Fin A.count × Fin c) (z : Ep × Es)
    (hz : z.2 ∈ (A.chart i.1).target) (v : Es) :
    round4OriginalNativeTensorCoordinates A B
      (fun p x => inducedMetric («I» := I) (fun y => F (p,y)) x) i z v v =
    ‖fderiv ℝ (fun x => F ((B i.2).symm z.1,(A.chart i.1).symm x)) z.2 v‖ ^ 2 := by
  rw [increment_original_gamma_native_apply A B hA F hF i z hz v v]
  exact real_inner_self_eq_norm_sq _

/-- Factory tensor ellipticity follows directly from the original spatial
ellipticity on the same carrier.  Only literal target membership is needed. -/
theorem increment_original_gamma_tensor_lower
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (F : P × M → Ey)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,Ey) ∞ (fun x => F (p,x)))
    (i : Fin A.count × Fin c) (K : Set (Ep × Es)) (lower : ℝ)
    (hTarget : ∀ z ∈ K, z.2 ∈ (A.chart i.1).target)
    (hLower : ∀ z ∈ K, ∀ v : Es, lower * ‖v‖ ^ 2 ≤
      ‖fderiv ℝ (fun x => F ((B i.2).symm z.1,(A.chart i.1).symm x)) z.2 v‖ ^ 2) :
    ∀ z ∈ K, ∀ v : Es, lower * ‖v‖ ^ 2 ≤
      round4OriginalNativeTensorCoordinates A B
        (fun p x => inducedMetric («I» := I) (fun y => F (p,y)) x) i z v v := by
  intro z hz v
  rw [increment_original_gamma_native_diag A B hA F hF i z (hTarget z hz) v]
  exact hLower z hz v

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.increment_original_gamma_native_apply
#print axioms GlobalEmbedding.Continuation.increment_original_gamma_native_diag
#print axioms GlobalEmbedding.Continuation.increment_original_gamma_tensor_lower
