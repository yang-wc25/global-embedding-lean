import GlobalEmbedding.Paper.IncrementsCoordinateGramGeometry
import GlobalEmbedding.Paper.NormalProjectionGramFormula

/-!
# The actual true second form under a fixed induced metric

Source: the final paragraph in the proof of prop:probes. The connection is
constructed from the native first and second derivatives of the actual map.
Its equality for maps with the same metric germ is proved from the original
Koszul identity. Thus the ambient formula B=D2F-DF Gamma(h0) is a theorem about
the original trueSecondForm, not a replacement second-form definition or an
assumed connection derivative identity.
-/
noncomputable section
open Filter Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Offline

variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual induced connection as a continuous bilinear map. Its values
are the native Gram-inverse tangential Hessian coefficients. -/
def probeInducedConnection (f : E → V) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  let A := fderiv ℝ f x
  (ContinuousLinearMap.compL ℝ E V E ((A.adjoint.comp A).inverse.comp A.adjoint)).comp
    (fderiv ℝ (fderiv ℝ f) x)

/-- The connection is exactly the actual Gram-inverse Hessian coefficient. -/
theorem probeInducedConnection_apply (f : E → V) (x v w : E) :
    probeInducedConnection f x v w =
      ((fderiv ℝ f x).adjoint.comp (fderiv ℝ f x)).inverse
        ((fderiv ℝ f x).adjoint (fderiv ℝ (fderiv ℝ f) x v w)) := rfl

/-- Equality of the actual induced metric germs forces equality of the
actual connection. No connection identity is supplied as a hypothesis. -/
theorem probeInducedConnection_eq_of_metric_germ
    (f g : E → V) (x : E) (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hinjf : Function.Injective (fderiv ℝ f x))
    (hinjg : Function.Injective (fderiv ℝ g x))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : E,
      inner ℝ (fderiv ℝ f y v) (fderiv ℝ f y w) =
        inner ℝ (fderiv ℝ g y v) (fderiv ℝ g y w)) :
    probeInducedConnection f x = probeInducedConnection g x := by
  let A := fderiv ℝ f x
  let C := fderiv ℝ g x
  have hG : A.adjoint.comp A = C.adjoint.comp C := by
    apply ContinuousLinearMap.ext
    intro v
    apply ext_inner_right ℝ
    intro w
    simpa only [A, C, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left] using hmetric.self_of_nhds v w
  have hderiv (v w : E) :
      fderiv ℝ (fun y ↦ inner ℝ (fderiv ℝ f y v) (fderiv ℝ f y w)) x =
      fderiv ℝ (fun y ↦ inner ℝ (fderiv ℝ g y v) (fderiv ℝ g y w)) x :=
    by
      have heq : (fun y ↦ inner ℝ (fderiv ℝ f y v) (fderiv ℝ f y w)) =ᶠ[𝓝 x]
          (fun y ↦ inner ℝ (fderiv ℝ g y v) (fderiv ℝ g y w)) :=
        hmetric.mono (fun _ h ↦ h v w)
      exact heq.fderiv_eq
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  apply (C.adjoint_comp_self_injective_iff.mpr hinjg)
  apply ext_inner_right ℝ
  intro z
  have hfK := increments_coordinate_christoffel_koszul f x v w z hf hinjf
  have hgK := increments_coordinate_christoffel_koszul g x v w z hg hinjg
  change 2 * inner ℝ ((A.adjoint.comp A) (probeInducedConnection f x v w)) z = _ at hfK
  change 2 * inner ℝ ((C.adjoint.comp C) (probeInducedConnection g x v w)) z = _ at hgK
  rw [hG, hderiv w z, hderiv v z, hderiv v w] at hfK
  simp only [ContinuousLinearMap.comp_apply, Function.comp_apply] at hfK hgK ⊢
  linarith only [hfK, hgK]

/-- The original trueSecondForm is exactly its native Hessian minus the
actual tangential connection term, as an ambient vector. -/
theorem trueSecondForm_eq_hessian_sub_inducedConnection
    (f : E → V) (hf : ContDiff ℝ ∞ f) (x v w : E)
    (hinj : Function.Injective (fderiv ℝ f x)) :
    (trueSecondForm (I := 𝓘(ℝ, E)) f hf.contMDiff x
      (symmetricSquareProduct (TangentSpace 𝓘(ℝ, E) x)
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm v)
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm w)) : V) =
      fderiv ℝ (fderiv ℝ f) x v w -
        fderiv ℝ f x (probeInducedConnection f x v w) := by
  rw [increments_trueSecondForm_coordinate f hf x v w,
    (normal_projection_gram_formula (fderiv ℝ f x) hinj).2.2.2]
  rfl

/-- For the actual fixed metric the connection is the base map's connection.
The only metric input is equality of genuine pullback metric germs. -/
theorem trueSecondForm_eq_hessian_sub_fixedConnection
    (f f₀ : E → V) (x v w : E)
    (hf : ContDiff ℝ ∞ f) (hf₀ : ContDiffAt ℝ 2 f₀ x) (hinjf : Function.Injective (fderiv ℝ f x))
    (hinjf₀ : Function.Injective (fderiv ℝ f₀ x))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : E,
      inner ℝ (fderiv ℝ f y a) (fderiv ℝ f y b) =
        inner ℝ (fderiv ℝ f₀ y a) (fderiv ℝ f₀ y b)) :
    (trueSecondForm (I := 𝓘(ℝ, E)) f hf.contMDiff x
      (symmetricSquareProduct (TangentSpace 𝓘(ℝ, E) x)
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm v)
        ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm w)) : V) =
      fderiv ℝ (fderiv ℝ f) x v w -
        fderiv ℝ f x (probeInducedConnection f₀ x v w) := by
  rw [trueSecondForm_eq_hessian_sub_inducedConnection f hf x v w hinjf,
    probeInducedConnection_eq_of_metric_germ f f₀ x
      (hf.contDiffAt.of_le (by simp)) hf₀ hinjf hinjf₀ hmetric]

#print axioms probeInducedConnection_eq_of_metric_germ
#print axioms trueSecondForm_eq_hessian_sub_inducedConnection
#print axioms trueSecondForm_eq_hessian_sub_fixedConnection
end GlobalEmbedding.Offline
