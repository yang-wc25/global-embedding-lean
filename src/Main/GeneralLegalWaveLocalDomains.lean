import Main.GeneralLegalWaveRefinement

/-!
# Local-domain presentations of arbitrary-cutoff legal waves

The phase and normal need only be smooth on a genuine open neighborhood
of the cutoff support. The cutoff, defined on that open manifold with
compact support there, is extended by zero using Mathlib's smooth extension
theorem. The phase is merely totalized outside the open set, and the normal
is assigned the zero normal vector outside it. No global smoothness of
these uncut extensions is claimed or required.

The native phase covector of the local germ is computed using a totalized
representative. It is independent of all values assigned outside the open
set, as proved below. This supplies a concrete presentation adapter to
`OpenSupportedLegalWave`; it does not supply the full generic probe family.
-/

noncomputable section
open Set Function Manifold TopologicalSpace
open scoped ContDiff Topology Classical

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Arbitrary values away from an open set do not affect smoothness on it. -/
theorem open_subtype_extend_contMDiffOn
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (U : Opens M) (f : U → W) (outside : M → W)
    (hf : ContMDiff IM 𝓘(ℝ,W) ∞ f) :
    ContMDiffOn IM 𝓘(ℝ,W) ∞ (Subtype.val.extend f outside) (U : Set M) := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rw [← contMDiffAt_subtype_iff (x := (⟨x,hx⟩ : U))]
  have he : (fun y : U => Subtype.val.extend f outside (y : M)) = f := by
    funext y
    exact Subtype.val_injective.extend_apply f outside y
  rw [he]
  exact hf.contMDiffAt

/-- The zero extension retains the literal local cutoff and its support
stays inside the original open set, not merely inside its closure. -/
theorem open_compact_cutoff_zero_extension
    (U : Opens M) (chi : U → ℝ) (hcompact : HasCompactSupport chi)
    (hchi : ContMDiff IM 𝓘(ℝ,ℝ) ∞ chi) :
    ContMDiff IM 𝓘(ℝ,ℝ) ∞ (Subtype.val.extend chi 0) ∧
      tsupport (Subtype.val.extend chi 0) ⊆ (U : Set M) ∧
      ∀ x : U, Subtype.val.extend chi 0 (x : M) = chi x := by
  refine ⟨ContMDiff.extend_zero hcompact hchi,?_,?_⟩
  · exact (hcompact.tsupport_extend_zero_subset continuous_subtype_val).trans
      (Subtype.coe_image_subset _ _)
  · exact Subtype.val_injective.extend_apply chi 0

/-- Native phase differentials depend only on the local germ, regardless
of the chosen values away from the legal open neighborhood. -/
theorem phase_mfderiv_eq_of_same_open_restriction
    (U : Opens M) (f g : M → ℝ) (hfg : EqOn f g U)
    (x : M) (hx : x ∈ U) :
    mfderiv IM 𝓘(ℝ,ℝ) f x = mfderiv IM 𝓘(ℝ,ℝ) g x := by
  have he : f =ᶠ[𝓝 x] g := by
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    exact hfg hy
  have hm := he.mfderiv_eq (I := IM) (I' := 𝓘(ℝ,ℝ))
  ext v
  exact congrArg (fun L => L v) hm

/-- A zero totalization of a local section of the actual normal fibers. -/
def localNormalZeroExtension
    (F : M → V) (U : Opens M) (nu : ∀ x : U, normalSpace (I := IM) F (x : M)) :
    ∀ x : M, normalSpace (I := IM) F x :=
  fun x => if hx : x ∈ U then nu ⟨x,hx⟩ else 0

theorem localNormalZeroExtension_on
    (F : M → V) (U : Opens M) (nu : ∀ x : U, normalSpace (I := IM) F (x : M))
    (x : U) : localNormalZeroExtension F U nu (x : M) = nu x := by
  simp only [localNormalZeroExtension,dif_pos x.property]

theorem localNormalZeroExtension_contMDiffOn
    (F : M → V) (U : Opens M) (nu : ∀ x : U, normalSpace (I := IM) F (x : M))
    (hnu : ContMDiff IM 𝓘(ℝ,V) ∞ (fun x : U => (nu x : V))) :
    ContMDiffOn IM 𝓘(ℝ,V) ∞
      (fun x => (localNormalZeroExtension F U nu x : V)) (U : Set M) := by
  have he := open_subtype_extend_contMDiffOn U (fun x : U => (nu x : V)) 0 hnu
  apply he.congr
  intro x hx
  have hext := Subtype.val_injective.extend_apply (fun y : U => (nu y : V))
    (0 : M → V) (⟨x,hx⟩ : U)
  change (localNormalZeroExtension F U nu x : V) = _
  rw [localNormalZeroExtension_on F U nu (⟨x,hx⟩ : U)]
  exact hext.symm

/-- A fully local presentation. The phase covector is the native derivative
of its germ, represented by the arbitrary zero totalization. The preceding
congruence theorem ensures this definition is independent of that choice.
Compact support is relative to the open source, which is the precise
condition needed for smooth cutoff extension across its boundary. -/
structure LocallyPresentedLegalWave
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F) where
  domain : Opens M
  cutoff : domain → ℝ
  cutoff_compact : HasCompactSupport cutoff
  cutoff_smooth : ContMDiff IM 𝓘(ℝ,ℝ) ∞ cutoff
  phase : domain → ℝ
  phase_smooth : ContMDiff IM 𝓘(ℝ,ℝ) ∞ phase
  normal : ∀ x : domain, normalSpace (I := IM) F (x : M)
  normal_smooth : ContMDiff IM 𝓘(ℝ,V) ∞ (fun x : domain => (normal x : V))
  legal : ∀ x : domain,
    GoodCovector F hF (x : M)
      (mfderiv IM 𝓘(ℝ,ℝ) (Subtype.val.extend phase 0) (x : M)) ∧
      normal x ∈ supportedRankLegalValueSpace (trueSecondForm F hF (x : M))
        (mfderiv IM 𝓘(ℝ,ℝ) (Subtype.val.extend phase 0) (x : M)).toLinearMap

namespace LocallyPresentedLegalWave

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}

/-- The actual local-to-total input adapter. Only the supported cutoff is
globally smooth. The uncut phase and normal are smooth on the old domain. -/
def toOpenSupported (w : LocallyPresentedLegalWave (n := n) F hF) :
    OpenSupportedLegalWave (n := n) F hF where
  domain := w.domain
  phase := Subtype.val.extend w.phase 0
  normal := localNormalZeroExtension F w.domain w.normal
  cutoff := Subtype.val.extend w.cutoff 0
  cutoff_smooth := (open_compact_cutoff_zero_extension w.domain w.cutoff
    w.cutoff_compact w.cutoff_smooth).1
  domain_open := w.domain.isOpen
  support_subset := (open_compact_cutoff_zero_extension w.domain w.cutoff
    w.cutoff_compact w.cutoff_smooth).2.1
  phase_smooth := open_subtype_extend_contMDiffOn w.domain w.phase 0 w.phase_smooth
  normal_smooth := localNormalZeroExtension_contMDiffOn F w.domain w.normal w.normal_smooth
  legal := by
    intro x hx
    change GoodCovector F hF x _ ∧ localNormalZeroExtension F w.domain w.normal x ∈ _
    rw [localNormalZeroExtension_on F w.domain w.normal (⟨x,hx⟩ : w.domain)]
    exact w.legal ⟨x,hx⟩

theorem toOpenSupported_value (w : LocallyPresentedLegalWave (n := n) F hF)
    (x : w.domain) :
    w.toOpenSupported.value (x : M) = w.cutoff x • (w.normal x : V) := by
  change Subtype.val.extend w.cutoff 0 (x : M) •
    (localNormalZeroExtension F w.domain w.normal (x : M) : V) = _
  rw [Subtype.val_injective.extend_apply,localNormalZeroExtension_on]

end LocallyPresentedLegalWave
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.open_compact_cutoff_zero_extension
#print axioms GlobalEmbedding.Continuation.phase_mfderiv_eq_of_same_open_restriction
#print axioms GlobalEmbedding.Continuation.LocallyPresentedLegalWave.toOpenSupported
#print axioms GlobalEmbedding.Continuation.LocallyPresentedLegalWave.toOpenSupported_value
