import GlobalEmbedding.Paper.PrincipalTorusEuclideanCharts
import GlobalEmbedding.Paper.BalancedSourceLittleDataExistence

/-!
# Actual local little data from the original native global sources

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines403–418.
DAG node: `balanced-native-local-source-data`.
-/

noncomputable section

open Set WithLp
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {E H EB M B ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]

namespace PrincipalTorusBundle

variable {a : ℕ} {I : ModelWithCorners ℝ E H} {π : M → B}
  [IsManifold I ∞ M] [AddAction (PeriodOneTorus a) M]
  (S : PrincipalTorusBundle (ι := ι) a I 𝓘(ℝ, EB) π)

/-- Literal pullback of the original global time-dependent source in the actual native
base chart and actual original fiber lift; the base itself remains a manifold.
Source: local bundle expression of the original data in `lem:balanced`, line418. -/
def nativeSourcePullback {V : Type*} (F : ℝ × M → V) (i : ι) (b : B)
    (z : EB × ℝ) (y : EuclideanSpace ℝ (Fin a)) : V :=
  F (z.2, S.fiberEuclideanLift i ((chartAt EB b).symm z.1) y)

/-- Actual joint native source smoothness gives true coordinate smoothness and periodicity
on the original local parameter domain, without assuming either pullback property.

Compose the original source with time projection and the accepted actual joint inverse-chart
lift. This map takes the actual local domain into J×M, so only the original source regularity
is used. Native-to-normed smoothness gives ContDiffOn. The accepted actual integer-periodic
joint lift makes the original source values periodic by equality of their arguments.
Source: local smooth periodic source data in `lem:balanced`, lines403–418. -/
theorem native_source_pullback_smooth_periodic
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (J : Set ℝ) (F : ℝ × M → V)
    (hF : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, V) ∞ F (J ×ˢ univ))
    (i : ι) (b : B) :
    ContDiffOn ℝ ∞ (Function.uncurry (S.nativeSourcePullback F i b))
      ((S.nativeBundleBaseSet i b ×ˢ J) ×ˢ univ) ∧
      ∀ z ∈ S.nativeBundleBaseSet i b ×ˢ J,
        ∀ (y : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
          S.nativeSourcePullback F i b z (y + toLp 2 (fun j ↦ (m j : ℝ))) =
            S.nativeSourcePullback F i b z y := by
  have hparam : ContDiff ℝ ∞ (fun z : (EB × ℝ) × EuclideanSpace ℝ (Fin a) ↦
      z.1.1) := contDiff_fst.comp contDiff_fst
  have htime : ContDiff ℝ ∞ (fun z : (EB × ℝ) × EuclideanSpace ℝ (Fin a) ↦
      z.1.2) := contDiff_snd.comp contDiff_fst
  have hargs : ContMDiff 𝓘(ℝ, (EB × ℝ) × EuclideanSpace ℝ (Fin a))
      (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) ∞
      (fun z : (EB × ℝ) × EuclideanSpace ℝ (Fin a) ↦ (z.1.1, z.2)) :=
    hparam.contMDiff.prodMk contDiff_snd.contMDiff
  have hpoint := (S.contMDiffOn_nativeBundleChart_jointLift i b).comp hargs.contMDiffOn
    (show ∀ z ∈ (S.nativeBundleBaseSet i b ×ˢ J) ×ˢ
      (univ : Set (EuclideanSpace ℝ (Fin a))),
      (z.1.1, z.2) ∈ S.nativeBundleBaseSet i b ×ˢ univ by
      intro z hz
      exact ⟨hz.1.1, mem_univ _⟩)
  have hpair := htime.contMDiff.contMDiffOn.prodMk hpoint
  refine ⟨(hF.comp hpair (fun z hz ↦ ⟨hz.1.2, mem_univ _⟩)).contDiffOn, ?_⟩
  intro z hz y m
  exact congrArg (fun x : M ↦ F (z.2, x))
    (S.nativeBundleChart_jointLift_periodic i b z.1 y m)

/-- Actual global operator and forcing sources construct actual local little forcing and
bounded multiplication, with exact original values and genuine parameter norm smoothness.

Apply the preceding actual native pullback theorem to both original sources. Invoke the
already proved arbitrary-finite-dimensional source constructor on EB×time and retain its
actual carriers, pointwise values, and norm smoothness. No periodicity, little membership,
selected solution or desired operator regularity is assumed. Empty domains and all zero
dimensions are included. Source: local construction before(4.3) in `lem:balanced`. -/
theorem native_local_source_data [FiniteDimensional ℝ EB]
    {R N : ℕ} {α : ℝ} (J : Set ℝ) (hJ : IsOpen J)
    (sourceA : ℝ × M → EuclideanSpace ℝ (Fin R) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (sourcef : ℝ × M → EuclideanSpace ℝ (Fin N))
    (hA : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I)
      𝓘(ℝ, EuclideanSpace ℝ (Fin R) →L[ℝ] EuclideanSpace ℝ (Fin N)) ∞
      sourceA (J ×ˢ univ))
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I)
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ sourcef (J ×ˢ univ))
    (i : ι) (b : B) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ f : EB × ℝ → LittlePeriodicCAlphaFunction a N 2 α,
      ∃ A : EB × ℝ → LittlePeriodicCAlphaFunction a R 2 α →L[ℝ]
          LittlePeriodicCAlphaFunction a N 2 α,
        (∀ z ∈ S.nativeBundleBaseSet i b ×ˢ J, ∀ y,
          (f z).val.toFun y = S.nativeSourcePullback sourcef i b z y) ∧
        (∀ z ∈ S.nativeBundleBaseSet i b ×ˢ J,
          ∀ (u : LittlePeriodicCAlphaFunction a R 2 α) y,
            (A z u).val.toFun y = S.nativeSourcePullback sourceA i b z y (u.val.toFun y)) ∧
        ContDiffOn ℝ ∞ f (S.nativeBundleBaseSet i b ×ˢ J) ∧
        ContDiffOn ℝ ∞ A (S.nativeBundleBaseSet i b ×ˢ J) := by
  obtain ⟨hsA, hperiodA⟩ := S.native_source_pullback_smooth_periodic J sourceA hA i b
  obtain ⟨hsf, hperiodf⟩ := S.native_source_pullback_smooth_periodic J sourcef hf i b
  obtain ⟨f, A, hfvalue, hAvalue, hfsmooth, hAsmooth, _, _⟩ :=
    balanced_source_little_data_exists (S.nativeBundleBaseSet i b ×ˢ J)
      ((S.isOpen_nativeBundleBaseSet i b).prod hJ)
      (S.nativeSourcePullback sourceA i b) (S.nativeSourcePullback sourcef i b)
      hsA hsf hperiodA hperiodf hα0 hα1
  exact ⟨f, A, hfvalue, hAvalue, hfsmooth, hAsmooth⟩

#print axioms native_source_pullback_smooth_periodic
#print axioms native_local_source_data

end PrincipalTorusBundle
end GlobalEmbedding.Paper
