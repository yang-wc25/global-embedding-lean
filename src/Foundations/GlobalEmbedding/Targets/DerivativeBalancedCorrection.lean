import GlobalEmbedding.Paper.PrincipalTorusVerticalCalculus
import GlobalEmbedding.Paper.BalancedPairingRightInverse
import GlobalEmbedding.Paper.BalancedVerticalC2Size
import GlobalEmbedding.Paper.BalancedFixedResidualCoefficientsSmooth
import GlobalEmbedding.Paper.BalancedResidualCoefficientsFromGeometry
import GlobalEmbedding.Paper.BalancedCompactBaseChartCover
import GlobalEmbedding.Paper.PrincipalTorusEuclideanCharts
import GlobalEmbedding.Paper.BalancedNormalizedSourceForcing
import GlobalEmbedding.Paper.BalancedQuadraticDataOperator
import GlobalEmbedding.Paper.BalancedQuadraticDataTranslation
import GlobalEmbedding.Paper.BalancedNativeCompactSourceCorrection
import GlobalEmbedding.Paper.BalancedNativeFixedBranchMetric
import GlobalEmbedding.Paper.PrincipalTorusVerticalC2Bound
import GlobalEmbedding.Paper.BalancedNativeBranchGluing
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Derivative-balanced correction: original full target statement draft

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines371–418.
DAG node: `lem-balanced` (the unchanged original target node).

This is a stage2 statement candidate for independent root source/type review. The final
named target proof is still open and is explicitly marked below. No target acceptance,
Challenge edit or whole-library integration is claimed. Actual generators are constructed
from the actual action by PrincipalTorusBundle, not extra formal derivations.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

local instance balancedCorrectionTargetTorusAtlas (a : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin a)) (PeriodOneTorus a) :=
  periodicFlatTorusChartedSpace a

/-- Joint native smoothness on the actual parameter domain gives native smoothness
of each actual admissible spatial slice, without a separate slice hypothesis.
Proof: compose with actual smooth x↦(epsilon,x), whose range is in the original
parameter product. Source: the smooth family hypothesis of `lem:balanced`. -/
theorem balanced_family_slice_contMDiff
    {A E H M F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Set A} (P : A × M → F)
    (hP : ContMDiffOn ((𝓘(ℝ, A)).prod I) 𝓘(ℝ, F) ∞ P (J ×ˢ univ))
    {ε : A} (hε : ε ∈ J) :
    ContMDiff I 𝓘(ℝ, F) ∞ (fun x ↦ P (ε, x)) := by
  have hmap : ContMDiff I ((𝓘(ℝ, A)).prod I) ∞ (fun x : M ↦ (ε, x)) :=
    contMDiff_const.prodMk contMDiff_id
  exact hP.comp_contMDiff hmap (fun x ↦ ⟨hε, mem_univ x⟩)

/-- Derivative-balanced correction on the actual compact principal period-one torus bundle.

The source family is jointly smooth only on an actual open J containing zero. S3,S4
are fixed in epsilon and have no extra regularity hypothesis. C is an arbitrary actual
right inverse of the full actual first/second pairing at nonzero admissible epsilon;
its image has no restriction. Only its actual normalized extension Ctilde is jointly
smooth through zero; Ctilde(0) is unconstrained. All conclusions hold on one common
interval, including actual joint smoothness and actual uniform vertical C² O(epsilon²).
The actual finite-sum C² size is equivalent to the componentwise source convention
with fixed factor1+a+a², proved separately in BalancedVerticalC2Size.

Complete natural-language proof (source: `lem:balanced`, main.tex381–418): obtain actual
smoothness of fixed S3,S4 by evaluating the actual Gram residual at two different
nonzero parameters in J and solving the two scalar coefficient equations. On each
actual torus fiber construct the translation-invariant inverse W of L=sum D_i²−1
on the actual little Hölder spaces c^{0,1/2}→c^{2,1/2}; its existence and two-derivative
bound are the separate actual periodic PDE obligations. Construct the actual symmetric
bounded whole-function Qi,Qij by the exact source formulas(4.1), and prove(4.2) first
on actual smooth lifts by applying L and using product rules/commutation, then by
actual smooth density. Form the actual Qcal=(-Qi,Qij/2). In each actual local bundle
chart construct v=Ctilde(0,(epsilon S3+epsilon²S4)/2)+Ctilde Qcal(v,v) by the actual
small quadratic contraction. Actual compactness gives one common interval and forcing
bound, so v=O(epsilon) in actual c^{2,1/2}. The derivative has a uniform Neumann bound
on that same interval. Actual source translated-family smoothness and actual strict-small
uniqueness prove all mixed derivatives without successive interval shrink. The genuine
principal charts give actual torus shifts on overlaps; original global source data
then yield the actual operator conjugacy, and translation equivariance/uniqueness
identify the actual solutions. Existing native chart gluing on the actual open parameter
domain produces the actual jointly smooth global function. Put U=epsilon v, giving
actual vertical C² O(epsilon²). For nonzero epsilon, apply the actual pointwise right
inverse to the whole-function fixed equation and only then evaluate Qcal at the fiber
point. Bilinearity gives the true first/second pairings of U. The actual differentiated
pairing product rule and(4.2) cancel the residual exactly. At zero, U0=0 and the original
residual vanishes, so the same actual metric conclusion holds. Empty total space and
a=0 are retained. No desired Q, solution, transport law or correction is added as a
hypothesis of this final target. Root independently reviews the statement and ultimately
checks exact types/axioms/comparator before acceptance.

DAG node: `lem-balanced`; its original source statement is unchanged. This named theorem
is the sole deliberately open proof in this candidate and is not an accepted delivery. -/
theorem derivative_balanced_correction
    {a N : ℕ} {E EB M B ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
    [AddAction (PeriodOneTorus a) M]
    (π : M → B)
    (S : PrincipalTorusBundle (ι := ι) a 𝓘(ℝ, E) 𝓘(ℝ, EB) π)
    (J : Set ℝ) (hJ : IsOpen J) (hzero : 0 ∈ J)
    (P : ℝ × M → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P (J ×ˢ univ))
    (S3 S4 : M → Matrix (Fin a) (Fin a) ℝ)
    (hresidual : ∀ (ε : ℝ) (hε : ε ∈ J) (x : M),
      balancedGeometry (fun y ↦ P (ε, y)) (balanced_family_slice_contMDiff P hP hε)
        S.verticalGeneratorSection x =
        1 + ε ^ 3 • S3 x + ε ^ 4 • S4 x)
    (C : ℝ → M → EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
    (hC : ∀ (ε : ℝ), ε ∈ J → ε ≠ 0 → ∀ x : M,
      IsBalancedPairingRightInverse (fun y ↦ P (ε, y)) S.verticalGenerator x (C ε x))
    (Ctilde : ℝ × M → EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
    (hCtilde : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
      𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
        EuclideanSpace ℝ (Fin N)) ∞ Ctilde (J ×ˢ univ))
    (hscale : ∀ (ε : ℝ), ε ∈ J → ε ≠ 0 → ∀ x : M,
      Ctilde (ε, x) = ε • C ε x) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ hδJ : Metric.ball (0 : ℝ) δ ⊆ J,
      ∃ K : ℝ, 0 < K ∧ ∃ U : ℝ × M → EuclideanSpace ℝ (Fin N),
        ∃ hU : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
            𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U (Metric.ball (0 : ℝ) δ ×ˢ univ),
          ∀ (ε : ℝ) (hε : ε ∈ Metric.ball (0 : ℝ) δ) (x : M),
            balancedGeometry (fun y ↦ P (ε, y) + U (ε, y))
              ((balanced_family_slice_contMDiff P hP (hδJ hε)).add
                (balanced_family_slice_contMDiff U hU hε)) S.verticalGeneratorSection x = 1 ∧
            balancedVerticalC2Size S.verticalGenerator (fun y ↦ U (ε, y)) x ≤ K * ε ^ 2 := by
  classical
  obtain ⟨R, hR, hRJ⟩ := Metric.isOpen_iff.mp hJ 0 hzero
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨R, hR, hRJ, 1, by norm_num, fun _ ↦ 0, contMDiffOn_const, ?_⟩
    intro ε hε x
    exact isEmptyElim x
  by_cases ha : a = 0
  · subst a
    refine ⟨R, hR, hRJ, 1, by norm_num, fun _ ↦ 0, contMDiffOn_const, ?_⟩
    intro ε hε x
    constructor
    · exact Subsingleton.elim _ _
    · simpa [balancedVerticalC2Size] using sq_nonneg ε
  have hcoeff := balanced_residual_coefficients_from_geometry J hJ hzero
    (fun ε y ↦ P (ε, y)) (fun _ hε ↦ balanced_family_slice_contMDiff P hP hε)
    S.verticalGeneratorSection S3 S4 hresidual
  let : CompactSpace B := S.compactSpace_base
  obtain ⟨centers, index, radius, hballs, hcover⟩ :=
    balanced_compact_base_chart_cover (E := EB) (fun i ↦ (S.trivialization i).baseSet)
      (fun i ↦ (S.trivialization i).open_baseSet) S.cover_base
  let K (b : B) := Metric.closedBall (chartAt EB b b) (radius b)
  have hKcompact (b : B) : IsCompact (K b) := (hballs b).2.2.1
  have hKsub (b : B) : K b ⊆ S.nativeBundleBaseSet (index b) b :=
    (hballs b).2.2.2
  have htotalcover (x : M) : ∃ b ∈ centers,
      x ∈ (S.nativeBundleChart (index b) b).source ∧
        chartAt EB b (π x) ∈ K b := by
    obtain ⟨b, hb, hxsource, hxball⟩ := hcover (π x)
    have hxK : chartAt EB b (π x) ∈ K b := Metric.ball_subset_closedBall hxball
    have hbase : π x ∈ (S.trivialization (index b)).baseSet := by
      have hx := (hKsub b hxK).2
      change (chartAt EB b).symm (chartAt EB b (π x)) ∈
        (S.trivialization (index b)).baseSet at hx
      simpa only [(chartAt EB b).left_inv hxsource] using hx
    refine ⟨b, hb, ?_, hxK⟩
    rw [S.nativeBundleChart_source]
    exact ⟨(S.trivialization (index b)).mem_source.mpr hbase, hxsource⟩
  have hcenters : centers.Nonempty := by
    obtain ⟨b, hb, _⟩ := htotalcover (Classical.choice hM)
    exact ⟨b, hb⟩
  have hfiniteBounds (localδ localC : B → ℝ)
      (hδ : ∀ b ∈ centers, 0 < localδ b) (hC : ∀ b ∈ centers, 0 < localC b) :
      ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
        ∀ b ∈ centers, δ ≤ localδ b ∧ localC b ≤ C := by
    let δ := centers.inf' hcenters localδ
    let C := centers.sup' hcenters localC
    have hδpos : 0 < δ := (Finset.lt_inf'_iff hcenters).mpr hδ
    obtain ⟨b, hb⟩ := hcenters
    have hCpos : 0 < C := (hC b hb).trans_le (Finset.le_sup' localC hb)
    refine ⟨δ, C, hδpos, hCpos, ?_⟩
    intro b hb
    exact ⟨Finset.inf'_le localδ hb, Finset.le_sup' localC hb⟩
  let sourceA (z : ℝ × M) := balancedNormalizedSourceOperator (Ctilde z)
  let sourcef (z : ℝ × M) :=
    balancedNormalizedSourceForcing (Ctilde z) z.1 (S3 z.2) (S4 z.2)
  have hsources := balanced_normalized_source_contMDiffOn
    (fun z : ℝ × M ↦ z.1) (fun z ↦ S3 z.2) (fun z ↦ S4 z.2) Ctilde
    contMDiff_fst.contMDiffOn
    (fun i j ↦ ((hcoeff i j).1.comp contMDiff_snd).contMDiffOn)
    (fun i j ↦ ((hcoeff i j).2.comp contMDiff_snd).contMDiffOn) hCtilde
  have hsourcef0 (x : M) : sourcef (0, x) = 0 :=
    (balanced_normalized_source_forcing_spec (Ctilde (0, x)) 0 (S3 x) (S4 x)).2.2.1
  have hsourceAR : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card (BalancedPairingIndex a))) →L[ℝ]
        EuclideanSpace ℝ (Fin N)) ∞ sourceA (Metric.ball (0 : ℝ) R ×ˢ univ) :=
    hsources.1.mono (fun z hz ↦ ⟨hRJ hz.1, hz.2⟩)
  have hsourcefR : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ sourcef
      (Metric.ball (0 : ℝ) R ×ˢ univ) :=
    hsources.2.mono (fun z hz ↦ ⟨hRJ hz.1, hz.2⟩)
  let Q := balancedQuadraticDataOperator (a := a) (N := N) (α := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)
  have hQsym : ∀ v w, Q v w = Q w v :=
    balancedQuadraticDataOperator_symmetric (by norm_num) (by norm_num)
  have hQτ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w) :=
    balancedQuadraticDataOperator_translate_euclidean (by norm_num) (by norm_num)
  have branches := fun b : B ↦ S.native_compact_source_correction Q hQsym hQτ R hR
    sourceA sourcef hsourceAR hsourcefR hsourcef0 (index b) b (K b)
    (hKcompact b) (hKsub b) (by norm_num) (by norm_num)
  choose forcing ops hfvalue hAvalue V hV hKV hVU δloc Cloc hδloc hCloc hδlocR
    v hv hv0 hspec hunorm hunative using branches
  obtain ⟨δ, Cbound, hδ, hCbound, hlocalbounds⟩ :=
    hfiniteBounds δloc Cloc (fun b _ ↦ hδloc b) (fun b _ ↦ hCloc b)
  obtain ⟨b₀, hb₀⟩ := hcenters
  have hδR : δ < R := (hlocalbounds b₀ hb₀).1.trans_lt (hδlocR b₀)
  have hδJ : Metric.ball (0 : ℝ) δ ⊆ J :=
    (Metric.ball_subset_ball hδR.le).trans hRJ
  have hlocaldomain (b : B) (hb : b ∈ centers) :
      V b ×ˢ Metric.ball (0 : ℝ) δ ⊆ V b ×ˢ Metric.ball (0 : ℝ) (δloc b) :=
    fun z hz ↦ ⟨hz.1, Metric.ball_subset_ball (hlocalbounds b hb).1 hz.2⟩
  have hdatadomain (b : B) : V b ×ˢ Metric.ball (0 : ℝ) δ ⊆
      S.nativeBundleBaseSet (index b) b ×ˢ Metric.ball (0 : ℝ) R :=
    fun z hz ↦ ⟨hVU b hz.1, Metric.ball_subset_ball hδR.le hz.2⟩
  have hunormUniform (b : B) (hb : b ∈ centers) (z : EB × ℝ)
      (hz : z ∈ V b ×ˢ Metric.ball (0 : ℝ) δ) :
      ‖z.2 • v b z‖ ≤ Cbound * z.2 ^ 2 :=
    (hunorm b z (hlocaldomain b hb hz)).trans
      (mul_le_mul_of_nonneg_right (hlocalbounds b hb).2 (sq_nonneg z.2))
  have hnativeUniform (b : B) (hb : b ∈ centers) := (hunative b).mono
    (show (V b ×ˢ Metric.ball (0 : ℝ) δ) ×ˢ (univ : Set (PeriodOneTorus a)) ⊆
        (V b ×ˢ Metric.ball (0 : ℝ) (δloc b)) ×ˢ univ by
      intro z hz
      exact ⟨hlocaldomain b hb hz.1, hz.2⟩)
  let κ := {b : B // b ∈ centers}
  have hVcover (x : M) : ∃ k : κ,
      x ∈ (S.nativeBundleChart (index k.val) k.val).source ∧
        chartAt EB k.val (π x) ∈ V k.val := by
    obtain ⟨b, hb, hx, hcoord⟩ := htotalcover x
    exact ⟨⟨b, hb⟩, hx, hKV b hcoord⟩
  have hpointfixed (b : B) (hb : b ∈ centers) (z : EB × ℝ)
      (hz : z ∈ V b ×ˢ Metric.ball (0 : ℝ) δ) (y : EuclideanSpace ℝ (Fin a)) :
      (v b z).val.toFun y =
        Ctilde (z.2, S.fiberEuclideanLift (index b) ((chartAt EB b).symm z.1) y)
          (balancedNormalizedResidualData z.2
            (S3 (S.fiberEuclideanLift (index b) ((chartAt EB b).symm z.1) y))
            (S4 (S.fiberEuclideanLift (index b) ((chartAt EB b).symm z.1) y))) +
        Ctilde (z.2, S.fiberEuclideanLift (index b) ((chartAt EB b).symm z.1) y)
          ((balancedPairingDataCoordinates a).symm ((Q (v b z) (v b z)).val.toFun y)) := by
    have he := congrArg
      (fun w : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) ↦ w.val.toFun y)
      (hspec b z (hlocaldomain b hb hz)).1
    simp only [Submodule.coe_add,
      (periodicCAlpha_pointwise_operations a N 2 (1 / 2 : ℝ)).2.1, Pi.add_apply] at he
    rw [hfvalue b z (hdatadomain b hz) y, hAvalue b z (hdatadomain b hz)] at he
    exact he
  have hfinish (U : ℝ × M → EuclideanSpace ℝ (Fin N))
      (hU : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
        𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U (Metric.ball (0 : ℝ) δ ×ˢ univ))
      (hlifts : ∀ b ∈ centers, ∀ p ∈ V b, ∀ ε ∈ Metric.ball (0 : ℝ) δ, ∀ y,
        U (ε, S.fiberEuclideanLift (index b) ((chartAt EB b).symm p) y) =
          (ε • v b (p, ε)).val.toFun y) :
      ∀ (ε : ℝ) (hε : ε ∈ Metric.ball (0 : ℝ) δ) (x : M),
        balancedGeometry (fun y ↦ P (ε, y) + U (ε, y))
          ((balanced_family_slice_contMDiff P hP (hδJ hε)).add
            (balanced_family_slice_contMDiff U hU hε)) S.verticalGeneratorSection x = 1 ∧
        balancedVerticalC2Size S.verticalGenerator (fun y ↦ U (ε, y)) x ≤
          ((1 + (a : ℝ) + (a : ℝ) ^ 2) * Cbound) * ε ^ 2 := by
    have hgram_congr (F G : M → EuclideanSpace ℝ (Fin N))
        (hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
        (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G)
        (heq : F = G) : balancedGeometry F hF S.verticalGeneratorSection =
          balancedGeometry G hG S.verticalGeneratorSection := by
      cases heq
      rfl
    have hzeroδ : (0 : ℝ) ∈ Metric.ball (0 : ℝ) δ := by simpa using hδ
    have hU0 (x : M) : U (0, x) = 0 := by
      obtain ⟨b, hb, hxchart, hxK⟩ := htotalcover x
      have hxparts : x ∈ (S.trivialization (index b)).source ∧
          π x ∈ (chartAt EB b).source := by
        simpa only [S.nativeBundleChart_source, mem_inter_iff, mem_preimage] using hxchart
      obtain ⟨y, hy⟩ := S.exists_fiberEuclideanLift (index b) hxparts.1
      have he := hlifts b hb (chartAt EB b (π x)) (hKV b hxK) 0 hzeroδ y
      rw [(chartAt EB b).left_inv hxparts.2, hy] at he
      simpa only [zero_smul, Submodule.coe_zero,
        (periodicCAlpha_pointwise_operations a N 2 (1 / 2 : ℝ)).1, Pi.zero_apply] using he
    intro ε hε x
    obtain ⟨b, hb, hxchart, hxK⟩ := htotalcover x
    have hxparts : x ∈ (S.trivialization (index b)).source ∧
        π x ∈ (chartAt EB b).source := by
      simpa only [S.nativeBundleChart_source, mem_inter_iff, mem_preimage] using hxchart
    let p := chartAt EB b (π x)
    have hp : p ∈ V b := hKV b hxK
    have hpbase : (chartAt EB b).symm p = π x :=
      (chartAt EB b).left_inv hxparts.2
    have hbbase := (S.trivialization (index b)).mem_source.mp hxparts.1
    obtain ⟨y, hy⟩ := S.exists_fiberEuclideanLift (index b) hxparts.1
    have hUε := balanced_family_slice_contMDiff U hU hε
    have hPε := balanced_family_slice_contMDiff P hP (hδJ hε)
    have hlift (z : EuclideanSpace ℝ (Fin a)) :
        U (ε, S.fiberEuclideanLift (index b) (π x) z) =
          (ε • v b (p, ε)).val.toFun z := by
      simpa only [hpbase] using hlifts b hb p hp ε hε z
    constructor
    · by_cases hεzero : ε = 0
      · subst ε
        have heq := hgram_congr (fun z ↦ P (0, z) + U (0, z))
          (fun z ↦ P (0, z)) (hPε.add hUε) hPε
          (funext (fun z ↦ by rw [hU0 z, add_zero]))
        apply (congrFun heq x).trans
        simpa only [zero_pow (by omega : 3 ≠ 0), zero_pow (by omega : 4 ≠ 0),
          zero_smul, add_zero] using hresidual 0 hzero x
      · have hm := S.balanced_native_fixed_branch_metric
          (fun z ↦ P (ε, z)) (fun z ↦ U (ε, z)) hPε hUε
          (index b) hbbase (by norm_num) (by norm_num) ε S3 S4
          (C ε) (fun z ↦ Ctilde (ε, z)) (v b (p, ε)) hlift
          (fun z ↦ hresidual ε (hδJ hε) (S.fiberEuclideanLift (index b) (π x) z))
          (fun z ↦ hC ε (hδJ hε) hεzero (S.fiberEuclideanLift (index b) (π x) z))
          (fun z ↦ hscale ε (hδJ hε) hεzero
            (S.fiberEuclideanLift (index b) (π x) z))
          (fun z ↦ by simpa only [hpbase] using hpointfixed b hb (p, ε) ⟨hp, hε⟩ z)
        have hmy := hm y
        rw [hy] at hmy
        exact hmy
    · have hs := S.verticalC2Size_le_little_norm (fun z ↦ U (ε, z)) hUε
        (index b) hbbase (ε • v b (p, ε)) hlift y
      rw [hy] at hs
      have hn := mul_le_mul_of_nonneg_left
        (hunormUniform b hb (p, ε) ⟨hp, hε⟩)
        (show 0 ≤ 1 + (a : ℝ) + (a : ℝ) ^ 2 by positivity)
      exact hs.trans (by simpa only [mul_assoc] using hn)
  obtain ⟨U, hU, _hUchart, hlift⟩ := S.selected_native_branches_glue
    (fun k : κ ↦ index k.val) (fun k : κ ↦ k.val) (fun k : κ ↦ V k.val)
    (fun k ↦ hV k.val) (fun k ↦ hVU k.val) hVcover δ Q hQsym hQτ sourceA sourcef
    (fun k ↦ forcing k.val) (fun k ↦ v k.val) (fun k ↦ ops k.val)
    (fun k z hz y ↦ hfvalue k.val z (hdatadomain k.val hz) y)
    (fun k z hz u y ↦ hAvalue k.val z (hdatadomain k.val hz) u y)
    (fun k z hz ↦ (hspec k.val z (hlocaldomain k.val k.property hz)).1)
    (fun k z hz ↦ (hspec k.val z (hlocaldomain k.val k.property hz)).2.2)
    (fun k ↦ hnativeUniform k.val k.property)
  refine ⟨δ, hδ, hδJ, (1 + (a : ℝ) + (a : ℝ) ^ 2) * Cbound,
    by positivity, U, hU, ?_⟩
  exact hfinish U hU (fun b hb p hp ε hε y ↦ hlift ⟨b, hb⟩ p hp ε hε y)

#print axioms balanced_family_slice_contMDiff
#print axioms derivative_balanced_correction

end GlobalEmbedding.Paper
