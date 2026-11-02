import GlobalEmbedding.Paper.FreeHopfOrbitCorrection
import GlobalEmbedding.Paper.FreeHopfFixedBranchMetric
import GlobalEmbedding.Paper.BalancedResidualCoefficientsFromGeometry
import GlobalEmbedding.Paper.BalancedQuadraticDataTranslation

/-!
# Full original balanced correction on the genuine whole Hopf product

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines371–418 and477–495.
DAG node: `free-hopf-balanced-correction`.
-/

noncomputable section

open Set Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual native Gram is exactly the original literal Hopf partial Gram. -/
theorem freeHopf_geometry_eq_gram {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (F : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (x : FreeHopfProduct C) :
    balancedGeometry F hF (freeHopfGeneratorSection C) x =
      Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i F x) := by
  change Matrix.gram ℝ (fun i ↦
    mvfderiv (freeHopfModel C) F x (freeHopfGenerator C i x)) = _
  congr 1
  funext i
  exact freeHopfGenerator_mvfderiv C i F hF x

/-- The original balanced inputs construct one genuine correction on the whole Hopf product.

Proof: actual residual geometry recovers smooth fixed S3,S4 without assuming it. The
accepted normalized-source construction, with the actual unconstrained normalized inverse,
gives true smooth forcing vanishing at zero. Instantiate the actual canonical whole-function
quadratic operator and its proved symmetry/translation identities. The genuine compact orbit
correction theorem constructs one native jointly smooth U with exact orbit lifts and uniform
actual vertical C² O(epsilon²), deriving covariance by strict-small uniqueness. At every
nonzero epsilon apply the accepted actual Hopf fixed-branch metric theorem to its constructed
profile, original full right inverse and original scaling identity. At zero, U is exactly
zero and the original residual is exactly identity. The actual native/literal derivative
identification gives the original partial Gram throughout the common interval. No principal
CP atlas, desired solution, analytic-Q hypothesis, carrier, compatibility, metric identity,
norm bound, inverse at zero or constraint on the normalized value at zero is an input.
Source: lem:balanced and its use in thm:free, lines371–418 and477–495. -/
theorem freeHopf_balanced_correction {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (J : Set ℝ) (hJ : IsOpen J) (hzero : 0 ∈ J)
    (P : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P (J ×ˢ univ))
    (S3 S4 : FreeHopfProduct C → Matrix (Fin a) (Fin a) ℝ)
    (hresidual : ∀ (ε : ℝ), ε ∈ J → ∀ x : FreeHopfProduct C,
      Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i (fun y ↦ P (ε, y)) x) =
        1 + ε ^ 3 • S3 x + ε ^ 4 • S4 x)
    (A : ℝ → FreeHopfProduct C → EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
    (hA : ∀ (ε : ℝ), ε ∈ J → ε ≠ 0 → ∀ x : FreeHopfProduct C,
      IsBalancedPairingRightInverse (fun y ↦ P (ε, y)) (freeHopfGenerator C) x (A ε x))
    (Atilde : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N))
    (hAtilde : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
        EuclideanSpace ℝ (Fin N)) ∞ Atilde (J ×ˢ univ))
    (hscale : ∀ (ε : ℝ), ε ∈ J → ε ≠ 0 → ∀ x : FreeHopfProduct C,
      Atilde (ε, x) = ε • A ε x) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (0 : ℝ) δ ⊆ J ∧
      ∃ K : ℝ, 0 < K ∧ ∃ U : ℝ × FreeHopfProduct C → EuclideanSpace ℝ (Fin N),
        ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
          𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U (Metric.ball (0 : ℝ) δ ×ˢ univ) ∧
        ∀ (ε : ℝ), ε ∈ Metric.ball (0 : ℝ) δ → ∀ x : FreeHopfProduct C,
          Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i
            (fun y ↦ P (ε, y) + U (ε, y)) x) = 1 ∧
          balancedVerticalC2Size (freeHopfGenerator C) (fun y ↦ U (ε, y)) x ≤ K * ε ^ 2 := by
  have hPslice (ε : ℝ) (hε : ε ∈ J) :
      ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (fun x ↦ P (ε, x)) :=
    hP.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun x ↦ ⟨hε, mem_univ x⟩)
  have hgeometry (ε : ℝ) (hε : ε ∈ J) (x : FreeHopfProduct C) :
      balancedGeometry (fun y ↦ P (ε, y)) (hPslice ε hε) (freeHopfGeneratorSection C) x =
        1 + ε ^ 3 • S3 x + ε ^ 4 • S4 x :=
    (freeHopf_geometry_eq_gram C _ (hPslice ε hε) x).trans (hresidual ε hε x)
  have hcoeff := balanced_residual_coefficients_from_geometry J hJ hzero
    (fun ε y ↦ P (ε, y)) hPslice (freeHopfGeneratorSection C) S3 S4 hgeometry
  obtain ⟨R, hR, hRJ⟩ := Metric.isOpen_iff.mp hJ 0 hzero
  let sourceA (z : ℝ × FreeHopfProduct C) := balancedNormalizedSourceOperator (Atilde z)
  let sourcef (z : ℝ × FreeHopfProduct C) :=
    balancedNormalizedSourceForcing (Atilde z) z.1 (S3 z.2) (S4 z.2)
  have hsources := balanced_normalized_source_contMDiffOn
    (fun z : ℝ × FreeHopfProduct C ↦ z.1) (fun z ↦ S3 z.2) (fun z ↦ S4 z.2) Atilde
    contMDiff_fst.contMDiffOn
    (fun i j ↦ ((hcoeff i j).1.comp contMDiff_snd).contMDiffOn)
    (fun i j ↦ ((hcoeff i j).2.comp contMDiff_snd).contMDiffOn) hAtilde
  have hsourcef0 (x : FreeHopfProduct C) : sourcef (0, x) = 0 :=
    (balanced_normalized_source_forcing_spec (Atilde (0, x)) 0 (S3 x) (S4 x)).2.2.1
  have hsourceAR : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card (BalancedPairingIndex a))) →L[ℝ]
        EuclideanSpace ℝ (Fin N)) ∞ sourceA (Metric.ball (0 : ℝ) R ×ˢ univ) :=
    hsources.1.mono (fun z hz ↦ ⟨hRJ hz.1, hz.2⟩)
  have hsourcefR : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ sourcef (Metric.ball (0 : ℝ) R ×ˢ univ) :=
    hsources.2.mono (fun z hz ↦ ⟨hRJ hz.1, hz.2⟩)
  let Q := balancedQuadraticDataOperator (a := a) (N := N) (α := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)
  have hQsym : ∀ v w, Q v w = Q w v :=
    balancedQuadraticDataOperator_symmetric (by norm_num) (by norm_num)
  have hQτ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w) :=
    balancedQuadraticDataOperator_translate_euclidean (by norm_num) (by norm_num)
  obtain ⟨δ, L, hδ, hL, hδR, v, U, hU, hU0, hspec⟩ :=
    freeHopf_orbit_correction C Q hQsym hQτ R hR sourceA sourcef hsourceAR hsourcefR
      hsourcef0 (by norm_num) (by norm_num)
  have hδJ : Metric.ball (0 : ℝ) δ ⊆ J :=
    (Metric.ball_subset_ball hδR.le).trans hRJ
  refine ⟨δ, hδ, hδJ, (1 + (a : ℝ) + (a : ℝ) ^ 2) * L, by positivity, U, hU, ?_⟩
  intro ε hε x
  rcases hspec ε hε x with ⟨_, hfixed, hlift, hbound⟩
  refine ⟨?_, hbound⟩
  by_cases hεzero : ε = 0
  · subst ε
    have heq : (fun y ↦ P (0, y) + U (0, y)) = (fun y ↦ P (0, y)) := by
      funext y
      rw [hU0 y, add_zero]
    rw [heq]
    simpa only [zero_pow (by omega : 3 ≠ 0), zero_pow (by omega : 4 ≠ 0),
      zero_smul, add_zero] using hresidual 0 hzero x
  · have hUε : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (fun y ↦ U (ε, y)) :=
      hU.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun y ↦ ⟨hε, mem_univ y⟩)
    have hpointfixed (y : EuclideanSpace ℝ (Fin a)) :
        (v (ε, x)).val.toFun y = Atilde (ε, freeHopfOrbitLift C x y)
          (balancedNormalizedResidualData ε
            (S3 (freeHopfOrbitLift C x y)) (S4 (freeHopfOrbitLift C x y))) +
        Atilde (ε, freeHopfOrbitLift C x y) ((balancedPairingDataCoordinates a).symm
          ((Q (v (ε, x)) (v (ε, x))).val.toFun y)) := by
      exact hfixed y
    have hm := freeHopf_fixed_branch_metric C
      (fun y ↦ P (ε, y)) (fun y ↦ U (ε, y)) (hPslice ε (hδJ hε)) hUε x
      (by norm_num) (by norm_num) ε S3 S4 (A ε) (fun y ↦ Atilde (ε, y)) (v (ε, x))
      hlift (fun y ↦ hgeometry ε (hδJ hε) (freeHopfOrbitLift C x y))
      (fun y ↦ hA ε (hδJ hε) hεzero (freeHopfOrbitLift C x y))
      (fun y ↦ hscale ε (hδJ hε) hεzero (freeHopfOrbitLift C x y)) hpointfixed
    have hm0 := hm 0
    rw [freeHopfOrbitLift_zero,
      freeHopf_geometry_eq_gram C _ ((hPslice ε (hδJ hε)).add hUε)] at hm0
    exact hm0

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.freeHopf_geometry_eq_gram
#print axioms GlobalEmbedding.Paper.freeHopf_balanced_correction
