import GlobalEmbedding.Paper.FreeBufferedPairingGluing
import GlobalEmbedding.Paper.FreeInductionNormalizedFrames
import GlobalEmbedding.Paper.FreeHopfUniformNormalizedMargins
import GlobalEmbedding.Paper.FreeInductionLimitingRank
import GlobalEmbedding.Paper.FreeInductionNormalizedFlowColumns

/-! Actual normalized inverse assembly is the remaining owned parent.
W5 exclusively supplies the accepted common-parameter/margin theorem.
Actual limiting-rank geometry is now exclusively W3; finite algebra moved to its own provider.
The complete same-fixed-data inverse candidate below awaits ROOT review and acceptance. -/

noncomputable section

namespace GlobalEmbedding.Paper



section RelativeGluing

open scoped ContDiff Manifold

variable {P H M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace H] {I : ModelWithCorners ℝ P H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The actual support buffer also works relative to an open common time domain. No regularity
or injectivity is required outside that domain or outside the corresponding curvature patch. -/
theorem free_weighted_patch_contMDiffOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : M → ℝ) (U : Set M) (hU : IsOpen U)
    (hχ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ U)
    (V : Set M) (hV : IsOpen V) (hs : tsupport χ ⊆ V)
    (B : M → F) (hB : ContMDiffOn I 𝓘(ℝ, F) ∞ B (U ∩ V)) :
    ContMDiffOn I 𝓘(ℝ, F) ∞ (fun x ↦ χ x • B x) U := by
  intro x hxU
  by_cases hx : x ∈ tsupport (fun y ↦ χ y • B y)
  · have hxV := hs (tsupport_smul_subset_left χ B hx)
    exact ((hχ.contMDiffAt (hU.mem_nhds hxU)).smul
      (hB.contMDiffAt ((hU.inter hV).mem_nhds ⟨hxU, hxV⟩))).contMDiffWithinAt
  · exact (ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const
      (notMem_tsupport_iff_eventuallyEq.1 hx)).contMDiffWithinAt

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine buffered Gram reconstruction is native smooth on the common open parameter
interval, requiring full rank only there. This is the exact domain needed by balanced correction. -/
theorem freeTwoPatchNormalizedInverse_contMDiffOn
    (κ : M → ℝ) (hκ : ContMDiff I 𝓘(ℝ, ℝ) ∞ κ) (d : ℝ) (hd : 0 < d)
    (U : Set M) (hU : IsOpen U)
    (prj : M → E →L[ℝ] E) (Bn Bf : M → V →L[ℝ] E)
    (Jn Jf : V →L[ℝ] V) (ε : M → ℝ)
    (hprj : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞ prj U)
    (hBn : ContMDiffOn I 𝓘(ℝ, V →L[ℝ] E) ∞ Bn (U ∩ {x | |κ x| < d}))
    (hBf : ContMDiffOn I 𝓘(ℝ, V →L[ℝ] E) ∞ Bf (U ∩ {x | d / 3 < |κ x|}))
    (hin : ∀ x ∈ U, |κ x| < d → Function.Injective (Bn x))
    (hif : ∀ x ∈ U, d / 3 < |κ x| → Function.Injective (Bf x))
    (hε : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ε U) :
    ContMDiffOn I 𝓘(ℝ, V →L[ℝ] E) ∞
      (freeTwoPatchNormalizedInverse κ d hd prj Bn Bf Jn Jf ε) U := by
  have hχ := freeInverseNearWeight_contMDiff κ hκ d hd
  have hnear := free_gram_patch_contMDiffOn (U ∩ {x | |κ x| < d}) Jn prj Bn ε
    (hprj.mono Set.inter_subset_left) hBn (fun x hx ↦ hin x hx.1 hx.2)
    (hε.mono Set.inter_subset_left)
  have hfar := free_gram_patch_contMDiffOn (U ∩ {x | d / 3 < |κ x|}) Jf
    (fun _ ↦ ContinuousLinearMap.id ℝ E) Bf ε contMDiffOn_const hBf
    (fun x hx ↦ hif x hx.1 hx.2) (hε.mono Set.inter_subset_left)
  exact (free_weighted_patch_contMDiffOn _ U hU hχ.contMDiffOn _
    (isOpen_lt hκ.continuous.abs continuous_const)
    (freeInverseNearWeight_tsupport κ hκ.continuous d hd) _ hnear).add
    (free_weighted_patch_contMDiffOn _ U hU (contMDiff_const.sub hχ).contMDiffOn _
      (isOpen_lt continuous_const hκ.continuous.abs)
      (freeInverseFarWeight_tsupport κ hκ.continuous d hd) _ hfar)

omit [TopologicalSpace M] in
/-- The same literal Gram/cutoff formula satisfies its true full-data scaled identity on the
common open parameter domain. Restrict the already proved pointwise identity to the given point;
no behavior of the Gram inverse outside the domain is needed. -/
theorem freeTwoPatchNormalizedInverse_scaled_identity_on
    (κ : M → ℝ) (d : ℝ) (hd : 0 < d) (U : Set M)
    (T : M → E →L[ℝ] V) (prj : M → E →L[ℝ] E) (Bn Bf : M → V →L[ℝ] E)
    (Jn Jf : V →L[ℝ] V) (hJn : Jn.comp Jn = Jn) (hJf : Jf.comp Jf = Jf)
    (ε : M → ℝ)
    (hin : ∀ x ∈ U, |κ x| < d → Function.Injective (Bn x))
    (hif : ∀ x ∈ U, d / 3 < |κ x| → Function.Injective (Bf x))
    (hTn : ∀ x ∈ U, |κ x| < d →
      (T x).comp (prj x) = (freeColumnScale Jn (ε x)).comp (Bn x).adjoint)
    (hTf : ∀ x ∈ U, d / 3 < |κ x| →
      T x = (freeColumnScale Jf (ε x)).comp (Bf x).adjoint) (x : M) (hx : x ∈ U) :
    (T x).comp (freeTwoPatchNormalizedInverse κ d hd prj Bn Bf Jn Jf ε x) =
      ε x • ContinuousLinearMap.id ℝ V := by
  simpa only [freeTwoPatchNormalizedInverse, freeInverseNearWeight] using
    freeTwoPatchNormalizedInverse_scaled_identity (fun _ : Unit ↦ κ x) continuous_const d hd
      (fun _ ↦ T x) (fun _ ↦ prj x) (fun _ ↦ Bn x) (fun _ ↦ Bf x) Jn Jf hJn hJf
      (fun _ ↦ ε x) (fun _ hp ↦ hin x hx hp) (fun _ hp ↦ hif x hx hp)
      (fun _ hp ↦ hTn x hx hp) (fun _ hp ↦ hTf x hx hp) ()

/-- Construct the full pairing inverse and its actual native smooth normalized extension on
an open common domain from the genuine two-patch Gram formulas. Scaling is asserted only away
from zero; the normalized value at zero is unrestricted. No inverse is among the inputs. -/
theorem free_two_patch_pairing_inverse_exists
    (κ : M → ℝ) (hκ : ContMDiff I 𝓘(ℝ, ℝ) ∞ κ) (d : ℝ) (hd : 0 < d)
    (U : Set M) (hU : IsOpen U)
    (T : M → E →L[ℝ] V) (prj : M → E →L[ℝ] E) (Bn Bf : M → V →L[ℝ] E)
    (Jn Jf : V →L[ℝ] V) (hJn : Jn.comp Jn = Jn) (hJf : Jf.comp Jf = Jf)
    (ε : M → ℝ)
    (hprj : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞ prj U)
    (hBn : ContMDiffOn I 𝓘(ℝ, V →L[ℝ] E) ∞ Bn (U ∩ {x | |κ x| < d}))
    (hBf : ContMDiffOn I 𝓘(ℝ, V →L[ℝ] E) ∞ Bf (U ∩ {x | d / 3 < |κ x|}))
    (hin : ∀ x ∈ U, |κ x| < d → Function.Injective (Bn x))
    (hif : ∀ x ∈ U, d / 3 < |κ x| → Function.Injective (Bf x))
    (hε : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ε U)
    (hTn : ∀ x ∈ U, |κ x| < d →
      (T x).comp (prj x) = (freeColumnScale Jn (ε x)).comp (Bn x).adjoint)
    (hTf : ∀ x ∈ U, d / 3 < |κ x| →
      T x = (freeColumnScale Jf (ε x)).comp (Bf x).adjoint) :
    ∃ A Atilde : M → V →L[ℝ] E,
      ContMDiffOn I 𝓘(ℝ, V →L[ℝ] E) ∞ Atilde U ∧
      ∀ x ∈ U, ε x ≠ 0 →
        (T x).comp (A x) = ContinuousLinearMap.id ℝ V ∧ Atilde x = ε x • A x := by
  let Ctilde := freeTwoPatchNormalizedInverse κ d hd prj Bn Bf Jn Jf ε
  let A (x : M) := (ε x)⁻¹ • Ctilde x
  refine ⟨A, Ctilde, freeTwoPatchNormalizedInverse_contMDiffOn κ hκ d hd U hU
    prj Bn Bf Jn Jf ε hprj hBn hBf hin hif hε, ?_⟩
  intro x hx hεx
  have hs := freeTwoPatchNormalizedInverse_scaled_identity_on κ d hd U
    T prj Bn Bf Jn Jf hJn hJf ε hin hif hTn hTf x hx
  change (T x).comp (Ctilde x) = ε x • ContinuousLinearMap.id ℝ V at hs
  constructor
  · change (T x).comp ((ε x)⁻¹ • Ctilde x) = ContinuousLinearMap.id ℝ V
    rw [ContinuousLinearMap.comp_smul, hs, smul_smul, inv_mul_cancel₀ hεx, one_smul]
  · change Ctilde x = ε x • ((ε x)⁻¹ • Ctilde x)
    rw [smul_smul, mul_inv_cancel₀ hεx, one_smul]

end RelativeGluing

#print axioms free_weighted_patch_contMDiffOn
#print axioms freeTwoPatchNormalizedInverse_contMDiffOn
#print axioms freeTwoPatchNormalizedInverse_scaled_identity_on
#print axioms free_two_patch_pairing_inverse_exists

section ActualInductionInverse

open scoped Manifold ContDiff
variable {m K : ℕ} (C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < C i)]
variable (H : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
variable (f : PlanarHopfSphere (C (Fin.last m)) → Planar)
variable (Z W : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))))
variable (hH : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
  𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ H)
variable (hf : MatrixPlanarSelectorProperties f)
variable (hZ : ContMDiff (freeHopfModel C)
  𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ Z)
variable (hW : ContMDiff (freeHopfModel C)
  𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ W)

include hH hf hZ hW in
/-- Construct the actual original pairing inverse and its native normalized extension on one
common open time interval. The two actual pointwise limiting-rank inputs are the separate W3
outputs; every smoothness, actual base annihilation, scale relation and uniformization is
already discharged here by canonical providers. The final fixed-data theorem below discharges
these rank inputs using W3's actual theorem; this connection alone is not full-parent acceptance. -/
theorem freeHopf_induction_inverse_of_limiting_rank (d0 : ℝ) (hd0 : 0 < d0)
    (hinjNear : ∀ x, |planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2| < d0 →
      Function.Injective (freeHopfInductionNearFrame C H f Z W (0, x)))
    (hinjFar : ∀ x, planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2 ≠ 0 →
      Function.Injective (freeHopfInductionFarFrame C H f Z W (0, x))) :
    ∃ d ε₀ μ : ℝ, d = d0 / 2 ∧ 0 < d ∧ 0 < ε₀ ∧ 0 < μ ∧
      ∃ A Atilde : ℝ × FreeHopfProduct C →
        EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (K + (2 + m))),
        ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
          𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
            EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ Atilde
              (Metric.ball (0 : ℝ) ε₀ ×ˢ Set.univ) ∧
        (∀ ε, |ε| < ε₀ → ε ≠ 0 → ∀ x,
          (balancedPairingMap (freePolynomialFamily (freeHopfInductionBase C H f) Z W ε)
            (freeHopfGenerator C) x).comp (A (ε, x)) = ContinuousLinearMap.id ℝ _ ∧
              Atilde (ε, x) = ε • A (ε, x)) ∧
        (∀ ε, |ε| < ε₀ → ∀ x,
          (|planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2| ≤ d →
            ∀ u, μ * ‖u‖ ≤ ‖freeHopfInductionNearFrame C H f Z W (ε, x) u‖) ∧
          (d / 3 ≤ |planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2| →
            ∀ u, μ * ‖u‖ ≤ ‖freeHopfInductionFarFrame C H f Z W (ε, x) u‖)) := by
  let κ (x : FreeHopfProduct C) :=
    planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2
  have hκ : ContMDiff (freeHopfModel C) 𝓘(ℝ, ℝ) ∞ κ :=
    hf.curvature_smooth.comp (contMDiff_snd.comp (freeHopfProductSplit_contMDiff C))
  have hBs := freeHopfInductionFrames_contMDiff C H f Z W hH hf hZ hW
  obtain ⟨d, ε₀, μ, hdeq, hd, hε₀, hμ, _, hn, hfar⟩ :=
    freeHopf_uniform_normalized_margins C κ hκ.continuous hd0
      (freeHopfInductionNearFrame C H f Z W) (freeHopfInductionFarFrame C H f Z W)
      hBs.1.continuous hBs.2.continuous hinjNear hinjFar
  let U : Set (ℝ × FreeHopfProduct C) := Metric.ball (0 : ℝ) ε₀ ×ˢ Set.univ
  have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_univ
  have htime {p : ℝ × FreeHopfProduct C} (hp : p ∈ U) : |p.1| < ε₀ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hp.1
  let prj (p : ℝ × FreeHopfProduct C) := freeInductionNearProjection K m
    (orbitDeriv planarHopfFlow f (freeHopfProductSplit C p.2).2)
  have hlast : ContMDiff (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      (planarHopfModel (C (Fin.last m))) ∞
      (fun p : ℝ × FreeHopfProduct C ↦ (freeHopfProductSplit C p.2).2) :=
    (contMDiff_snd.comp (freeHopfProductSplit_contMDiff C)).comp contMDiff_snd
  have hprj := (freeInductionNearProjection_selector_contMDiff K m _ f hf).comp hlast
  obtain ⟨A, Atilde, hAt, hA⟩ := free_two_patch_pairing_inverse_exists
    (fun p : ℝ × FreeHopfProduct C ↦ κ p.2) (hκ.comp contMDiff_snd) d hd U hU
    (fun p ↦ balancedPairingMap
      (freePolynomialFamily (freeHopfInductionBase C H f) Z W p.1) (freeHopfGenerator C) p.2)
    prj (freeHopfInductionNearFrame C H f Z W) (freeHopfInductionFarFrame C H f Z W)
    (freeCoordinateMask (freeNearColumnMask m)) (freeCoordinateMask (freeFarColumnMask m))
    (freeCoordinateMask_idempotent _) (freeCoordinateMask_idempotent _) Prod.fst
    hprj.contMDiffOn (hBs.1.contMDiffOn) (hBs.2.contMDiffOn)
    (fun p hp hk ↦ (hn p.1 (htime hp) p.2 hk.le).1)
    (fun p hp hk ↦ (hfar p.1 (htime hp) p.2 hk.le).1) contMDiff_fst.contMDiffOn
    (fun p _ _ ↦ freeHopfInductionNearFrame_adjoint_scale C H f Z W hH hf hZ hW p.1 p.2)
    (fun p _ _ ↦ freeHopfInductionFarFrame_adjoint_scale C H f Z W hH hf hZ hW p.1 p.2)
  refine ⟨d, ε₀, μ, hdeq, hd, hε₀, hμ, A, Atilde, hAt, ?_, ?_⟩
  · intro ε hε hne x
    exact hA (ε, x) ⟨by simpa [Metric.mem_ball, Real.dist_eq] using hε, Set.mem_univ x⟩ hne
  · intro ε hε x
    exact ⟨fun hx ↦ (hn ε hε x hx).2, fun hx ↦ (hfar ε hε x hx).2⟩

end ActualInductionInverse

#print axioms freeHopf_induction_inverse_of_limiting_rank

section FixedInductionData

open scoped Manifold ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
variable {m K : ℕ} (C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < C i)]

local instance freeInverseOldPositive (i : Fin m) :
    Fact (0 < freeHopfOldDimensions C i) := inferInstanceAs (Fact (0 < C i.castSucc))
local instance freeInverseMatrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  let normed := (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ))
  normed.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- On the SAME fixed induction data, construct the original full pairing inverse, a native
smooth normalized extension through zero, and one common genuine normalized-flow-column margin.
W3's actual limiting-rank theorems discharge both rank premises, W5 supplies the sole compact
uniformization, and W2's exact F3 equalities transfer the same bounds to the original columns.
No new matrix data, displacement, correction, frequency or pivot parameters are chosen.
Source: main.tex477–495. -/
theorem freeHopf_induction_pairing_inverse
    (H ν : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin K))
    (hIH : FreeSelectorProperties (freeHopfModel (freeHopfOldDimensions C))
      (freeHopfProductFlow (freeHopfOldDimensions C)) H ν)
    (f : PlanarHopfSphere (C (Fin.last m)) → Planar) (hf : MatrixPlanarSelectorProperties f)
    (P Q : PlanarHopfSphere (C (Fin.last m)) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel (C (Fin.last m)))
      𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (η : PlanarHopfSphere (C (Fin.last m)) → ℝ)
    (hη : ContMDiff (planarHopfModel (C (Fin.last m))) 𝓘(ℝ, ℝ) ∞ η)
    (δ d0 lam : ℝ) (hδ : 0 < δ) (hd0 : 0 < d0) (hlam : 0 < lam)
    (A n : FreeHopfProduct (freeHopfOldDimensions C) → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel (freeHopfOldDimensions C))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (hcoercive : ∀ x : FreeHopfProduct C, ∀ w, lam * ‖w‖ ^ 2 ≤
      ‖freePivotMixedFrame (freeHopfOldDimensions C) Q η A n δ
        (freeHopfProductSplit C x) w‖ ^ 2)
    (hpivot : ∀ x : FreeHopfProduct C,
      |planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2| < d0 →
      δ / 4 ≤ ⟪freePivotNormal (freeHopfOldDimensions C) Q η A n δ (freeHopfProductSplit C x),
        freePivotActiveSecond (freeHopfOldDimensions C) P Q η A n δ (freeHopfProductSplit C x)⟫)
    (W : FreeHopfProduct C → EuclideanSpace ℝ (Fin (K + (2 + m))))
    (hW : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ W) :
    let Z := freeHopfInductionZ C ν P Q η δ A n
    let F0 := freeHopfInductionBase C H f
    let κ := fun x ↦ planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2
    ∃ d ε₀ μ : ℝ, d = d0 / 2 ∧ 0 < d ∧ 0 < ε₀ ∧ 0 < μ ∧
      ∃ R Rtilde : ℝ × FreeHopfProduct C →
        EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (K + (2 + m))),
        ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
          𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
            EuclideanSpace ℝ (Fin (K + (2 + m)))) ∞ Rtilde
              (Metric.ball (0 : ℝ) ε₀ ×ˢ Set.univ) ∧
        (∀ ε, |ε| < ε₀ → ε ≠ 0 → ∀ x,
          IsBalancedPairingRightInverse (freePolynomialFamily F0 Z W ε)
            (freeHopfGenerator C) x (R (ε, x)) ∧ Rtilde (ε, x) = ε • R (ε, x)) ∧
        (∀ ε, 0 < ε → ε < ε₀ → ∀ x,
          (|κ x| ≤ d → ∀ u, μ * ‖u‖ ≤ ‖freeColumnOperator
            (freeNormalizedColumns
              (freeInductionNearProjection K m
                (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2))
              (freeNearColumnMask m) ε
              (freeFlowColumns (freeHopfProductFlow C) (freePolynomialFamily F0 Z W ε) x)) u‖) ∧
          (d / 3 ≤ |κ x| → ∀ u, μ * ‖u‖ ≤ ‖freeColumnOperator
            (freeNormalizedColumns (ContinuousLinearMap.id ℝ _) (freeFarColumnMask m) ε
              (freeFlowColumns (freeHopfProductFlow C)
                (freePolynomialFamily F0 Z W ε) x)) u‖)) := by
  let Z := freeHopfInductionZ C ν P Q η δ A n
  have hZ := freeHopfInductionZ_contMDiff C ν hIH.2.1 P Q hP hQ η hη δ A n hA hn
  have hnear : ∀ x, |planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2| < d0 →
      Function.Injective (freeHopfInductionNearFrame C H f Z W (0, x)) := by
    intro x hx
    exact free_induction_near_zero_injective C ν hIH.2.1 hIH.2.2.2.2.1 P Q hP hQ hPQ η hη δ
      A n hA hn H hIH.1 hIH.2.2.2.1 hIH.2.2.2.2.2 f hf
      (balancedPairingMap W (freeHopfGenerator C) x).adjoint lam x hlam
      (hcoercive x) (lt_of_lt_of_le (by linarith : 0 < δ / 4) (hpivot x hx))
  have hfar : ∀ x, planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2 ≠ 0 →
      Function.Injective (freeHopfInductionFarFrame C H f Z W (0, x)) := by
    intro x hx
    exact free_induction_far_zero_injective C ν hIH.2.1 hIH.2.2.2.2.1 P Q hP hQ hPQ η hη δ
      A n hA hn H hIH.1 hIH.2.2.2.1 hIH.2.2.2.2.2 f hf
      (balancedPairingMap W (freeHopfGenerator C) x).adjoint lam x hlam (hcoercive x) hx
  obtain ⟨d, ε₀, μ, hdeq, hd, hε₀, hμ, R, Rtilde, hRt, hR, hmargin⟩ :=
    freeHopf_induction_inverse_of_limiting_rank C H f Z W hIH.1 hf hZ hW d0 hd0 hnear hfar
  refine ⟨d, ε₀, μ, hdeq, hd, hε₀, hμ, R, Rtilde, hRt, hR, ?_⟩
  intro ε hε hsmall x
  have hmarg := hmargin ε (by simpa only [abs_of_pos hε] using hsmall) x
  have hnEq := freeHopfInductionNearPolynomial_eq_flowColumns C H ν hIH f hf P Q hP hQ
    η hη δ A n hA hn W hW ε (ne_of_gt hε) x
  have hfEq := freeHopfInductionFarPolynomial_eq_flowColumns C H ν hIH f hf P Q hP hQ
    η hη δ A n hA hn W hW ε (ne_of_gt hε) x
  constructor
  · intro hx u
    have hh := hmarg.1 hx u
    change μ * ‖u‖ ≤ ‖freeNormalizedColumnPolynomial _ _ _ _ _ ε u‖ at hh
    rw [hnEq] at hh
    exact hh
  · intro hx u
    have hh := hmarg.2 hx u
    change μ * ‖u‖ ≤ ‖freeNormalizedColumnPolynomial _ _ _ _ _ ε u‖ at hh
    rw [hfEq] at hh
    exact hh

end FixedInductionData

#print axioms freeHopf_induction_pairing_inverse
#print axioms freeInverseOldPositive
#print axioms freeInverseMatrixNormedTopology

end GlobalEmbedding.Paper
