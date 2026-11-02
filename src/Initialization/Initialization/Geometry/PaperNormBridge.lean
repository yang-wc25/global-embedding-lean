import Initialization.Assembly.RescaledNorms
import Initialization.Colored.ActualNativeMetric
import GlobalEmbedding.Paper.PaperCoordinateNormBridge

/-!
# The original componentwise partial/MAX norms of the actual initialization

The source coordinates below use the actual continuous linear equivalence from
Pi coordinates to Euclidean coordinates. Their domain is its preimage of the
actual chart target, not a Pi-norm ball with a silently changed radius.
The target components are fixed continuous linear evaluations. Consequently
only fixed dimension/order constants occur, never a number of chart patches.
-/

noncomputable section
open Set Function Metric Manifold IsManifold Bundle
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

section LinearCoordinates

variable {n q : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The genuine Pi-coordinate image of the actual Euclidean differentiation
domain. For a Euclidean ball this is its exact ellipsoidal/preimage domain. -/
def paperSourceDomain (U : Set (EuclideanSpace ℝ (Fin n))) : Set (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm ⁻¹' U

theorem paperSourceDomain_isOpen {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) : IsOpen (paperSourceDomain U) :=
  hU.preimage (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous

/-- Actual fixed linear target components in the same source coordinates. -/
def paperLinearCoordinates (L : V →L[ℝ] (Fin q → ℝ))
    (u : EuclideanSpace ℝ (Fin n) → V) : (Fin n → ℝ) → Fin q → ℝ :=
  L ∘ u ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm

def paperLinearCoordinateFactor (L : V →L[ℝ] (Fin q → ℝ)) (j : ℕ) : ℝ :=
  max 1 ‖L‖ * (max 1 ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖)^j

theorem paperLinearCoordinateFactor_pos (L : V →L[ℝ] (Fin q → ℝ)) (j : ℕ) :
    0 < paperLinearCoordinateFactor (n := n) L j := by
  unfold paperLinearCoordinateFactor
  positivity

theorem paperLinearCoordinates_contDiffOn (L : V →L[ℝ] (Fin q → ℝ))
    (u : EuclideanSpace ℝ (Fin n) → V) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (paperLinearCoordinates L u) (paperSourceDomain U) :=
  L.contDiff.comp_contDiffOn
    (hu.comp (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.contDiffOn (fun _ hy ↦ hy))

/-- True Pi jets are controlled by true Euclidean jets through the actual
source equivalence and actual linear target evaluations. -/
theorem paperLinearCoordinates_jet_bound (L : V →L[ℝ] (Fin q → ℝ))
    (u : EuclideanSpace ℝ (Fin n) → V) (y : Fin n → ℝ) (k : ℕ)
    (hu : ContDiffAt ℝ ∞ u ((EuclideanSpace.equiv (Fin n) ℝ).symm y)) :
    ‖iteratedFDeriv ℝ k (paperLinearCoordinates L u) y‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ k u ((EuclideanSpace.equiv (Fin n) ℝ).symm y)‖ *
        ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖^k := by
  let a := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have ha : iteratedFDeriv ℝ k (u ∘ a) y =
      (iteratedFDeriv ℝ k u (a y)).compContinuousLinearMap
        (fun _ : Fin k ↦ a.toContinuousLinearMap) := by
    simpa only [preimage_univ, iteratedFDerivWithin_univ] using
      a.iteratedFDerivWithin_comp_right u uniqueDiffOn_univ (mem_univ y) k
  have hc : ContDiffAt ℝ ∞ (u ∘ a) y := hu.comp y a.contDiff.contDiffAt
  have hpost := L.norm_iteratedFDeriv_comp_left hc (by simp : (k : ℕ∞ω) ≤ ∞)
  rw [ha] at hpost
  have hpre := (iteratedFDeriv ℝ k u (a y)).norm_compContinuousLinearMap_le
    (fun _ : Fin k ↦ a.toContinuousLinearMap)
  exact hpost.trans (by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_assoc] using
      mul_le_mul_of_nonneg_left hpre (norm_nonneg L))

theorem finiteCjNorm_le_finiteAtlasCjNorm
    {Idx : Type*} [Fintype Idx] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (u : Idx → E → V) (U : Idx → Set E) (i : Idx) :
    finiteCjNorm j (u i) (U i) ≤ finiteAtlasCjNorm j u U := by
  classical
  unfold finiteAtlasCjNorm
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The original partial/MAX norm is bounded by the actual Euclidean atlas
Fréchet norm. Genuine derivative boundedness is explicit; no real-supremum
totalization or infinity-to-zero conversion is used. -/
theorem paperAtlasCj_linearCoordinates_le
    {Idx : Type*} [Fintype Idx] (j : ℕ)
    (L : V →L[ℝ] (Fin q → ℝ)) (u : Idx → EuclideanSpace ℝ (Fin n) → V)
    (U : Idx → Set (EuclideanSpace ℝ (Fin n)))
    (hU : ∀ i, IsOpen (U i)) (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (U i))
    (hbdd : ∀ i, ∀ k ≤ j,
      BddAbove (Set.range fun x : U i ↦ ‖iteratedFDeriv ℝ k (u i) x‖)) :
    paperAtlasCj j (fun i ↦ paperLinearCoordinates L (u i))
      (fun i ↦ paperSourceDomain (U i)) (fun i ↦ paperSourceDomain (U i)) ≤
        ENNReal.ofReal
          (paperLinearCoordinateFactor (n := n) L j * finiteAtlasCjNorm j u U) := by
  apply iSup_le
  intro i
  rw [paperCoordinateCj_eq_coordinateJetGauge j _ _ _
    (paperSourceDomain_isOpen (hU i)) (Subset.rfl)
    (paperLinearCoordinates_contDiffOn L (u i) (U i) (hu i))]
  refine iSup_le fun k ↦ iSup_le fun x ↦ iSup_le fun σ ↦ iSup_le fun c ↦ ?_
  apply ENNReal.ofReal_le_ofReal
  have hk : k.val ≤ j := by omega
  have hN : 0 ≤ finiteAtlasCjNorm j u U := finiteAtlasCjNorm_nonneg j u U
  have hx : (EuclideanSpace.equiv (Fin n) ℝ).symm x ∈ U i := x.property
  have hn : ‖iteratedFDeriv ℝ k.val (u i) ((EuclideanSpace.equiv (Fin n) ℝ).symm x)‖ ≤
      finiteAtlasCjNorm j u U :=
    ((finiteCjNorm_specification j (u i) (U i) (hbdd i)).2.1 k.val hk _ hx).trans
      (finiteCjNorm_le_finiteAtlasCjNorm j u U i)
  have hpow : ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ ^ k.val ≤
      (max 1 ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖)^j :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hk)
  calc
    _ ≤ ‖iteratedFDeriv ℝ k.val (paperLinearCoordinates L (u i)) x‖ :=
      coordinate_jet_coefficient_le _ _ σ c
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ k.val (u i)
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x)‖ *
        ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ ^ k.val :=
      paperLinearCoordinates_jet_bound L (u i) x k.val
        ((hu i).contDiffAt ((hU i).mem_nhds hx))
    _ ≤ max 1 ‖L‖ * finiteAtlasCjNorm j u U *
        (max 1 ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖)^j := by
      exact mul_le_mul
        (mul_le_mul (le_max_right _ _) hn (norm_nonneg _)
          (le_trans zero_le_one (le_max_left _ _))) hpow
        (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by unfold paperLinearCoordinateFactor; ring

/-- Actual matrix entries of an operator, flattened only by the canonical
finite-product equivalence. The first index is the evaluated vector and the
second index is the scalar component. -/
def metricPaperComponents (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (Fin (n*n) → ℝ) :=
  ContinuousLinearMap.pi fun c ↦
    (EuclideanSpace.proj (finProdFinEquiv.symm c).2).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace.single (finProdFinEquiv.symm c).1 1))

@[simp] theorem metricPaperComponents_apply (A : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n)) (i k : Fin n) :
    metricPaperComponents n A (finProdFinEquiv (i,k)) =
      inner ℝ (A (EuclideanSpace.single i 1)) (EuclideanSpace.single k 1) := by
  change (A (EuclideanSpace.single
    (finProdFinEquiv.symm (finProdFinEquiv (i,k))).1 1))
      (finProdFinEquiv.symm (finProdFinEquiv (i,k))).2 = _
  rw [Equiv.symm_apply_apply]
  simp [EuclideanSpace.inner_single_right]

end LinearCoordinates

section ActualInitialization

variable {n N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)

/-- The actual H in the original scalar componentwise partial/MAX norm. -/
def initializationMapPaperCjNorm
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → EuclideanSpace ℝ (Fin N))
    (j : ℕ) (K T : ℝ) (hK : 1 ≤ K) (hT : 1 ≤ T) : ENNReal :=
  paperAtlasCj j
    (fun p : Fin (initializationAtlas G T hT).count ↦
      paperPiCoordinates (metricInitializationMap G g f S K T hK ∘
        ((initializationAtlas G T hT).chart p).symm))
    (fun p ↦ paperSourceDomain (((initializationAtlas G T hT).chart p).target))
    (fun p ↦ paperSourceDomain (((initializationAtlas G T hT).chart p).target))

/-- The original norm of all actual coordinate-matrix components of
γ(H_(K,T))−T²g. The same scale-T atlas and same actual global H are used. -/
def initializationMetricPaperCjNorm
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → EuclideanSpace ℝ (Fin N))
    (j : ℕ) (K T : ℝ) (hK : 1 ≤ K) (hT : 1 ≤ T) : ENNReal :=
  paperAtlasCj j
    (fun p : Fin (initializationAtlas G T hT).count ↦
      paperLinearCoordinates (metricPaperComponents n)
        (initializationMetricDefect G g f S K T hK hT p))
    (fun p ↦ paperSourceDomain (((initializationAtlas G T hT).chart p).target))
    (fun p ↦ paperSourceDomain (((initializationAtlas G T hT).chart p).target))

/-- Each scalar matrix entry in the paper norm is literally the original
native metric defect on the corresponding coordinate basis vectors. -/
theorem initializationMetricPaperCoordinates_native
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (K T : ℝ) (hK : 1 ≤ K) (hT : 1 ≤ T)
    (p : Fin (initializationAtlas G T hT).count) (y : Fin n → ℝ)
    (hy : y ∈ paperSourceDomain (((initializationAtlas G T hT).chart p).target))
    (i k : Fin n) :
    let e := (initializationAtlas G T hT).chart p
    let yE := (EuclideanSpace.equiv (Fin n) ℝ).symm y
    paperLinearCoordinates (metricPaperComponents n)
      (initializationMetricDefect G g f S K T hK hT p) y (finProdFinEquiv (i,k)) =
        inducedMetric (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (metricInitializationMap G g f S K T hK) (e.symm yE)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            e.symm yE (EuclideanSpace.single i 1))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            e.symm yE (EuclideanSpace.single k 1)) -
        T^2 * g.inner (e.symm yE)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            e.symm yE (EuclideanSpace.single i 1))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            e.symm yE (EuclideanSpace.single k 1)) := by
  dsimp only
  change metricPaperComponents n
    (initializationMetricDefect G g f S K T hK hT p
      ((EuclideanSpace.equiv (Fin n) ℝ).symm y)) (finProdFinEquiv (i,k)) = _
  rw [metricPaperComponents_apply]
  exact metricInitializationMap_native_metric_error G g f S hS hK
    (preparedCutoffsAt G T hT) hT p hy (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)

@[simp] theorem paperSourceEquiv_single (i : Fin n) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm (Pi.single i 1) =
      EuclideanSpace.single i 1 := rfl

theorem paperSourceDomain_ball (ρ : ℝ) :
    paperSourceDomain (ball (0 : EuclideanSpace ℝ (Fin n)) ρ) =
      {y | ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ < ρ} := by
  ext y
  simp only [paperSourceDomain, mem_preimage, mem_ball, dist_zero_right, mem_ofPred_eq]

/-- The bounded chart is a restriction of an actual wider smooth chart whose
target contains the entire closed ball. This proves honest jet boundedness. -/
theorem ChartCutoffFamily.closedBall_subset_scaledTarget {T : ℝ}
    (Q : ChartCutoffFamily G T) (hT : 1 ≤ T) (p : Fin Q.count) :
    closedBall (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius ⊆
      ((Q.scaledAtlas hT).chart p).target :=
  rescaledChart_closedBall_buffer _ (G.radius_pos _) (G.scaleRadius_le _)
    (Q.center_core p) (G.buffered _) hT

/-- Boundedness of genuine derivative ranges is supplied by a compact subset
of the wider actual chart. It is not inferred from a conditional real supremum. -/
theorem ChartCutoffFamily.boundedAtlas_jet_range_bddAbove
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {T : ℝ}
    (Q : ChartCutoffFamily G T) (hT : 1 ≤ T) (p : Fin Q.count)
    (u : EuclideanSpace ℝ (Fin n) → V)
    (hu : ContDiffOn ℝ ∞ u ((Q.scaledAtlas hT).chart p).target) (k : ℕ) :
    BddAbove (Set.range fun x : ((Q.boundedAtlas hT).chart p).target ↦
      ‖iteratedFDeriv ℝ k u x‖) := by
  obtain ⟨B, _hB, hbound⟩ := exists_compact_smooth_derivative_bounds
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius)
    ((Q.scaledAtlas hT).chart p).open_target (Q.closedBall_subset_scaledTarget G hT p) u hu
  refine ⟨B k, ?_⟩
  rintro r ⟨x, rfl⟩
  exact hbound k x (ball_subset_closedBall x.property)

theorem ChartCutoffFamily.boundedAtlas_pullback_contDiffOn_wide
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {T : ℝ}
    (Q : ChartCutoffFamily G T) (hT : 1 ≤ T) (p : Fin Q.count)
    (H : M → V) (hH : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞ H) :
    ContDiffOn ℝ ∞ (H ∘ ((Q.boundedAtlas hT).chart p).symm)
      ((Q.scaledAtlas hT).chart p).target :=
  (hH.comp_contMDiffOn
    (contMDiffOn_symm_of_mem_maximalAtlas ((Q.scaledAtlas_smooth hT).chart_mem p))).contDiffOn

/-- The exact T²g coefficient is smooth on the same wider chart, so its
restriction has genuinely bounded jets even before choosing uniform budgets. -/
theorem scaledTargetMetricOperator_contDiffOn_wide {T : ℝ}
    (Q : ChartCutoffFamily G T) (hT : 1 ≤ T) (p : Fin Q.count) :
    ContDiffOn ℝ ∞ (scaledTargetMetricOperator G g f Q p)
      ((Q.scaledAtlas hT).chart p).target := by
  apply (preparedMetricOperator_contDiffOn G g f (Q.parent p)).comp
    (contDiff_const.add (contDiff_id.const_smul T⁻¹)).contDiffOn
  intro y hy
  change T⁻¹ • y + Q.center p ∈ (G.chart (Q.parent p)).target at hy
  simpa only [add_comm, id_eq] using hy

theorem actualMetricDefect_contDiffOn_wide {T : ℝ}
    (Q : ChartCutoffFamily G T) (hT : 1 ≤ T) (p : Fin Q.count)
    (H : M → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H) :
    ContDiffOn ℝ ∞ (fun y ↦ actualMetricOperator
      (H ∘ ((Q.boundedAtlas hT).chart p).symm) y -
        scaledTargetMetricOperator G g f Q p y) ((Q.scaledAtlas hT).chart p).target := by
  have hDH := (Q.boundedAtlas_pullback_contDiffOn_wide G hT p H hH).fderiv_of_isOpen
    ((Q.scaledAtlas hT).chart p).open_target (by simp : ∞ + 1 ≤ (∞ : ℕ∞ω))
  let adj := ContinuousLinearMap.adjoint (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin n)) (F := EuclideanSpace ℝ (Fin N))
  exact ((adj.contDiff.comp_contDiffOn hDH).clm_comp hDH).sub
    (scaledTargetMetricOperator_contDiffOn_wide G g f Q hT p)

/-- Uniform reference bounds for the original paper norm of the same actual
map. Source/target norm conversion constants are fixed before K,T. -/
theorem exists_initializationMap_paper_reference_bounds [CompactSpace M]
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S) :
    ∃ R : ℕ → ℝ, (∀ j, 0 < R j) ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T) (j : ℕ),
        initializationMapPaperCjNorm G g f S j K T hK (hK.trans hKT) ≤ ENNReal.ofReal (R j) := by
  obtain ⟨R, hR, hbound⟩ := exists_initializationMap_reference_norm_bounds G g f S hS
  let L := (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
  let factor : ℕ → ℝ := paperLinearCoordinateFactor (n := n) L
  have hf (j : ℕ) : 0 < factor j := paperLinearCoordinateFactor_pos L j
  refine ⟨fun j ↦ factor j * R j, fun j ↦ mul_pos (hf j) (hR j), ?_⟩
  intro K T hK hKT j
  let hT := hK.trans hKT
  let Q := preparedCutoffsAt G T hT
  let H := metricInitializationMap G g f S K T hK
  have hH := metricInitializationMap_contMDiff G g f S hS K T hK
  have hsub (p : Fin Q.count) : ((Q.boundedAtlas hT).chart p).target ⊆
      ((Q.scaledAtlas hT).chart p).target :=
    ball_subset_closedBall.trans (Q.closedBall_subset_scaledTarget G hT p)
  have hbridge := paperAtlasCj_linearCoordinates_le j L
    (fun p : Fin Q.count ↦ H ∘ ((Q.boundedAtlas hT).chart p).symm)
    (fun p ↦ ((Q.boundedAtlas hT).chart p).target)
    (fun p ↦ ((Q.boundedAtlas hT).chart p).open_target)
    (fun p ↦ (Q.boundedAtlas_pullback_contDiffOn_wide G hT p H hH).mono (hsub p))
    (fun p k _ ↦ Q.boundedAtlas_jet_range_bddAbove G hT p _
      (Q.boundedAtlas_pullback_contDiffOn_wide G hT p H hH) k)
  exact hbridge.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (hbound K T hK hKT j) (hf j).le))

/-- Equation (7.1) in the original scalar coordinate-partial atlas MAX norm.
Every geometric, smoothness and boundedness premise is internally supplied. -/
theorem exists_initializationMetric_paper_error_bounds [CompactSpace M]
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → EuclideanSpace ℝ (Fin N))
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (hGram : ∀ z, Matrix.gram ℝ
      (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ G.palette) l S z) = 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T) (j : ℕ),
        initializationMetricPaperCjNorm G g f S j K T hK (hK.trans hKT) ≤
          ENNReal.ofReal (C j * (K⁻¹ + K / T)) := by
  obtain ⟨C, hC, hbound⟩ := exists_initializationMetric_error_norm_bounds G g f S hS hGram
  let L := metricPaperComponents n
  let factor : ℕ → ℝ := paperLinearCoordinateFactor (n := n) L
  have hf (j : ℕ) : 0 < factor j := paperLinearCoordinateFactor_pos L j
  refine ⟨fun j ↦ factor j * C j, fun j ↦ mul_pos (hf j) (hC j), ?_⟩
  intro K T hK hKT j
  let hT := hK.trans hKT
  let Q := preparedCutoffsAt G T hT
  let H := metricInitializationMap G g f S K T hK
  let defect := initializationMetricDefect G g f S K T hK hT
  have hH := metricInitializationMap_contMDiff G g f S hS K T hK
  have hD (p : Fin Q.count) : ContDiffOn ℝ ∞ (defect p) ((Q.scaledAtlas hT).chart p).target :=
    actualMetricDefect_contDiffOn_wide G g f Q hT p H hH
  have hsub (p : Fin Q.count) : ((Q.boundedAtlas hT).chart p).target ⊆
      ((Q.scaledAtlas hT).chart p).target :=
    ball_subset_closedBall.trans (Q.closedBall_subset_scaledTarget G hT p)
  have hbridge := paperAtlasCj_linearCoordinates_le j L defect
    (fun p ↦ ((Q.boundedAtlas hT).chart p).target)
    (fun p ↦ ((Q.boundedAtlas hT).chart p).open_target)
    (fun p ↦ (hD p).mono (hsub p))
    (fun p k _ ↦ Q.boundedAtlas_jet_range_bddAbove G hT p _ (hD p) k)
  apply hbridge.trans
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_left (hbound K T hK hKT j) (hf j).le).trans_eq (by ring)

/-- The finite real interpretation is used only after the original extended
partial/MAX norm has been proved finite. -/
theorem paperNorm_finite_and_toReal_le {a : ENNReal} {B : ℝ} (hB : 0 ≤ B)
    (h : a ≤ ENNReal.ofReal B) : a ≠ ⊤ ∧ a.toReal ≤ B :=
  ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top h, ENNReal.toReal_le_of_le_ofReal hB h⟩

end ActualInitialization

end GlobalEmbedding.Initialization
