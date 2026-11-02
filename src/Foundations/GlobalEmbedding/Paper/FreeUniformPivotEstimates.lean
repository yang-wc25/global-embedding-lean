import GlobalEmbedding.Paper.FreeCompactPivotPerturbation
import GlobalEmbedding.Paper.FreeCorrectionStability
import GlobalEmbedding.Paper.FreeHopfUnitComplements
import GlobalEmbedding.Paper.FreeActivePivotIdentity
import GlobalEmbedding.Paper.MatrixPlanarSelectorProperties

/-!
# Uniform mixed rank and active pivot on the actual Hopf product

Source: `main.tex`, thm:free, equations (4.5)–(4.6), lines455–470.
DAG: free-uniform-pivot-estimates. Exclusive W3 ownership recorded before edits.
The actual mixed columns are W2's literal displacement columns; their finite
Euclidean column operator is W5's accepted `freeColumnOperator`.
-/
noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise RealInnerProductSpace
namespace GlobalEmbedding.Paper

variable {m C : ℕ}
local instance freeUniformPivotMatrixNormedTopology (d : ℕ) :
    TopologicalSpace (Matrix (Fin d) (Fin d) ℝ) :=
  (inferInstance : NormedAddCommGroup (Matrix (Fin d) (Fin d) ℝ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The genuine zero-displacement mixed frame on the old product times active sphere. -/
def freePivotBaseFrame (Cs : Fin m → ℕ)
    (Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (A : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1)))
    (p : FreeHopfProduct Cs × PlanarHopfSphere C) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  freeColumnOperator (fun i ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2)
    (freeHopfDeriv Cs i A p.1))

/-- The genuine coefficient of delta in the mixed frame, retaining the XQ term. -/
def freePivotFramePerturbation (Cs : Fin m → ℕ)
    (Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (η : PlanarHopfSphere C → ℝ)
    (n : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1)))
    (p : FreeHopfProduct Cs × PlanarHopfSphere C) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  freeColumnOperator (fun i ↦
    orbitDeriv planarHopfFlow η p.2 • Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2)
      (freeHopfDeriv Cs i n p.1) +
    η p.2 • Matrix.toEuclideanCLM (𝕜 := ℝ) (orbitDeriv planarHopfFlow Q p.2)
      (freeHopfDeriv Cs i n p.1))

/-- The actual finite column operator of the same canonical mixed columns (4.5). -/
def freePivotMixedFrame (Cs : Fin m → ℕ)
    (Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (η : PlanarHopfSphere C → ℝ)
    (A n : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1))) (δ : ℝ)
    (p : FreeHopfProduct Cs × PlanarHopfSphere C) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  freeColumnOperator (fun i ↦ freeDisplacementMixedVector Q η δ
    (freeHopfDeriv Cs i A p.1) (freeHopfDeriv Cs i n p.1) p.2)

/-- The affine mixed frame is exactly the accepted compact-mechanism frame. -/
theorem freePivotMixedFrame_eq (Cs : Fin m → ℕ)
    (Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (η : PlanarHopfSphere C → ℝ)
    (A n : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1))) (δ : ℝ)
    (p : FreeHopfProduct Cs × PlanarHopfSphere C) :
    freePivotMixedFrame Cs Q η A n δ p =
      freeMixedFrame (freePivotBaseFrame Cs Q A) (freePivotFramePerturbation Cs Q η n) δ p := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [freePivotMixedFrame, freePivotBaseFrame, freePivotFramePerturbation,
    freeMixedFrame, add_apply, smul_apply, freeColumnOperator_apply,
    freeDisplacementMixedVector, freeDisplacementActiveVector, smul_add,
    smul_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_left_comm]

/-- The actual projected direction is defined using the literal mixed-column range. -/
def freePivotNormal (Cs : Fin m → ℕ)
    (Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (η : PlanarHopfSphere C → ℝ)
    (A n : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1))) (δ : ℝ)
    (p : FreeHopfProduct Cs × PlanarHopfSphere C) : EuclideanSpace ℝ (Fin (m + 1)) :=
  (LinearMap.range (freePivotMixedFrame Cs Q η A n δ p).toLinearMap)ᗮ.starProjection
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2) (n p.1))

/-- The pivot vector is the actual second active derivative of W2's same displacement. -/
def freePivotActiveSecond (Cs : Fin m → ℕ)
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (η : PlanarHopfSphere C → ℝ)
    (A n : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1))) (δ : ℝ)
    (p : FreeHopfProduct Cs × PlanarHopfSphere C) : EuclideanSpace ℝ (Fin (m + 1)) :=
  orbitDeriv planarHopfFlow
    (orbitDeriv planarHopfFlow (freeDisplacementVector P Q η δ (A p.1) (n p.1))) p.2

variable (Cs : Fin m → ℕ) [∀ i, Fact (0 < Cs i)] [Fact (0 < C)]

/-- The second active derivative is genuinely continuous jointly in both actual factors.
Proof: W2 gives native joint smoothness of its literal displacement. Twice apply
actual smooth orbit differentiation to the product's active factor action. -/
theorem freePivotActiveSecond_continuous
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (A n : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel Cs) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel Cs) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n) (δ : ℝ) :
    Continuous (freePivotActiveSecond Cs P Q η A n δ) := by
  let I := (freeHopfModel Cs).prod (planarHopfModel C)
  let R : ℝ → (FreeHopfProduct Cs × PlanarHopfSphere C) →
      (FreeHopfProduct Cs × PlanarHopfSphere C) := fun t p ↦ (p.1, planarHopfFlow t p.2)
  have hR : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × (FreeHopfProduct Cs × PlanarHopfSphere C) ↦ R p.1 p.2) :=
    contMDiff_snd.fst.prodMk ((planarHopfFlow_contMDiff C).comp
      (contMDiff_fst.prodMk contMDiff_snd.snd))
  have hV := freeDisplacementVector_joint_contMDiff P Q hP hQ η hη A n hA hn δ
  have hXX := contMDiff_orbitDeriv R hR _ (contMDiff_orbitDeriv R hR _ hV)
  exact hXX.continuous

/-- Both coefficients of the actual affine mixed frame are continuous on the
whole compact product. Native smoothness of A,n supplies the old derivatives. -/
theorem freePivotFrames_continuous
    (Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (A n : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel Cs) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel Cs) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n) :
    Continuous (freePivotBaseFrame Cs Q A) ∧
      Continuous (freePivotFramePerturbation Cs Q η n) := by
  let F := EuclideanSpace ℝ (Fin (m + 1))
  let T := FreeHopfProduct Cs × PlanarHopfSphere C
  have hop (v : T → Fin m → F) (hv : ∀ i, Continuous (fun p ↦ v p i)) :
      Continuous (fun p ↦ freeColumnOperator (v p)) := by
    apply continuous_finsetSum Finset.univ
    intro i _
    exact (ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin m)) F
      (EuclideanSpace.proj i)).continuous.comp (hv i)
  have hact (M : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
      (hM : Continuous M) (v : T → F) (hv : Continuous v) :
      Continuous (fun p : T ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (M p.2) (v p)) := by
    let L := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (m + 1))).toAlgEquiv.toLinearEquiv
      |>.toContinuousLinearEquiv
    exact (L.continuous.comp (hM.comp continuous_snd)).clm_apply hv
  have hXQ := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) Q hQ
  have hXη := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) η hη
  constructor
  · apply hop
    intro i
    exact hact Q hQ.continuous _
      ((freeHopfDeriv_contMDiff Cs A hA i).continuous.comp continuous_fst)
  · apply hop
    intro i
    have hd := (freeHopfDeriv_contMDiff Cs n hn i).continuous.comp
      (continuous_fst : Continuous (Prod.fst : T → FreeHopfProduct Cs))
    exact ((hXη.continuous.comp continuous_snd).smul (hact Q hQ.continuous _ hd)).add
      ((hη.continuous.comp continuous_snd).smul (hact _ hXQ.continuous _ hd))

omit [∀ i, Fact (0 < Cs i)] [Fact (0 < C)] in
/-- Orthogonality transports the genuine independent old derivative columns
and their same unit cofactor to the actual zero-displacement mixed frame. -/
theorem freePivotBaseFrame_properties
    (Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (horth : ∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin (m + 1)) ℝ)
    (A n : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1)))
    (hLI : ∀ x, LinearIndependent ℝ (fun i ↦ freeHopfDeriv Cs i A x))
    (hunit : ∀ x, ‖n x‖ = 1)
    (hperp : ∀ x i, ⟪n x, freeHopfDeriv Cs i A x⟫ = 0)
    (p : FreeHopfProduct Cs × PlanarHopfSphere C) :
    Function.Injective (freePivotBaseFrame Cs Q A p) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2) (n p.1)‖ = 1 ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2) (n p.1) ∈
        (LinearMap.range (freePivotBaseFrame Cs Q A p).toLinearMap)ᗮ := by
  have hQi (z : PlanarHopfSphere C) :
      Function.Injective (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z)) := by
    apply (injective_iff_map_eq_zero (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q z))).mpr
    intro v hv
    have hh := matrix_action_inner_orthogonal (Q z) (horth z) v v
    rw [hv, inner_zero_left, real_inner_self_eq_norm_sq] at hh
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  refine ⟨?_, ?_, ?_⟩
  · apply (freeColumnOperator_injective_iff _).mpr
    exact (hLI p.1).map' _ (LinearMap.ker_eq_bot.mpr (hQi p.2))
  · have hh := matrix_action_inner_orthogonal (Q p.2) (horth p.2) (n p.1) (n p.1)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hunit] at hh
    nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2) (n p.1))]
  · rw [Submodule.mem_orthogonal']
    rintro v ⟨w, rfl⟩
    change ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2) (n p.1),
      freePivotBaseFrame Cs Q A p w⟫ = 0
    rw [freePivotBaseFrame, freeColumnOperator_apply, inner_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [real_inner_smul_right, matrix_action_inner_orthogonal _ (horth p.2), hperp,
      mul_zero]

/-- One positive displacement and curvature buffer work on the entire genuine
old-product times active sphere. All rank, projection error and pivot bounds
are derived from the same native A,n,P,Q,eta. No perturbed rank, desired pivot,
point-dependent constant or inverse-curvature estimate is assumed. -/
theorem free_uniform_mixed_pivot
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (hQ : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ Q)
    (hPQ : ∀ z, orbitDeriv planarHopfFlow P z = Q z)
    (horth : ∀ z, Q z ∈ Matrix.specialOrthogonalGroup (Fin (m + 1)) ℝ)
    (η κ : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η) (hκ : Continuous κ)
    (hstationary : ∀ z, κ z = 0 → orbitDeriv planarHopfFlow Q z = 0)
    (haccel : ∀ z, κ z = 0 →
      orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow η) z = 1)
    (A n : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1)))
    (hA : ContMDiff (freeHopfModel Cs) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A)
    (hn : ContMDiff (freeHopfModel Cs) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n)
    (hLI : ∀ x, LinearIndependent ℝ (fun i ↦ freeHopfDeriv Cs i A x))
    (hunit : ∀ x, ‖n x‖ = 1)
    (hperp : ∀ x i, ⟪n x, freeHopfDeriv Cs i A x⟫ = 0) :
    ∃ δ₀ d₀ lam K : ℝ, 0 < δ₀ ∧ 0 < d₀ ∧ 0 < lam ∧ 0 < K ∧
      ∀ p : FreeHopfProduct Cs × PlanarHopfSphere C,
      (∀ v, lam * ‖v‖ ^ 2 ≤ ‖freePivotMixedFrame Cs Q η A n δ₀ p v‖ ^ 2) ∧
      ‖freePivotNormal Cs Q η A n δ₀ p -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2) (n p.1)‖ ≤ K * δ₀ ∧
      (κ p.2 = 0 → |⟪freePivotNormal Cs Q η A n δ₀ p,
        freePivotActiveSecond Cs P Q η A n δ₀ p⟫ - δ₀| ≤ K * δ₀ ^ 2) ∧
      (|κ p.2| < d₀ → δ₀ / 4 ≤ ⟪freePivotNormal Cs Q η A n δ₀ p,
        freePivotActiveSecond Cs P Q η A n δ₀ p⟫) := by
  let T := FreeHopfProduct Cs × PlanarHopfSphere C
  let u : T → EuclideanSpace ℝ (Fin (m + 1)) := fun p ↦
    Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2) (n p.1)
  let b : T → EuclideanSpace ℝ (Fin (m + 1)) := fun p ↦ u p + η p.2 •
    Matrix.toEuclideanCLM (𝕜 := ℝ)
      (orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow Q) p.2) (n p.1)
  let L := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (m + 1))).toAlgEquiv.toLinearEquiv
    |>.toContinuousLinearEquiv
  have hu : Continuous u :=
    (L.continuous.comp (hQ.continuous.comp continuous_snd)).clm_apply
      (hn.continuous.comp continuous_fst)
  have hXQ := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) Q hQ
  have hXXQ := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) _ hXQ
  have hb : Continuous b := hu.add ((hη.continuous.comp continuous_snd).smul
    ((L.continuous.comp (hXXQ.continuous.comp continuous_snd)).clm_apply
      (hn.continuous.comp continuous_fst)))
  have hbase := freePivotBaseFrame_properties Cs Q horth A n hLI hunit hperp
  have hfactor (δ : ℝ) (p : T) (hz : κ p.2 = 0) :
      freePivotActiveSecond Cs P Q η A n δ p = δ • b p :=
    free_active_second_displacement_factor P Q hP hQ hPQ η hη δ (A p.1) (n p.1)
      p.2 (hstationary p.2 hz) (haccel p.2 hz)
  have hpivot (p : T) (hz : κ p.2 = 0) : ⟪u p, b p⟫ = 1 := by
    dsimp only [u, b]
    rw [inner_add_right, real_inner_smul_right,
      free_orthogonal_second_self_pair_zero Q hQ horth (n p.1) p.2 (hstationary p.2 hz),
      mul_zero, add_zero, matrix_action_inner_orthogonal _ (horth p.2),
      real_inner_self_eq_norm_sq, hunit]
    norm_num
  obtain ⟨δ₀, d₀, lam, K, hδ, hd, hlam, hK, hbound⟩ := free_compact_pivot_choice
    (freePivotBaseFrame Cs Q A) (freePivotFramePerturbation Cs Q η n) u b
    (freePivotActiveSecond Cs P Q η A n) (fun p : T ↦ κ p.2)
    (freePivotFrames_continuous Cs Q hQ η hη A n hA hn).1
    (freePivotFrames_continuous Cs Q hQ η hη A n hA hn).2 hu hb
    (freePivotActiveSecond_continuous Cs P Q hP hQ η hη A n hA hn)
    (hκ.comp continuous_snd) (fun p ↦ (hbase p).1)
    (fun p ↦ (hbase p).2.1.le) (fun p ↦ (hbase p).2.2) hfactor hpivot
  refine ⟨δ₀, d₀, lam, K, hδ, hd, hlam, hK, ?_⟩
  intro p
  simpa only [freePivotNormal, freePivotMixedFrame_eq, freeMixedNormal, u] using hbound p

omit [∀ i, Fact (0 < Cs i)] [Fact (0 < C)] in
/-- The actual uniform coercivity and positive projected pivot give independence
of all mixed columns together with the active second column on the near patch. -/
theorem freePivot_rank_of_bounds
    (P Q : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (η : PlanarHopfSphere C → ℝ)
    (A n : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1))) (δ lam : ℝ)
    (p : FreeHopfProduct Cs × PlanarHopfSphere C) (hlam : 0 < lam)
    (hbound : ∀ v, lam * ‖v‖ ^ 2 ≤ ‖freePivotMixedFrame Cs Q η A n δ p v‖ ^ 2)
    (hpivot : 0 < ⟪freePivotNormal Cs Q η A n δ p,
      freePivotActiveSecond Cs P Q η A n δ p⟫) :
    LinearIndependent ℝ (fun i ↦ freeDisplacementMixedVector Q η δ
      (freeHopfDeriv Cs i A p.1) (freeHopfDeriv Cs i n p.1) p.2) ∧
    LinearIndependent ℝ (Fin.snoc (fun i ↦ freeDisplacementMixedVector Q η δ
      (freeHopfDeriv Cs i A p.1) (freeHopfDeriv Cs i n p.1) p.2)
      (freePivotActiveSecond Cs P Q η A n δ p)) := by
  have hinj : Function.Injective (freePivotMixedFrame Cs Q η A n δ p) := by
    apply (injective_iff_map_eq_zero (freePivotMixedFrame Cs Q η A n δ p)).mpr
    intro v hv
    have hh := hbound v
    rw [hv, norm_zero, zero_pow (by omega)] at hh
    have hnonpos : ‖v‖ ^ 2 ≤ 0 := (mul_le_mul_iff_of_pos_left hlam).mp (by simpa using hh)
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  have hLI := (freeColumnOperator_injective_iff _).mp hinj
  refine ⟨hLI, linearIndependent_finSnoc.mpr ⟨hLI, ?_⟩⟩
  intro hspan
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  have hmem : freePivotActiveSecond Cs P Q η A n δ p ∈
      LinearMap.range (freePivotMixedFrame Cs Q η A n δ p).toLinearMap := by
    refine ⟨WithLp.toLp 2 g, ?_⟩
    change freePivotMixedFrame Cs Q η A n δ p (WithLp.toLp 2 g) = _
    simpa [freePivotMixedFrame, freeColumnOperator_apply] using hg
  have hnmem := Submodule.starProjection_apply_mem
    (LinearMap.range (freePivotMixedFrame Cs Q η A n δ p).toLinearMap)ᗮ
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2) (n p.1))
  have hz : ⟪freePivotNormal Cs Q η A n δ p,
      freePivotActiveSecond Cs P Q η A n δ p⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hmem hnmem
  linarith

/-- With the same actual matrix-selector data, genuinely construct immersive
coordinates and their unit cofactor, then obtain one common delta and buffer.
Here Q is literally XP and kappa is the actual curvature of the same f.
Proof: the accepted actual partial immersion/ordered cofactor theorem supplies
A,n. Smooth actual differentiation supplies Q; the full uniform theorem derives
all mixed coercivity, projection error and near-zero pivot bounds. -/
theorem free_matrix_uniform_pivot_exists
    (f : PlanarHopfSphere C → Planar) (hf : MatrixPlanarSelectorProperties f)
    (P : PlanarHopfSphere C → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hP : ContMDiff (planarHopfModel C) 𝓘(ℝ, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ∞ P)
    (η : PlanarHopfSphere C → ℝ)
    (hη : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ η)
    (horth : ∀ z, orbitDeriv planarHopfFlow P z ∈
      Matrix.specialOrthogonalGroup (Fin (m + 1)) ℝ)
    (hstationary : ∀ z, planarOrbitCurvature planarHopfFlow f z = 0 →
      orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow P) z = 0)
    (haccel : ∀ z, planarOrbitCurvature planarHopfFlow f z = 0 →
      orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow η) z = 1) :
    let Q := orbitDeriv planarHopfFlow P
    ∃ A n : FreeHopfProduct Cs → EuclideanSpace ℝ (Fin (m + 1)),
      ContMDiff (freeHopfModel Cs) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A ∧
      ContMDiff (freeHopfModel Cs) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ n ∧
      (∀ x, LinearIndependent ℝ (fun i ↦ freeHopfDeriv Cs i A x)) ∧
      (∀ x, ‖n x‖ = 1) ∧ (∀ x i, ⟪n x, freeHopfDeriv Cs i A x⟫ = 0) ∧
      ∃ δ₀ d₀ lam K : ℝ, 0 < δ₀ ∧ 0 < d₀ ∧ 0 < lam ∧ 0 < K ∧
        ∀ p : FreeHopfProduct Cs × PlanarHopfSphere C,
        (∀ v, lam * ‖v‖ ^ 2 ≤ ‖freePivotMixedFrame Cs Q η A n δ₀ p v‖ ^ 2) ∧
        ‖freePivotNormal Cs Q η A n δ₀ p -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (Q p.2) (n p.1)‖ ≤ K * δ₀ ∧
        (planarOrbitCurvature planarHopfFlow f p.2 = 0 →
          |⟪freePivotNormal Cs Q η A n δ₀ p,
            freePivotActiveSecond Cs P Q η A n δ₀ p⟫ - δ₀| ≤ K * δ₀ ^ 2) ∧
        (|planarOrbitCurvature planarHopfFlow f p.2| < d₀ →
          δ₀ / 4 ≤ ⟪freePivotNormal Cs Q η A n δ₀ p,
            freePivotActiveSecond Cs P Q η A n δ₀ p⟫) := by
  dsimp only
  obtain ⟨A, n, hA, hn, hLI, hunit, hperp, _⟩ :=
    freeHopf_immersive_coordinates_unit_cofactor Cs
  refine ⟨A, n, hA, hn, hLI, hunit, hperp, ?_⟩
  exact free_uniform_mixed_pivot Cs P (orbitDeriv planarHopfFlow P) hP
    (contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) P hP)
    (fun _ ↦ rfl) horth η (planarOrbitCurvature planarHopfFlow f) hη
    hf.curvature_smooth.continuous hstationary haccel A n hA hn hLI hunit hperp

end GlobalEmbedding.Paper
