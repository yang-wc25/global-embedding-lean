import GlobalEmbedding.Paper.CollarRealGramSmallForcingAnalyticCorrection
import GlobalEmbedding.Paper.CollarHopfGaussianQuantitativeData
import GlobalEmbedding.Paper.CollarGaussianAnalyticRestriction
import GlobalEmbedding.Paper.CollarCofactorBalancedAlignment
import GlobalEmbedding.Paper.FreeHopfOrbitBranchEquivariance
import GlobalEmbedding.Paper.FreeHopfBalancedCorrection
import GlobalEmbedding.Paper.FreeNormalizedColumnStabilityBridge
import GlobalEmbedding.Paper.CollarHopfColumnSubtraction

/-!
# The original global native analytic exact free Hopf seed

Source: `main.tex`, Proposition `prop:collar`, proof lines 522–534.
W4 exclusive global assembly, registered before edits; W2 supplies the sole packing/Q.
The original ambient maximum norm is transported by its actual CLE, without an isometry claim.
-/

noncomputable section
open Set Filter WithLp Matrix
open scoped Topology Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Restrict the accepted analytic Gaussian to the SAME literal ambient F.
This is only coordinate composition, with no new width or approximation choice. -/
theorem collarHopf_literal_gaussian_contDiff {a N : ℕ} (C : Fin a → ℕ)
    (f0 F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (hf0 : Continuous f0) (hc : HasCompactSupport f0) (ε : ℝ)
    (hF : ∀ p, F p = ∫ y : EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C)),
      ((Real.pi * ε) ^ (-(CollarHopfAmbientDim C : ℝ) / 2) *
        Real.exp (-‖collarHopfAmbientCoordinates C p - y‖ ^ 2 / ε)) •
          f0 ((collarHopfAmbientCoordinates C).symm y)) : ContDiff ℝ ω F := by
  let e := collarHopfAmbientCoordinates C
  have hg := collar_gaussian_analytic_restriction ε (f0 ∘ e.symm)
    (hf0.comp e.symm.continuous) (hc.comp_homeomorph e.symm.toHomeomorph)
  simpa only [Function.comp_def, e, ← hF] using
    (hg.contDiff (n := ω)).comp e.contDiff

/-- The actual ambient point and actual orbit time in the finite real coordinates of69.
This only transports coordinates; it does not define another action or another atlas. -/
def collarHopfAmbientSourceParameter {a : ℕ} (C : Fin a → ℕ)
    (z : Fin (CollarHopfAmbientDim C + a) → ℝ) :
    FreeHopfAmbientSpace C × (Fin a → ℝ) :=
  ((collarHopfAmbientCoordinates C).symm
    (toLp 2 (fun i ↦ z (Fin.castAdd a i))), fun j ↦ z (Fin.natAdd _ j))

/-- The69 matrix source is the original pairing matrix at the actual ambient orbit point. -/
def collarHopfAmbientGramSource {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (z : Fin (CollarHopfAmbientDim C + a) → ℝ) :
    Matrix (Fin (freeSymmetricColumnCount a + a)) (Fin N) ℝ :=
  collarAmbientHopfPairingMatrix C F
    (collarAmbientHopfAction C (collarHopfAmbientSourceParameter C z).2
      (collarHopfAmbientSourceParameter C z).1)

/-- The raw source is the original OLD Gram minus identity in cofactor order.
There is no half here: the accepted69 theorem inserts that half exactly once. -/
def collarHopfAmbientRawSource {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (z : Fin (CollarHopfAmbientDim C + a) → ℝ) :
    Fin (freeSymmetricColumnCount a + a) → ℝ :=
  fun r ↦ match (freeCofactorColumnOrder a).symm r with
    | Sum.inl _ => 0
    | Sum.inr ij => collarAmbientHopfMetricDefect C F
        (collarAmbientHopfAction C (collarHopfAmbientSourceParameter C z).2
          (collarHopfAmbientSourceParameter C z).1) ij.val.1 ij.val.2

/-- Finite coordinate transport to the genuine ambient parameter is analytic. -/
theorem collarHopfAmbientSourceParameter_contDiff {a : ℕ} (C : Fin a → ℕ) :
    ContDiff ℝ ω (collarHopfAmbientSourceParameter C) := by
  have hb : ContDiff ℝ ω (fun z : Fin (CollarHopfAmbientDim C + a) → ℝ ↦
      toLp 2 (fun i : Fin (CollarHopfAmbientDim C) ↦ z (Fin.castAdd a i))) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (CollarHopfAmbientDim C) ↦ ℝ)).symm.contDiff.comp
      (contDiff_pi.mpr (fun i ↦ contDiff_apply ℝ (fun _ ↦ ℝ) (Fin.castAdd a i)))
  exact ((collarHopfAmbientCoordinates C).symm.contDiff.comp hb).prodMk
    (contDiff_pi.mpr (fun j ↦ contDiff_apply ℝ (fun _ ↦ ℝ) (Fin.natAdd _ j)))

/-- Appending the original base and orbit coordinates changes neither actual parameter. -/
theorem collarHopfAmbientSourceParameter_append {a : ℕ} (C : Fin a → ℕ)
    (p : EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C))) (y : Fin a → ℝ) :
    collarHopfAmbientSourceParameter C (Fin.append (ofLp p) y) =
      ((collarHopfAmbientCoordinates C).symm p, y) := by
  simp [collarHopfAmbientSourceParameter]

/-- Actual analytic F gives both actual69 sources analytic on the whole real parameter space.
Only existing source analyticity and the actual finite coordinate map are composed. -/
theorem collarHopfAmbientSources_analyticAt {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F)
    (z : Fin (CollarHopfAmbientDim C + a) → ℝ) :
    (∀ i j, AnalyticAt ℝ (fun q ↦ collarHopfAmbientGramSource C F q i j) z) ∧
      AnalyticAt ℝ (collarHopfAmbientRawSource C F) z := by
  have hT := (collarAmbientHopfPairingMatrix_joint_contDiff C F hF).comp
    (collarHopfAmbientSourceParameter_contDiff C)
  have hH := (collarAmbientHopfMetricDefect_joint_contDiff C F hF).comp
    (collarHopfAmbientSourceParameter_contDiff C)
  constructor
  · intro i j
    exact ((contDiff_apply ℝ (fun _ ↦ ℝ) j).comp
      ((contDiff_apply ℝ (fun _ ↦ Fin N → ℝ) i).comp hT)).contDiffAt.analyticAt
  · apply ContDiffAt.analyticAt
    apply ContDiff.contDiffAt
    apply contDiff_pi.mpr
    intro r
    simp only [collarHopfAmbientRawSource]
    split
    · exact contDiff_const
    · rename_i ij hij
      exact (contDiff_apply ℝ (fun _ ↦ ℝ) ij.val.2).comp
        ((contDiff_apply ℝ (fun _ ↦ Fin a → ℝ) ij.val.1).comp hH)

/-- Actual integer periodicity holds for every ambient base, not just on the sphere product. -/
theorem collarHopfAmbientSources_integer_periodic {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (z : Fin (CollarHopfAmbientDim C + a) → ℝ) (t : Fin a → ℤ) :
    collarHopfAmbientGramSource C F
        (z + Fin.append (fun _ : Fin (CollarHopfAmbientDim C) ↦ 0) (fun j ↦ (t j : ℝ))) =
      collarHopfAmbientGramSource C F z ∧
    collarHopfAmbientRawSource C F
        (z + Fin.append (fun _ : Fin (CollarHopfAmbientDim C) ↦ 0) (fun j ↦ (t j : ℝ))) =
      collarHopfAmbientRawSource C F z := by
  have hp : collarHopfAmbientSourceParameter C
      (z + Fin.append (fun _ : Fin (CollarHopfAmbientDim C) ↦ 0) (fun j ↦ (t j : ℝ))) =
      ((collarHopfAmbientSourceParameter C z).1,
        fun j ↦ (collarHopfAmbientSourceParameter C z).2 j + (t j : ℝ)) := by
    simp [collarHopfAmbientSourceParameter, Fin.append_left, Fin.append_right]
  constructor
  · simp only [collarHopfAmbientGramSource, hp]
    exact collarAmbientHopfPairingMatrix_integer_periodic C F _ _ t
  · funext r
    simp only [collarHopfAmbientRawSource, hp]
    rcases (freeCofactorColumnOrder a).symm r with i | ij
    · rfl
    · rw [collarAmbientHopfMetricDefect_integer_periodic]

/-- The literal flattened coefficient of the SAME transpose/Gram inverse. -/
def collarHopfAmbientInverseSource {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (z : Fin (CollarHopfAmbientDim C + a) → ℝ) :
    Fin (N * (freeSymmetricColumnCount a + a)) → ℝ :=
  fun q ↦
    let T := collarHopfAmbientGramSource C F z
    (T.transpose * (T * T.transpose)⁻¹)
      (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

/-- The actual operator norm of the sole accepted cofactor Q, with explicit spaces. -/
def collarHopfCofactorQNorm (a N : ℕ) : ℝ :=
  ContinuousLinearMap.opNorm (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
    (F := LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 (1 / 2 : ℝ))
    (collarCofactorQuadraticDataOperator (by norm_num) (by norm_num))

/-- Instantiate the full accepted69 endpoint on the actual ambient Hopf sources.

The actual center coefficient/forcing lifts and common multiplier bound are the41c6 data.
The explicit uniform threshold is below the actual69 center threshold; no unrelated
existential radii are identified. Nearby solutions retain the original linear norm bound
and native joint analyticity. This intermediate does not assert the global seed. -/
theorem collarHopf_actual_local_analytic_correction {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F)
    (p₀ : EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C)))
    (hbase : ∀ y : Fin a → ℝ,
      let T := collarHopfAmbientGramSource C F (Fin.append (ofLp p₀) y)
      (T * T.transpose).det ≠ 0)
    (coeff : LittlePeriodicCAlphaFunction a (N * (freeSymmetricColumnCount a + a))
      2 (1 / 2 : ℝ))
    (h : LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 (1 / 2 : ℝ))
    (hc : ∀ y, coeff.val.toFun y = toLp 2
      (collarHopfAmbientInverseSource C F (Fin.append (ofLp p₀) (ofLp y))))
    (hh : ∀ y, h.val.toFun y = toLp 2
      (collarHopfAmbientRawSource C F (Fin.append (ofLp p₀) (ofLp y))))
    (K : ℝ) (_hK : 0 ≤ K)
    (hbound : ∀ mult :
      LittlePeriodicCAlphaFunction a (N * (freeSymmetricColumnCount a + a)) 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ),
      (∀ A v y, (mult A v).val.toFun y =
        hilbertSchmidtCoordinateEvaluation (freeSymmetricColumnCount a + a) N
          (A.val.toFun y) (v.val.toFun y)) → ‖mult coeff‖ ≤ K)
    (hsmall : ‖h‖ < (1 / (4 * (K * collarHopfCofactorQNorm a N + 1))) / (K + 1)) :
    let Q := collarCofactorQuadraticDataOperator (a := a) (N := N)
      (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    ∃ (A : EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C)) →
        LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 (1 / 2 : ℝ) →L[ℝ]
        LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
      (H : EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C)) →
        LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 (1 / 2 : ℝ))
      (u : EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C)) →
        LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
      (W : Set (EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C)))),
      IsOpen W ∧ p₀ ∈ W ∧
      (∀ p ∈ W,
        (∀ v y, (A p v).val.toFun y =
          hilbertSchmidtCoordinateEvaluation (freeSymmetricColumnCount a + a) N
            (toLp 2 (collarHopfAmbientInverseSource C F
              (Fin.append (ofLp p) (ofLp y)))) (v.val.toFun y)) ∧
        (∀ y, (H p).val.toFun y = toLp 2
          (collarHopfAmbientRawSource C F (Fin.append (ofLp p) (ofLp y)))) ∧
        ‖u p‖ ≤ 2 * (K + 1) * ‖H p‖ ∧
        A p ((1 / 2 : ℝ) • H p + Q (u p) (u p)) = u p) ∧
      let _charted := periodicFlatTorusChartedSpace a
      ContMDiffOn ((𝓘(ℝ, EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C)))).prod
        (𝓘(ℝ, EuclideanSpace ℝ (Fin a)))) (𝓘(ℝ, EuclideanSpace ℝ (Fin N))) ω
        (fun z : EuclideanSpace ℝ (Fin (CollarHopfAmbientDim C)) ×
          PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)) ↦
          littlePeriodicCAlphaTorusValue (u z.1) z.2) (W ×ˢ univ) := by
  let b := CollarHopfAmbientDim C
  let M := freeSymmetricColumnCount a + a
  let Q := collarCofactorQuadraticDataOperator (a := a) (N := N)
    (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨V₀, hV₀, hpV₀, hsub, hright, AR, HR, mult, hAR, hHR, hsource, hmult,
    hρ, hδ, hbranch⟩ := collar_real_gram_small_forcing_analytic_correction
      (collarHopfAmbientGramSource C F) (collarHopfAmbientRawSource C F)
      univ isOpen_univ (ofLp p₀) (mem_univ _)
      (fun z _ ↦ (collarHopfAmbientSources_analyticAt C F hF z).1)
      (fun z _ ↦ (collarHopfAmbientSources_analyticAt C F hF z).2)
      (fun z _ t ↦ (collarHopfAmbientSources_integer_periodic C F z t).1)
      (fun z _ t ↦ (collarHopfAmbientSources_integer_periodic C F z t).2)
      hbase Q (collarCofactorQuadraticDataOperator_translate (by norm_num) (by norm_num))
  let p₀R := collarEuclideanRealEquiv (b + a)
    (toLp 2 (Fin.append (ofLp p₀) (fun _ : Fin a ↦ (0 : ℝ))))
  have hc0 : AR p₀R = coeff := by
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext y
    rw [hc]
    change (AR p₀R).val.toFun y = toLp 2 (fun q ↦
      let T := collarHopfAmbientGramSource C F (Fin.append (ofLp p₀) (ofLp y))
      (T.transpose * (T * T.transpose)⁻¹)
        (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)
    simpa [p₀R, b, collarEuclideanRealEquiv] using hsource.self_of_nhds.1 y
  have hh0 : HR p₀R = h := by
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext y
    rw [hh]
    simpa [p₀R, b, collarEuclideanRealEquiv] using hsource.self_of_nhds.2 y
  have hAn : ‖mult (AR p₀R)‖ ≤ K := by rw [hc0]; exact hbound mult hmult
  have hQN : 0 ≤ collarHopfCofactorQNorm a N := by
    exact Real.sInf_nonneg (fun c hc ↦ hc.1)
  have hsmall0 : ‖HR p₀R‖ <
      (1 / (4 * (‖mult (AR p₀R)‖ * collarHopfCofactorQNorm a N + 1))) /
        (‖mult (AR p₀R)‖ + 1) := by
    rw [hh0]
    apply hsmall.trans_le
    apply div_le_div₀
    · positivity
    · apply one_div_le_one_div_of_le
      · positivity
      · nlinarith [hQN]
    · positivity
    · linarith
  obtain ⟨u, W, hW, hpW, hpoint, _, hnative⟩ := hbranch hsmall0
  refine ⟨fun p ↦ mult (AR (collarRealJointParameter b a (p, 0))),
    fun p ↦ HR (collarRealJointParameter b a (p, 0)), u, W, hW, hpW, ?_, hnative⟩
  intro p hp
  obtain ⟨_, hAp, hHp, _, _, _, hnorm, hfix, _⟩ := hpoint p hp
  refine ⟨?_, hHp, ?_, hfix⟩
  · intro v y
    rw [hmult, hAp]
    rfl
  · exact hnorm.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- Actual orbit-related ambient source parameters evaluate at the SAME native point.
This is coordinate cancellation followed by the accepted original inclusion/action identity. -/
theorem collarHopfAmbientSource_native_point {a : ℕ} (C : Fin a → ℕ)
    (x : FreeHopfProduct C) (y : Fin a → ℝ) :
    let p := collarHopfAmbientCoordinates C (freeHopfAmbientInclusion C x)
    let q := collarHopfAmbientSourceParameter C (Fin.append (ofLp p) y)
    collarAmbientHopfAction C q.2 q.1 =
      freeHopfAmbientInclusion C (freeHopfRealAction C y x) := by
  dsimp only
  rw [collarHopfAmbientSourceParameter_append]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  exact collarAmbientHopfAction_inclusion C y x

/-- The actual inverse/raw source at orbit time y is the zero-time source at the shifted point.
These are source identities, before any correction or compatibility is constructed. -/
theorem collarHopfAmbientSources_native_orbit {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (x : FreeHopfProduct C) (y : Fin a → ℝ) :
    let p := fun x ↦ collarHopfAmbientCoordinates C (freeHopfAmbientInclusion C x)
    collarHopfAmbientInverseSource C F (Fin.append (ofLp (p x)) y) =
      collarHopfAmbientInverseSource C F
        (Fin.append (ofLp (p (freeHopfRealAction C y x))) 0) ∧
    collarHopfAmbientRawSource C F (Fin.append (ofLp (p x)) y) =
      collarHopfAmbientRawSource C F
        (Fin.append (ofLp (p (freeHopfRealAction C y x))) 0) := by
  dsimp only
  have hx := collarHopfAmbientSource_native_point C x y
  have hy := collarHopfAmbientSource_native_point C (freeHopfRealAction C y x) 0
  simp only [freeHopfRealAction_zero] at hy
  constructor
  · funext q
    simp only [collarHopfAmbientInverseSource, collarHopfAmbientGramSource, hx, hy]
  · funext r
    simp only [collarHopfAmbientRawSource, hx, hy]

/-- Actual pointwise41c6 data construct a global native analytic correction with its true
complete orbit lift. All local branches come from the accepted69 theorem; compatibility
and orbit covariance follow from the accepted strict-small uniqueness results. -/
theorem collarHopf_actual_global_analytic_correction {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F)
    (coeff : FreeHopfProduct C →
      LittlePeriodicCAlphaFunction a (N * (freeSymmetricColumnCount a + a)) 2 (1 / 2 : ℝ))
    (h : FreeHopfProduct C →
      LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 (1 / 2 : ℝ))
    (K B δ : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B) (_hδ : 0 < δ)
    (hbase : ∀ x : FreeHopfProduct C, ∀ y : Fin a → ℝ,
      let T := collarHopfAmbientGramSource C F
        (Fin.append (ofLp (collarHopfAmbientCoordinates C (freeHopfAmbientInclusion C x))) y)
      (T * T.transpose).det ≠ 0)
    (hc : ∀ x y, (coeff x).val.toFun y = toLp 2
      (collarHopfAmbientInverseSource C F (Fin.append
        (ofLp (collarHopfAmbientCoordinates C (freeHopfAmbientInclusion C x))) (ofLp y))))
    (hh : ∀ x y, (h x).val.toFun y = toLp 2
      (collarHopfAmbientRawSource C F (Fin.append
        (ofLp (collarHopfAmbientCoordinates C (freeHopfAmbientInclusion C x))) (ofLp y))))
    (hbound : ∀ x, ∀ mult :
      LittlePeriodicCAlphaFunction a (N * (freeSymmetricColumnCount a + a)) 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ),
      (∀ A v y, (mult A v).val.toFun y =
        hilbertSchmidtCoordinateEvaluation (freeSymmetricColumnCount a + a) N
          (A.val.toFun y) (v.val.toFun y)) → ‖mult (coeff x)‖ ≤ K)
    (hsmall : ∀ x, ‖h x‖ < δ)
    (hthreshold : δ ≤ (1 / (4 * (K * collarHopfCofactorQNorm a N + 1))) / (K + 1))
    (hstrict : 4 * K * B * (K + 1) * δ < (1 / 2 : ℝ))
    (hquad : ∀ v w : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ),
      ‖collarCofactorQuadraticDataOperator (by norm_num) (by norm_num) v w‖ ≤
        B * ‖v‖ * ‖w‖) :
    let Q := collarCofactorQuadraticDataOperator (a := a) (N := N)
      (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    ∃ (mult :
        LittlePeriodicCAlphaFunction a (N * (freeSymmetricColumnCount a + a)) 2 (1 / 2 : ℝ) →L[ℝ]
        LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 (1 / 2 : ℝ) →L[ℝ]
        LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
      (v : FreeHopfProduct C → LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
      (U : FreeHopfProduct C → EuclideanSpace ℝ (Fin N)),
      (∀ A v y, (mult A v).val.toFun y =
        hilbertSchmidtCoordinateEvaluation (freeSymmetricColumnCount a + a) N
          (A.val.toFun y) (v.val.toFun y)) ∧
      ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω U ∧
      ∀ x, ‖v x‖ ≤ 2 * (K + 1) * ‖h x‖ ∧
        mult (coeff x) ((1 / 2 : ℝ) • h x + Q (v x) (v x)) = v x ∧
        ∀ y, U (freeHopfOrbitLift C x y) = (v x).val.toFun y := by
  let b := CollarHopfAmbientDim C
  let M := freeSymmetricColumnCount a + a
  let p := fun x ↦ collarHopfAmbientCoordinates C (freeHopfAmbientInclusion C x)
  let Q := collarCofactorQuadraticDataOperator (a := a) (N := N)
    (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨_, _, mult, hmult, _⟩ := balanced_holder_multiplication_bounded
    (a := a) (M := M) (N := N) (k := 2) (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hlocal (x : FreeHopfProduct C) := collarHopf_actual_local_analytic_correction
    C F hF (p x) (hbase x) (coeff x) (h x) (hc x) (hh x) K hK (hbound x)
      ((hsmall x).trans_le hthreshold)
  choose A H u W hW hpW hspec hnative using hlocal
  have hHeq (x z : FreeHopfProduct C) (hz : p z ∈ W x) : H x (p z) = h z := by
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext y
    exact ((hspec x (p z) hz).2.1 y).trans (hh z y).symm
  have hAeq (x z : FreeHopfProduct C) (hz : p z ∈ W x) :
      A x (p z) = mult (coeff z) := by
    apply ContinuousLinearMap.ext
    intro w
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext y
    rw [(hspec x (p z) hz).1, hmult, hc]
  have hsol (x z : FreeHopfProduct C) (hz : p z ∈ W x) :
      ‖u x (p z)‖ ≤ 2 * (K + 1) * ‖h z‖ ∧
      mult (coeff z) ((1 / 2 : ℝ) • h z + Q (u x (p z)) (u x (p z))) = u x (p z) := by
    have hs := (hspec x (p z) hz).2.2
    rw [hHeq x z hz, hAeq x z hz] at hs
    exact hs
  have hlin (x : FreeHopfProduct C) (w : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
      (hw : ‖w‖ ≤ 2 * (K + 1) * ‖h x‖) :
      ‖(2 : ℝ) • (mult (coeff x)).comp (Q w)‖ < 1 := by
    have hQw : ‖Q w‖ ≤ B * ‖w‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg w))
      intro z
      exact hquad w z
    have hKn := hbound x mult hmult
    calc
      ‖(2 : ℝ) • (mult (coeff x)).comp (Q w)‖ ≤
          2 * ‖(mult (coeff x)).comp (Q w)‖ := by
            simpa only [Real.norm_ofNat] using
              ContinuousLinearMap.opNorm_smul_le (2 : ℝ) ((mult (coeff x)).comp (Q w))
      _ ≤ 2 * (K * (B * ‖w‖)) := by
        gcongr
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hKn hQw (ContinuousLinearMap.opNorm_nonneg (Q w)) hK)
      _ ≤ 4 * K * B * (K + 1) * δ := by
        have hhδ := (hsmall x).le
        have hwδ : ‖w‖ ≤ 2 * (K + 1) * δ :=
          hw.trans (mul_le_mul_of_nonneg_left hhδ (by positivity))
        nlinarith [mul_nonneg hK hB]
      _ < 1 := hstrict.trans (by norm_num)
  let v := fun x ↦ u x (p x)
  have hv (x : FreeHopfProduct C) := hsol x x (hpW x)
  have hsame (x z : FreeHopfProduct C) (hz : p z ∈ W x) : u x (p z) = v z := by
    have hs := hsol x z hz
    apply balanced_fixed_small_unique Q
      (collarCofactorQuadraticDataOperator_symmetric (by norm_num) (by norm_num))
      (mult (coeff z)) ((mult (coeff z)) ((1 / 2 : ℝ) • h z))
      (u x (p z)) (v z)
    · simpa only [map_add] using hs.2.symm
    · simpa only [map_add] using (hv z).2.symm
    · exact hlin z _ hs.1
    · exact hlin z _ (hv z).1
  let U := fun x ↦ (v x).val.toFun 0
  have hU : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω U := by
    intro x
    let _charted := periodicFlatTorusChartedSpace a
    have hp : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin b)) ω p :=
      (collarHopfAmbientCoordinates C).contDiff.contMDiff.comp
        (collarHopfAmbientInclusion_omega C)
    have he : ContMDiffAt (freeHopfModel C)
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin b))).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin a)))) ω
        (fun z : FreeHopfProduct C ↦ (p z, (0 : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))))) x :=
      hp.contMDiffAt.prodMk contMDiffAt_const
    have ha := ((hnative x).contMDiffAt
      ((hW x).prod isOpen_univ |>.mem_nhds ⟨hpW x, mem_univ _⟩)).comp x he
    apply ha.congr_of_eventuallyEq
    filter_upwards [hp.continuous.continuousAt.preimage_mem_nhds ((hW x).mem_nhds (hpW x))]
      with z hz
    change (v z).val.toFun 0 = littlePeriodicCAlphaTorusValue (u x (p z)) 0
    rw [hsame x z hz]
    have hzero : (toLp 2 (fun _ : Fin a ↦ (0 : AddCircle (1 : ℝ)))) =
        (0 : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) := by
      apply PiLp.ext
      intro i
      rfl
    simpa only [PiLp.zero_apply, AddCircle.coe_zero, hzero] using
      (littlePeriodicCAlphaTorusValue_lift (v z) (0 : EuclideanSpace ℝ (Fin a))).symm
  refine ⟨mult, v, U, hmult, hU, ?_⟩
  intro x
  refine ⟨(hv x).1, (hv x).2, ?_⟩
  intro y
  let sourceA := fun x ↦ hilbertSchmidtCoordinateEvaluation M N ((coeff x).val.toFun 0)
  let sourceh := fun x ↦ (h x).val.toFun 0
  have hcoeffOrbit (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) :
      (coeff x).val.toFun y = (coeff (freeHopfRealAction C (ofLp y) x)).val.toFun 0 := by
    rw [hc, hc, (collarHopfAmbientSources_native_orbit C F x (ofLp y)).1]
    rfl
  have hhOrbit (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) :
      (h x).val.toFun y = sourceh (freeHopfRealAction C (ofLp y) x) := by
    dsimp only [sourceh]
    rw [hh, hh, (collarHopfAmbientSources_native_orbit C F x (ofLp y)).2]
    rfl
  let sourcef := fun x ↦ sourceA x ((1 / 2 : ℝ) • sourceh x)
  have hf (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) :
      (mult (coeff x) ((1 / 2 : ℝ) • h x)).val.toFun y =
        sourcef (freeHopfRealAction C (ofLp y) x) := by
    rw [hmult, hcoeffOrbit]
    change _ = sourceA _ ((1 / 2 : ℝ) • sourceh _)
    congr 1
    change ((1 / 2 : ℝ) • (h x).val).toFun y = _
    rw [(periodicCAlpha_pointwise_operations a M 2 (1 / 2 : ℝ)).2.2]
    exact congrArg ((1 / 2 : ℝ) • ·) (hhOrbit x y)
  have hAm (x : FreeHopfProduct C) (w) (y : EuclideanSpace ℝ (Fin a)) :
      (mult (coeff x) w).val.toFun y =
        sourceA (freeHopfRealAction C (ofLp y) x) (w.val.toFun y) := by
    rw [hmult, hcoeffOrbit]
  have ht := freeHopf_orbit_fixed_branch_translate C x y Q
    (collarCofactorQuadraticDataOperator_symmetric (by norm_num) (by norm_num))
    (collarCofactorQuadraticDataOperator_translate (by norm_num) (by norm_num))
    sourceA sourcef _ _ (v x) (v (freeHopfRealAction C (ofLp y) x))
    (mult (coeff x)) (mult (coeff (freeHopfRealAction C (ofLp y) x)))
    (hf x) (hf _) (hAm x) (hAm _)
    (by simpa only [map_add] using (hv x).2.symm)
    (by simpa only [map_add] using (hv _).2.symm)
    (hlin x _ (hv x).1) (hlin _ _ (hv _).1)
  change (v (freeHopfRealAction C (ofLp y) x)).val.toFun 0 = (v x).val.toFun y
  rw [ht]
  change (v x).val.toFun (0 + y) = (v x).val.toFun y
  rw [zero_add]

/-- The actual cofactor fixed equation gives the original exact native Gram.
Reuse the sole accepted packing and the accepted actual Hopf fixed-branch metric theorem;
neither a new quadratic identity nor a new metric cancellation proof is needed. -/
theorem collarHopf_actual_correction_metric {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F)
    (hfree : ∀ x, LinearIndependent ℝ
      (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) x))
    (coeff : FreeHopfProduct C →
      LittlePeriodicCAlphaFunction a (N * (freeSymmetricColumnCount a + a)) 2 (1 / 2 : ℝ))
    (h : FreeHopfProduct C →
      LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 (1 / 2 : ℝ))
    (hc : ∀ x y, (coeff x).val.toFun y = toLp 2
      (collarHopfAmbientInverseSource C F (Fin.append
        (ofLp (collarHopfAmbientCoordinates C (freeHopfAmbientInclusion C x))) (ofLp y))))
    (hh : ∀ x y, (h x).val.toFun y = toLp 2
      (collarHopfAmbientRawSource C F (Fin.append
        (ofLp (collarHopfAmbientCoordinates C (freeHopfAmbientInclusion C x))) (ofLp y))))
    (mult :
      LittlePeriodicCAlphaFunction a (N * (freeSymmetricColumnCount a + a)) 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a (freeSymmetricColumnCount a + a) 2 (1 / 2 : ℝ) →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
    (hmult : ∀ A v y, (mult A v).val.toFun y =
      hilbertSchmidtCoordinateEvaluation (freeSymmetricColumnCount a + a) N
        (A.val.toFun y) (v.val.toFun y))
    (v : FreeHopfProduct C → LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ))
    (U : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hU : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (hfix : ∀ x, mult (coeff x) ((1 / 2 : ℝ) • h x +
      collarCofactorQuadraticDataOperator (by norm_num) (by norm_num) (v x) (v x)) = v x)
    (hlift : ∀ x y, U (freeHopfOrbitLift C x y) = (v x).val.toFun y) :
    ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i
      ((F ∘ freeHopfAmbientInclusion C) + U) x) = 1 := by
  let P := F ∘ freeHopfAmbientInclusion C
  have hP : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P :=
    (hF.of_le (by simp)).contMDiff.comp (freeHopfAmbientInclusion_contMDiff C)
  let R := fun x ↦ freeGramRightInverse (freeColumnOperator
    (freeFlowColumns (freeHopfProductFlow C) P x))
  let S := fun x ↦ Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i P x) - 1
  have hR (x : FreeHopfProduct C) :
      IsBalancedPairingRightInverse P (freeHopfGenerator C) x (R x) := by
    have he := free_balanced_pairing_adjoint_eq_columnOperator P (freeHopfGenerator C) x
    rw [freeHopf_balanced_pairing_columns C P hP x] at he
    have he' := congrArg (fun T ↦ T.adjoint) he
    rw [ContinuousLinearMap.adjoint_adjoint] at he'
    change (balancedPairingMap P (freeHopfGenerator C) x).comp (R x) = _
    rw [he']
    exact freeGramRightInverse_spec _ ((freeColumnOperator_injective_iff _).mpr (hfree x))
  have hc' (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) :
      (coeff x).val.toFun y = collarCofactorCoefficientCoordinates a N
        (balancedPairingInverseCoordinates a N (R (freeHopfOrbitLift C x y))) := by
    rw [hc, collarHopf_cofactor_balanced_inverse_coordinates]
    apply PiLp.ext
    intro q
    simp only [collarHopfAmbientInverseSource, collarHopfAmbientGramSource,
      collarHopfAmbientSource_native_point]
    rfl
  have hh' (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) :
      (h x).val.toFun y = collarCofactorDataCoordinates a
        ((2 : ℝ) • balancedNormalizedResidualCoordinates 1 (S (freeHopfOrbitLift C x y)) 0) := by
    dsimp only [S, P, freeHopfOrbitLift]
    rw [hh, collarHopf_raw_residual_balanced_coordinates]
    apply PiLp.ext
    intro r
    simp only [collarHopfAmbientRawSource, collarHopfAmbientSourceParameter_append,
      ContinuousLinearEquiv.symm_apply_apply]
    rfl
  intro x
  have hpoint (y : EuclideanSpace ℝ (Fin a)) :
      (v x).val.toFun y = R (freeHopfOrbitLift C x y)
        (balancedNormalizedResidualData 1 (S (freeHopfOrbitLift C x y)) 0) +
      R (freeHopfOrbitLift C x y) ((balancedPairingDataCoordinates a).symm
        ((balancedQuadraticDataOperator (by norm_num) (by norm_num) (v x) (v x)).val.toFun y)) := by
    have he := congrArg (fun w : LittlePeriodicCAlphaFunction a N 2 (1 / 2 : ℝ) ↦
      w.val.toFun y) (hfix x).symm
    rw [hmult, hc'] at he
    have hd : (((1 / 2 : ℝ) • h x +
        collarCofactorQuadraticDataOperator (by norm_num) (by norm_num) (v x) (v x)).val.toFun y) =
        collarCofactorDataCoordinates a
          (balancedNormalizedResidualCoordinates 1 (S (freeHopfOrbitLift C x y)) 0 +
            (balancedQuadraticDataOperator (by norm_num) (by norm_num)
              (v x) (v x)).val.toFun y) := by
      change (((1 / 2 : ℝ) • (h x).val + _).toFun y) = _
      rw [(periodicCAlpha_pointwise_operations a _ 2 (1 / 2 : ℝ)).2.1,
        (periodicCAlpha_pointwise_operations a _ 2 (1 / 2 : ℝ)).2.2]
      change (1 / 2 : ℝ) • (h x).val.toFun y + _ = _
      rw [hh', collarCofactorQuadraticDataOperator_value, map_add, ← map_smul, smul_smul]
      norm_num
    rw [hd, collarCofactorCoefficientCoordinates_evaluation,
      (balanced_pairing_inverse_coordinates_spec a N).1, map_add] at he
    simpa only [balancedNormalizedResidualCoordinates,
      LinearIsometryEquiv.symm_apply_apply, map_add] using he
  have hm := freeHopf_fixed_branch_metric C P U hP hU x
    (by norm_num) (by norm_num) 1 S (fun _ ↦ 0) R R (v x)
    (by simpa only [one_smul] using hlift x)
    (fun y ↦ by
      rw [freeHopf_geometry_eq_gram]
      simp only [one_pow, one_smul, smul_zero, add_zero, S]
      abel)
    (fun y ↦ hR _) (fun y ↦ by simp only [one_smul]) hpoint
  have hm0 := hm 0
  rwa [freeHopfOrbitLift_zero, freeHopf_geometry_eq_gram] at hm0

/-- The original smooth free identity-Gram map has a global native analytic exact free seed.

Proof: fix the original uniform free margin, the actual Gaussian extension/multiplier
constant, and the sole accepted Q bound before choosing any approximation. A finite minimum
of the actual69 forcing threshold, strict-small threshold and original free-error threshold
then fixes one forcing tolerance. Choose the literal Gaussian once and use its accepted
analyticity. The actual69/global-correction assembly above yields the native analytic U and
derives its true orbit lift by accepted uniqueness/covariance. Accepted packing and actual
fixed-branch metric cancellation give exact Gram. Ambient C5 error and the original little
norm bound pay half of the fixed H0 column margin each, so freeness persists globally.
Source: Proposition prop:collar, main.tex522–534. No desired seed or gluing is assumed. -/
theorem collarHopf_global_analytic_seed {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (H0 : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hH0 : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H0)
    (hfree : ∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow C) H0 x))
    (hmetric : ∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i H0 x) = 1) :
    ∃ H : FreeHopfProduct C → EuclideanSpace ℝ (Fin N),
      ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω H ∧
      (∀ x, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i H x) = 1) ∧
      ∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow C) H x) := by
  obtain ⟨η, μ, hη, hμ, hpersist⟩ := collarHopf_native_free_persistence C H0 hH0 hfree
  obtain ⟨L, hL, hjet⟩ := collarHopf_ambient_c5_column_jets (N := N) C
  obtain ⟨f0, K, hf0, hcompact, hsame, hK, hthreshold, hchoice⟩ :=
    collarHopf_gaussian_quantitative_data C H0 hH0 hfree hmetric
  obtain ⟨B, hB, hquad⟩ := collarCofactorQuadraticDataOperator_bound
    (a := a) (N := N) (α := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨ρ, ζ, hρ, hζ, _, _, hstrict⟩ := hthreshold B hB.le
  let J := 1 + (a : ℝ) + (a : ℝ) ^ 2
  have hJ : 0 < J := by dsimp only [J]; positivity
  let δ₀ := (1 / (4 * (K * collarHopfCofactorQNorm a N + 1))) / (K + 1)
  have hQN : 0 ≤ collarHopfCofactorQNorm a N :=
    Real.sInf_nonneg (fun c hc ↦ hc.1)
  have hδ₀ : 0 < δ₀ := by dsimp only [δ₀]; positivity
  let δ := min (ζ / 2) (min δ₀ (η / (4 * J * (K + 1))))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδζ : δ < ζ := (min_le_left _ _).trans_lt (by linarith)
  have hδ₀le : δ ≤ δ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hδmargin : δ ≤ η / (4 * J * (K + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hδstrict : 4 * K * B * (K + 1) * δ < (1 / 2 : ℝ) := hstrict δ hδ.le hδζ
  let τ := η / (2 * (L + 1))
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  obtain ⟨ε, F, hε, hεcap, hliteral, hF, hFjets, hFfree, hFgram, hdata⟩ :=
    hchoice δ hδ τ hτ 1 zero_lt_one
  have hFω := collarHopf_literal_gaussian_contDiff C f0 F hf0.continuous hcompact ε hliteral
  choose coeff h hcoeff hncoeff hAn hforcing hnH using hdata
  have hc (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) :
      (coeff x).val.toFun y = toLp 2 (collarHopfAmbientInverseSource C F
        (Fin.append (ofLp (collarHopfAmbientCoordinates C (freeHopfAmbientInclusion C x)))
          (ofLp y))) := by
    apply PiLp.ext
    intro q
    rw [hcoeff]
    simp only [collarHopfAmbientInverseSource, collarHopfAmbientGramSource,
      collarHopfAmbientSourceParameter_append, ContinuousLinearEquiv.symm_apply_apply]
  have hh (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) :
      (h x).val.toFun y = toLp 2 (collarHopfAmbientRawSource C F
        (Fin.append (ofLp (collarHopfAmbientCoordinates C (freeHopfAmbientInclusion C x)))
          (ofLp y))) := by
    apply PiLp.ext
    intro r
    rw [hforcing]
    simp only [collarHopfAmbientRawSource, collarHopfAmbientSourceParameter_append,
      ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hbase (x : FreeHopfProduct C) (y : Fin a → ℝ) :
      let T := collarHopfAmbientGramSource C F (Fin.append
        (ofLp (collarHopfAmbientCoordinates C (freeHopfAmbientInclusion C x))) y)
      (T * T.transpose).det ≠ 0 := by
    convert hFgram x y using 1
    simp only [collarHopfAmbientGramSource, collarHopfAmbientSourceParameter_append,
      ContinuousLinearEquiv.symm_apply_apply]
  obtain ⟨mult, v, U, hmult, hUω, hUdata⟩ := collarHopf_actual_global_analytic_correction
    C F hFω coeff h K B δ hK.le hB.le hδ hbase hc hh hAn hnH hδ₀le hδstrict hquad
  have hU := hUω.of_le (by simp : (∞ : ℕ∞ω) ≤ ω)
  have hPω := hFω.contMDiff.comp (collarHopfAmbientInclusion_omega C)
  have hP := hPω.of_le (by simp : (∞ : ℕ∞ω) ≤ ω)
  let P := F ∘ freeHopfAmbientInclusion C
  have hmetricH := collarHopf_actual_correction_metric C F hFω hFfree coeff h hc hh
    mult hmult v U hU (fun x ↦ (hUdata x).2.1) (fun x ↦ (hUdata x).2.2)
  refine ⟨P + U, hPω.add hUω, hmetricH, ?_⟩
  suffices hclose : ∀ x k,
      ‖freeFlowColumns (freeHopfProductFlow C) (P + U) x k -
        freeFlowColumns (freeHopfProductFlow C) H0 x k‖ ≤ η by
    intro x
    exact (hpersist (P + U) hclose x).1
  intro x k
  let R := (F - f0) ∘ freeHopfAmbientInclusion C
  have hR : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ R :=
    (hF.sub hf0).contMDiff.comp (freeHopfAmbientInclusion_contMDiff C)
  have hRfun : R = P - H0 := by
    funext z
    simp only [R, P, Function.comp_apply, Pi.sub_apply, hsame]
  have hRbound : ‖freeFlowColumns (freeHopfProductFlow C) R x k‖ ≤ L * τ := by
    have hj := hjet (F - f0) (hF.sub hf0) τ hτ.le
      (fun z i hi ↦ hFjets _ i hi) x 0 0 (by norm_num) k
    simpa only [norm_iteratedFDeriv_zero, freeHopfOrbitLift_zero] using hj
  have hUnorm : ‖v x‖ ≤ 2 * (K + 1) * δ :=
    (hUdata x).1.trans (mul_le_mul_of_nonneg_left (hnH x).le (by positivity))
  have hUjet := freeHopf_verticalC2Size_le_little_norm C U hU x (v x) (hUdata x).2.2 0
  rw [freeHopfOrbitLift_zero] at hUjet
  have hUcol : ‖freeFlowColumns (freeHopfProductFlow C) U x k‖ ≤ J * ‖v x‖ := by
    rw [← freeHopf_balanced_pairing_columns C U hU x]
    exact free_pairing_column_norm_le (freeHopfGenerator C) U x hUjet k
  have hFpay : L * τ ≤ η / 2 := by
    have ht : τ * (2 * (L + 1)) = η := by
      dsimp only [τ]
      exact div_mul_cancel₀ _ (ne_of_gt (by positivity))
    nlinarith
  have hUpay : J * ‖v x‖ ≤ η / 2 := by
    have hd := (le_div_iff₀ (by positivity : 0 < 4 * J * (K + 1))).mp hδmargin
    nlinarith [mul_le_mul_of_nonneg_left hUnorm hJ.le]
  have hadd : freeFlowColumns (freeHopfProductFlow C) (P + U) x k =
      freeFlowColumns (freeHopfProductFlow C) P x k +
        freeFlowColumns (freeHopfProductFlow C) U x k := by
    have ha := free_pairing_columns_add P U hP hU (freeHopfGeneratorSection C) x
    change balancedPairingColumns (P + U) (freeHopfGenerator C) x =
      balancedPairingColumns P (freeHopfGenerator C) x +
        balancedPairingColumns U (freeHopfGenerator C) x at ha
    rw [freeHopf_balanced_pairing_columns C _ (hP.add hU) x,
      freeHopf_balanced_pairing_columns C P hP x,
      freeHopf_balanced_pairing_columns C U hU x] at ha
    exact congrFun ha k
  rw [hadd]
  calc
    ‖freeFlowColumns (freeHopfProductFlow C) P x k +
        freeFlowColumns (freeHopfProductFlow C) U x k -
        freeFlowColumns (freeHopfProductFlow C) H0 x k‖ =
        ‖freeFlowColumns (freeHopfProductFlow C) R x k +
          freeFlowColumns (freeHopfProductFlow C) U x k‖ := by
      rw [hRfun, freeHopf_columns_sub C P H0 hP hH0]
      congr 1
      abel
    _ ≤ L * τ + J * ‖v x‖ := (norm_add_le _ _).trans (add_le_add hRbound hUcol)
    _ ≤ η := by linarith

end GlobalEmbedding.Paper
