import GlobalEmbedding.Paper.CollarHopfLocalCKJets
import GlobalEmbedding.Paper.CollarCKCompactGermGluing

/-!
# The actual full-chart square-inverse collar Cauchy problem

Source: main.tex539–549, equation5.3. Reuse the native analytic sphere-product chart and all
transverse coordinates, actual Hopf flows, the accepted canonical normal, true square pairing,
native inverse analyticity and the accepted full second-order Cauchy theorem.
-/

noncomputable section
open scoped Topology Manifold ContDiff
open Filter
namespace GlobalEmbedding.Paper

section ChartJet
variable {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)] (x₀ : FreeHopfProduct C)
local notation "d" => Module.finrank ℝ (FreeHopfModelSpace C)
local notation "N" => freeSymmetricColumnCount a + a + 1
local notation "J" => CKForcingInput d N
local notation "L" => EuclideanSpace ℝ (Fin N)
local notation "V" => CKVal N

/-- Actual reconstructed maps are native jointly analytic wherever the genuine source chart
is valid and the SAME coordinate map is analytic. Source: main.tex549. -/
theorem collarHopfReconstruct_omega (u : CKJoint d → V) (z : ℝ × FreeHopfProduct C)
    (hz : z.2 ∈ (collarHopfFullChart C x₀).source)
    (hu : AnalyticAt ℝ u (z.1, collarHopfFullChart C x₀ z.2)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, L) ω
      (collarHopfReconstruct C x₀ u) z := by
  have hc : ContMDiffAt (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, CKJoint d) ω
      (fun p : ℝ × FreeHopfProduct C ↦ (p.1, collarHopfFullChart C x₀ p.2)) z :=
    contMDiffAt_fst.prodMk_space
      ((collarHopfFullChart_omega C x₀ z.2 hz).comp z contMDiffAt_snd)
  let e : V ≃L[ℝ] L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).symm
  exact (e.toContinuousLinearMap.contDiff.contMDiff.contMDiffAt).comp z
    (hu.contDiffAt.contMDiffAt.comp z hc)

omit [∀ i, Fact (0 < C i)] in
/-- The entire original second-order solution jet is analytic for an actual analytic map.
Source: main.tex5.3. Only native first and second derivatives in the existing CK directions
occur. -/
theorem collarHopfSolutionJet_analyticAt (u : CKJoint d → V) (z : CKJoint d)
    (hu : AnalyticAt ℝ u z) : AnalyticAt ℝ (collarHopfSolutionJet C u) z := by
  have hd (v : CKJoint d) : AnalyticAt ℝ (fun y ↦ fderiv ℝ u y v) z :=
    ((ContinuousLinearMap.apply ℝ V v).analyticAt _).comp hu.fderiv
  have hdd (v w : CKJoint d) :
      AnalyticAt ℝ (fun y ↦ fderiv ℝ (fun p ↦ fderiv ℝ u p v) y w) z :=
    ((ContinuousLinearMap.apply ℝ V w).analyticAt _).comp (hd v).fderiv
  have hs : AnalyticAt ℝ (ckSpatialDerivative u) z :=
    AnalyticAt.pi (fun i ↦ hd (ckSpaceDirection i))
  have hss : AnalyticAt ℝ (ckSecondSpatialDerivative u) z :=
    AnalyticAt.pi (fun i ↦ AnalyticAt.pi (fun j ↦ hdd (ckSpaceDirection j) (ckSpaceDirection i)))
  have hm : AnalyticAt ℝ (ckMixedDerivative u) z :=
    AnalyticAt.pi (fun i ↦ hdd ckTimeDirection (ckSpaceDirection i))
  exact analyticAt_snd.prod
    (analyticAt_fst.prod (hu.prod (hs.prod (hss.prod ((hd ckTimeDirection).prod hm)))))

omit [∀ i, Fact (0 < C i)] in
/-- At time zero the SAME full actual solution jet is the original actual Cauchy jet.
Source: main.tex5.3. Initial values and initial normal derivatives hold on an open spatial
ball, so native germ differentiation identifies all initial spatial and mixed derivatives. -/
theorem collarHopfSolutionJet_initial (u : CKJoint d → V) (h₀ h₁ : CKX d → V)
    (q : CKX d) (ε : ℝ) (hε : 0 < ε)
    (hu : AnalyticOnNhd ℝ u (Metric.ball ((0 : ℝ), q) ε))
    (hinit : ∀ y ∈ Metric.ball q ε, u (0, y) = h₀ y ∧ ckTimeDerivative u (0, y) = h₁ y) :
    collarHopfSolutionJet C u (0, q) = ckForcingInitialPoint h₀ h₁ q := by
  have hz : ((0 : ℝ), q) ∈ Metric.ball ((0 : ℝ), q) ε := Metric.mem_ball_self hε
  have ha := hu (0, q) hz
  have h₀g : (fun y ↦ u (0, y)) =ᶠ[𝓝 q] h₀ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)] with y hy
    exact (hinit y hy).1
  have h₁g : (fun y ↦ ckTimeDerivative u (0, y)) =ᶠ[𝓝 q] h₁ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)] with y hy
    exact (hinit y hy).2
  have hs : ckSpatialDerivative u (0, q) = ckDataSpatialDerivative h₀ q := by
    rw [← collarHopf_spatial_slice u 0 q ha.differentiableAt]
    exact congrArg (fun T : CKX d →L[ℝ] V ↦ fun i ↦ T (EuclideanSpace.single i 1))
      h₀g.fderiv_eq
  have hss : ckSecondSpatialDerivative u (0, q) = ckDataSpatialHessian h₀ q := by
    rw [← collarHopf_hessian_slice u 0 q ha]
    exact collarHopf_dataHessian_germ h₀g
  have ht : AnalyticAt ℝ (ckTimeDerivative u) (0, q) :=
    ((ContinuousLinearMap.apply ℝ V ckTimeDirection).analyticAt _).comp ha.fderiv
  have hm : ckMixedDerivative u (0, q) = ckDataSpatialDerivative h₁ q := by
    change ckSpatialDerivative (ckTimeDerivative u) (0, q) = _
    rw [← collarHopf_spatial_slice (ckTimeDerivative u) 0 q ht.differentiableAt]
    exact congrArg (fun T : CKX d →L[ℝ] V ↦ fun i ↦ T (EuclideanSpace.single i 1))
      h₁g.fderiv_eq
  simp only [collarHopfSolutionJet, ckForcingInitialPoint, (hinit q (Metric.mem_ball_self hε)).1,
    (hinit q (Metric.mem_ball_self hε)).2, hs, hss, hm]

/-- Genuine native local collar solutions from the SAME original analytic Cauchy data.
Source: main.tex539–549. Invoke the actual full-coordinate CK solver, then shrink using
true continuity and open neighborhoods of the native chart and invertible operators.
The spatial coordinate equivalence is never treated as an isometry. -/
theorem collarHopfLocalCK_native (H ν : FreeHopfProduct C → L)
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, L) ω H)
    (hν : ContMDiff (freeHopfModel C) 𝓘(ℝ, L) ω ν)
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun _ : Unit ↦ ν x₀) (freeFlowColumns (freeHopfProductFlow C) H x₀))) :
    ∃ U : Set (FreeHopfProduct C), IsOpen U ∧ x₀ ∈ U ∧
      ∃ r > 0, ∃ G : ℝ × FreeHopfProduct C → L,
        ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, L) ω G
          (Set.Ioo (-r) r ×ˢ U) ∧
        (∀ x ∈ U, G (0, x) = H x ∧ hopfCollarRDeriv G 0 x = ν x) ∧
        ∀ t x, (t, x) ∈ Set.Ioo (-r) r ×ˢ U →
          (hopfCollarSquarePairing C G t x).IsInvertible ∧
            deriv (fun s ↦ hopfCollarRDeriv G s x) t =
              (hopfCollarSquarePairing C G t x).inverse (hopfCollarSquareForcing C G t x) := by
  let ψ := collarHopfFullChart C x₀
  have hx₀ : x₀ ∈ ψ.source := ⟨mem_chart_source _ x₀, Set.mem_univ _⟩
  let q := ψ x₀
  have hq : q ∈ ψ.target := ψ.map_source hx₀
  have hHq := collarHopfChartData_analyticAt C x₀ H hH q hq
  have hνq := collarHopfChartData_analyticAt C x₀ ν hν q hq
  have hLIq : LinearIndependent ℝ
      (Sum.elim (fun _ : Unit ↦ ν (ψ.symm q))
        (freeFlowColumns (freeHopfProductFlow C) H (ψ.symm q))) := by
    simpa only [q, ψ.left_inv hx₀] using hLI
  obtain ⟨ε, hε, u, hsol, _⟩ := collarHopfLocalCK_coordinates C x₀ H ν q hq hHq hνq hLIq
  have ha := hsol.1 (0, q) (Metric.mem_ball_self hε)
  have hji := collarHopfSolutionJet_initial C u _ _ q ε hε hsol.1 hsol.2.2
  let T := fun z : CKJoint d ↦
    (freeColumnOperator (collarHopfJetColumns C x₀ (collarHopfSolutionJet C u z))).adjoint
  have hT₀ : (T (0, q)).IsInvertible := by
    dsimp only [T]
    rw [hji, collarHopfJetColumns_initial C x₀ H ν q hq hHq]
    exact collarHopfSquarePairing_invertible _ hLIq
  have hTc : ContinuousAt T (0, q) :=
    ((collarHopfJetPairing_analyticAt C x₀ (collarHopfSolutionJet C u (0, q)) hq).comp
      (collarHopfSolutionJet_analyticAt C u (0, q) ha)).continuousAt
  let S : Set (CKJoint d) := {z | z ∈ Metric.ball ((0 : ℝ), q) ε ∧
    z.2 ∈ ψ.target ∧ (T z).IsInvertible}
  have hS : S ∈ 𝓝 ((0 : ℝ), q) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε),
      continuous_snd.continuousAt.eventually (ψ.open_target.mem_nhds hq),
      hTc.eventually hT₀.eventually_nhds] with z hz hzt hzi
    exact ⟨hz, hzt, hzi⟩
  let θ := fun z : ℝ × FreeHopfProduct C ↦ (z.1, ψ z.2)
  have hθ : ContinuousAt θ (0, x₀) :=
    (contMDiffAt_fst.prodMk_space
      ((collarHopfFullChart_omega C x₀ x₀ hx₀).comp (0, x₀) contMDiffAt_snd)).continuousAt
  have hW : {z : ℝ × FreeHopfProduct C | z.2 ∈ ψ.source ∧ θ z ∈ S} ∈ 𝓝 (0, x₀) := by
    filter_upwards [continuous_snd.continuousAt.eventually (ψ.open_source.mem_nhds hx₀),
      hθ.eventually hS] with z hzs hzS
    exact ⟨hzs, hzS⟩
  obtain ⟨O, U, hO, hO₀, hU, hxU, hsub⟩ := mem_nhds_prod_iff'.mp hW
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hO₀)
  have hpoint (t : ℝ) (x : FreeHopfProduct C) (ht : t ∈ Set.Ioo (-r) r) (hx : x ∈ U) :
      x ∈ ψ.source ∧ (t, ψ x) ∈ S := by
    exact hsub (a := (t, x))
      ⟨hrO (by simpa only [Real.ball_zero_eq_Ioo] using ht), hx⟩
  refine ⟨U, hU, hxU, r, hr, collarHopfReconstruct C x₀ u, ?_, ?_, ?_⟩
  · intro z hz
    have hh := hpoint z.1 z.2 hz.1 hz.2
    exact (collarHopfReconstruct_omega C x₀ u z hh.1 (hsol.1 _ hh.2.1)).contMDiffWithinAt
  · intro x hx
    have hh := hpoint 0 x ⟨neg_lt_zero.mpr hr, hr⟩ hx
    have hb : ψ x ∈ Metric.ball q ε := by
      simpa only [Metric.mem_ball, Prod.dist_eq, dist_self,
        max_eq_right (dist_nonneg)] using hh.2.1
    have hi := hsol.2.2 (ψ x) hb
    simp only [ψ, (collarHopfFullChart C x₀).left_inv hh.1] at hi
    constructor
    · exact congrArg (WithLp.toLp 2) hi.1
    · rw [collarHopfReconstruct_rDeriv C x₀ u 0 x (hsol.1 _ hh.2.1).differentiableAt]
      exact congrArg (WithLp.toLp 2) hi.2
  · intro t x hx
    have hh := hpoint t x hx.1 hx.2
    have hu := hsol.1 _ hh.2.1
    have hpair := collarHopfReconstruct_pairing C x₀ u t (ψ x) hh.2.2.1 hu
    have hpde := (collarHopfReconstruct_inversePDE_iff C x₀ u t (ψ x) hh.2.2.1 hu).mpr
      (hsol.2.1 t (ψ x) hh.2.1)
    simp only [ψ, (collarHopfFullChart C x₀).left_inv hh.1] at hpair hpde
    refine ⟨?_, hpde⟩
    rw [hpair]
    exact hh.2.2.2

/-- The genuine full-coordinate representative of an arbitrary native collar function.
Source: main.tex549. Use the SAME full native chart and native target coordinates. -/
def collarHopfChartFunction (G : ℝ × FreeHopfProduct C → L) : CKJoint d → V :=
  fun z ↦ WithLp.ofLp (G (z.1, (collarHopfFullChart C x₀).symm z.2))

/-- Native joint analyticity gives actual analyticity in the FULL common source chart.
Source: main.tex549. The inverse native chart is used only on its genuine target. -/
theorem collarHopfChartFunction_analyticAt (G : ℝ × FreeHopfProduct C → L)
    (z : CKJoint d) (hz : z.2 ∈ (collarHopfFullChart C x₀).target)
    (hG : ContMDiffAt (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, L) ω G
      (z.1, (collarHopfFullChart C x₀).symm z.2)) :
    AnalyticAt ℝ (collarHopfChartFunction C x₀ G) z := by
  have hi : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, CKX d))
      (𝓘(ℝ, ℝ).prod (freeHopfModel C)) ω
      (fun p : CKJoint d ↦ (p.1, (collarHopfFullChart C x₀).symm p.2)) z :=
    contMDiffAt_fst.prodMk
      ((collarHopfFullChart_symm_omega C x₀ z.2 hz).comp z contMDiffAt_snd)
  have ho := hG.comp z hi
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at ho
  let e : L ≃L[ℝ] V := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)
  exact (e.toContinuousLinearMap.analyticAt _).comp ho.contDiffAt.analyticAt

/-- Reconstructing the common-chart representative returns the SAME arbitrary native map
as a JOINT germ. Source: main.tex549. Actual source openness and chart inversion suffice. -/
theorem collarHopfReconstruct_chartFunction_germ (G : ℝ × FreeHopfProduct C → L)
    (z : ℝ × FreeHopfProduct C) (hz : z.2 ∈ (collarHopfFullChart C x₀).source) :
    collarHopfReconstruct C x₀ (collarHopfChartFunction C x₀ G) =ᶠ[𝓝 z] G := by
  filter_upwards [continuous_snd.continuousAt.eventually
    ((collarHopfFullChart C x₀).open_source.mem_nhds hz)] with p hp
  simp only [collarHopfReconstruct, collarHopfChartFunction,
    (collarHopfFullChart C x₀).left_inv hp, WithLp.toLp_ofLp, Prod.mk.eta]

/-- EVERY genuine native analytic inverse-PDE competitor becomes an actual solution of the
SAME full-chart CK equation on a positive ball. Source: main.tex549. Native data/PDE hold on
honest neighborhoods; chart inversion, jet/PDE iff and accepted intrinsic germ transfer prove
all CK compatibility internally. This is the missing native-to-coordinate uniqueness bridge. -/
theorem collarHopf_native_CK_competitor (H ν : FreeHopfProduct C → L)
    (G : ℝ × FreeHopfProduct C → L)
    (hG : ∀ᶠ z : ℝ × FreeHopfProduct C in 𝓝 (0, x₀),
      ContMDiffAt (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, L) ω G z ∧
        (hopfCollarSquarePairing C G z.1 z.2).IsInvertible ∧
          deriv (fun t ↦ hopfCollarRDeriv G t z.2) z.1 =
            (hopfCollarSquarePairing C G z.1 z.2).inverse
              (hopfCollarSquareForcing C G z.1 z.2))
    (hinit : ∀ᶠ x in 𝓝 x₀, G (0, x) = H x ∧ hopfCollarRDeriv G 0 x = ν x) :
    ∃ η > 0, CKOriginalSolution (collarHopfLocalRHS C x₀)
      (fun y ↦ WithLp.ofLp (H ((collarHopfFullChart C x₀).symm y)))
      (fun y ↦ WithLp.ofLp (ν ((collarHopfFullChart C x₀).symm y)))
      (collarHopfFullChart C x₀ x₀) η (collarHopfChartFunction C x₀ G) := by
  let ψ := collarHopfFullChart C x₀
  let q := ψ x₀
  have hx₀ : x₀ ∈ ψ.source := ⟨mem_chart_source _ x₀, Set.mem_univ _⟩
  have hq : q ∈ ψ.target := ψ.map_source hx₀
  let β := fun z : CKJoint d ↦ (z.1, ψ.symm z.2)
  have hs : ContinuousAt ψ.symm q :=
    (collarHopfFullChart_symm_omega C x₀ q hq).continuousAt
  have hsp : ContinuousAt (fun z : CKJoint d ↦ ψ.symm z.2) (0, q) :=
    hs.comp (f := Prod.snd) continuous_snd.continuousAt
  have hβ : Tendsto β (𝓝 ((0 : ℝ), q)) (𝓝 ((0 : ℝ), x₀)) := by
    have hc := continuous_fst.continuousAt.prodMk hsp
    simpa only [q, ψ.left_inv hx₀] using hc.tendsto
  have hβs : Tendsto (fun z : CKJoint d ↦ ψ.symm z.2)
      (𝓝 ((0 : ℝ), q)) (𝓝 x₀) := by
    have hc := hsp
    simpa only [q, ψ.left_inv hx₀] using hc.tendsto
  have hE : {z : CKJoint d | z.2 ∈ ψ.target ∧
      (ContMDiffAt (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, L) ω G (β z) ∧
        (hopfCollarSquarePairing C G z.1 (ψ.symm z.2)).IsInvertible ∧
          deriv (fun t ↦ hopfCollarRDeriv G t (ψ.symm z.2)) z.1 =
            (hopfCollarSquarePairing C G z.1 (ψ.symm z.2)).inverse
              (hopfCollarSquareForcing C G z.1 (ψ.symm z.2))) ∧
      (G (0, ψ.symm z.2) = H (ψ.symm z.2) ∧
        hopfCollarRDeriv G 0 (ψ.symm z.2) = ν (ψ.symm z.2))} ∈ 𝓝 ((0 : ℝ), q) := by
    filter_upwards [continuous_snd.continuousAt.eventually (ψ.open_target.mem_nhds hq),
      hβ.eventually hG, hβs.eventually hinit] with z hzt hGz hiz
    exact ⟨hzt, hGz, hiz⟩
  obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp hE
  refine ⟨η, hη, ?_, ?_, ?_⟩
  · intro z hz
    have hh := hsub hz
    exact collarHopfChartFunction_analyticAt C x₀ G z hh.1 hh.2.1.1
  · intro r y hz
    have hh := hsub hz
    have ha := collarHopfChartFunction_analyticAt C x₀ G (r, y) hh.1 hh.2.1.1
    have heq := collarHopfReconstruct_chartFunction_germ C x₀ G (r, ψ.symm y)
      (ψ.map_target hh.1)
    have hp := collarCK_inversePDE_of_germ C heq hh.2.1.2.1 hh.2.1.2.2
    exact (collarHopfReconstruct_inversePDE_iff C x₀ _ r y hh.1 ha).mp hp.2
  · intro y hy
    have hz : ((0 : ℝ), y) ∈ Metric.ball ((0 : ℝ), q) η := by
      simpa only [Metric.mem_ball, Prod.dist_eq, dist_self,
        max_eq_right (dist_nonneg)] using hy
    have hh := hsub hz
    have ha := collarHopfChartFunction_analyticAt C x₀ G (0, y) hh.1 hh.2.1.1
    have heq := collarHopfReconstruct_chartFunction_germ C x₀ G (0, ψ.symm y)
      (ψ.map_target hh.1)
    have hr := (collarCK_rDeriv_germ C heq).self_of_nhds
    have hd : DifferentiableAt ℝ (collarHopfChartFunction C x₀ G) (0, ψ (ψ.symm y)) := by
      rw [ψ.right_inv hh.1]
      exact ha.differentiableAt
    have hn := collarHopfReconstruct_rDeriv C x₀ (collarHopfChartFunction C x₀ G)
      0 (ψ.symm y) hd
    simp only [ψ, (collarHopfFullChart C x₀).right_inv hh.1] at hn
    refine ⟨congrArg WithLp.ofLp hh.2.2.1, ?_⟩
    exact congrArg WithLp.ofLp (hn.symm.trans (hr.trans hh.2.2.2))

/-- ANY two genuine native analytic solutions with the same original Cauchy data have equal
JOINT native germs. Source: main.tex549. At THIS sourcepoint, choose ONE common FULL native
chart, turn both actual maps into actual competitors of the SAME CK equation, apply EVERY
competitor uniqueness, then pull back the resulting joint ball germ. No uniform radius over
any noncompact overlap is assumed and equality at time zero is never used as germ equality. -/
theorem collarHopf_native_germ_unique (H ν : FreeHopfProduct C → L)
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, L) ω H)
    (hν : ContMDiff (freeHopfModel C) 𝓘(ℝ, L) ω ν)
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun _ : Unit ↦ ν x₀) (freeFlowColumns (freeHopfProductFlow C) H x₀)))
    (G₁ G₂ : ℝ × FreeHopfProduct C → L)
    (hG₁ : ∀ᶠ z : ℝ × FreeHopfProduct C in 𝓝 (0, x₀),
      ContMDiffAt (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, L) ω G₁ z ∧
        (hopfCollarSquarePairing C G₁ z.1 z.2).IsInvertible ∧
          deriv (fun t ↦ hopfCollarRDeriv G₁ t z.2) z.1 =
            (hopfCollarSquarePairing C G₁ z.1 z.2).inverse
              (hopfCollarSquareForcing C G₁ z.1 z.2))
    (hG₂ : ∀ᶠ z : ℝ × FreeHopfProduct C in 𝓝 (0, x₀),
      ContMDiffAt (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, L) ω G₂ z ∧
        (hopfCollarSquarePairing C G₂ z.1 z.2).IsInvertible ∧
          deriv (fun t ↦ hopfCollarRDeriv G₂ t z.2) z.1 =
            (hopfCollarSquarePairing C G₂ z.1 z.2).inverse
              (hopfCollarSquareForcing C G₂ z.1 z.2))
    (hi₁ : ∀ᶠ x in 𝓝 x₀, G₁ (0, x) = H x ∧ hopfCollarRDeriv G₁ 0 x = ν x)
    (hi₂ : ∀ᶠ x in 𝓝 x₀, G₂ (0, x) = H x ∧ hopfCollarRDeriv G₂ 0 x = ν x) :
    G₁ =ᶠ[𝓝 ((0 : ℝ), x₀)] G₂ := by
  let ψ := collarHopfFullChart C x₀
  let q := ψ x₀
  have hx₀ : x₀ ∈ ψ.source := ⟨mem_chart_source _ x₀, Set.mem_univ _⟩
  have hq : q ∈ ψ.target := ψ.map_source hx₀
  have hLIq : LinearIndependent ℝ
      (Sum.elim (fun _ : Unit ↦ ν (ψ.symm q))
        (freeFlowColumns (freeHopfProductFlow C) H (ψ.symm q))) := by
    simpa only [q, ψ.left_inv hx₀] using hLI
  obtain ⟨ε, _, u, _, huniq⟩ := collarHopfLocalCK_coordinates C x₀ H ν q hq
    (collarHopfChartData_analyticAt C x₀ H hH q hq)
    (collarHopfChartData_analyticAt C x₀ ν hν q hq) hLIq
  obtain ⟨η₁, hη₁, hc₁⟩ := collarHopf_native_CK_competitor C x₀ H ν G₁ hG₁ hi₁
  obtain ⟨η₂, hη₂, hc₂⟩ := collarHopf_native_CK_competitor C x₀ H ν G₂ hG₂ hi₂
  obtain ⟨δ₁, hδ₁, _, _, he₁⟩ := huniq _ η₁ hη₁ hc₁
  obtain ⟨δ₂, hδ₂, _, _, he₂⟩ := huniq _ η₂ hη₂ hc₂
  have hg₁ : u =ᶠ[𝓝 ((0 : ℝ), q)] collarHopfChartFunction C x₀ G₁ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ₁)] with z hz
    exact he₁ z.1 z.2 hz
  have hg₂ : u =ᶠ[𝓝 ((0 : ℝ), q)] collarHopfChartFunction C x₀ G₂ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ₂)] with z hz
    exact he₂ z.1 z.2 hz
  have hθ : Tendsto (fun z : ℝ × FreeHopfProduct C ↦ (z.1, ψ z.2))
      (𝓝 ((0 : ℝ), x₀)) (𝓝 ((0 : ℝ), q)) :=
    (contMDiffAt_fst.prodMk_space
      ((collarHopfFullChart_omega C x₀ x₀ hx₀).comp (0, x₀) contMDiffAt_snd)).continuousAt
  filter_upwards [(hg₁.symm.trans hg₂).comp_tendsto hθ,
    continuous_snd.continuousAt.eventually (ψ.open_source.mem_nhds hx₀)] with z hz hzs
  have he := congrArg (WithLp.toLp 2) hz
  simpa only [Function.comp_apply, collarHopfChartFunction, ψ,
    (collarHopfFullChart C x₀).left_inv hzs, WithLp.toLp_ofLp, Prod.mk.eta] using he

/-- Actual local tubes with the SAME H/nu agree as JOINT native germs at EVERY overlap point.
Source: main.tex549. The common full chart is chosen at the overlap point x0, independently
of the two construction charts. No uniform overlap radius or global chart identity is assumed. -/
theorem collarHopf_native_tubes_germ_unique (H ν : FreeHopfProduct C → L)
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, L) ω H)
    (hν : ContMDiff (freeHopfModel C) 𝓘(ℝ, L) ω ν)
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun _ : Unit ↦ ν x₀) (freeFlowColumns (freeHopfProductFlow C) H x₀)))
    (U₁ U₂ : Set (FreeHopfProduct C)) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hx₁ : x₀ ∈ U₁) (hx₂ : x₀ ∈ U₂) (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (G₁ G₂ : ℝ × FreeHopfProduct C → L)
    (hG₁ : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, L) ω G₁
      (Set.Ioo (-r₁) r₁ ×ˢ U₁))
    (hG₂ : ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, L) ω G₂
      (Set.Ioo (-r₂) r₂ ×ˢ U₂))
    (hi₁ : ∀ x ∈ U₁, G₁ (0, x) = H x ∧ hopfCollarRDeriv G₁ 0 x = ν x)
    (hi₂ : ∀ x ∈ U₂, G₂ (0, x) = H x ∧ hopfCollarRDeriv G₂ 0 x = ν x)
    (hP₁ : ∀ t x, (t, x) ∈ Set.Ioo (-r₁) r₁ ×ˢ U₁ →
      (hopfCollarSquarePairing C G₁ t x).IsInvertible ∧
        deriv (fun s ↦ hopfCollarRDeriv G₁ s x) t =
          (hopfCollarSquarePairing C G₁ t x).inverse (hopfCollarSquareForcing C G₁ t x))
    (hP₂ : ∀ t x, (t, x) ∈ Set.Ioo (-r₂) r₂ ×ˢ U₂ →
      (hopfCollarSquarePairing C G₂ t x).IsInvertible ∧
        deriv (fun s ↦ hopfCollarRDeriv G₂ s x) t =
          (hopfCollarSquarePairing C G₂ t x).inverse (hopfCollarSquareForcing C G₂ t x)) :
    G₁ =ᶠ[𝓝 ((0 : ℝ), x₀)] G₂ := by
  apply collarHopf_native_germ_unique C x₀ H ν hH hν hLI G₁ G₂
  · have hz₀ : ((0 : ℝ), x₀) ∈ Set.Ioo (-r₁) r₁ ×ˢ U₁ :=
      ⟨⟨neg_lt_zero.mpr hr₁, hr₁⟩, hx₁⟩
    filter_upwards [(isOpen_Ioo.prod hU₁).mem_nhds hz₀] with z hz
    exact ⟨hG₁.contMDiffAt ((isOpen_Ioo.prod hU₁).mem_nhds hz), hP₁ z.1 z.2 hz⟩
  · have hz₀ : ((0 : ℝ), x₀) ∈ Set.Ioo (-r₂) r₂ ×ˢ U₂ :=
      ⟨⟨neg_lt_zero.mpr hr₂, hr₂⟩, hx₂⟩
    filter_upwards [(isOpen_Ioo.prod hU₂).mem_nhds hz₀] with z hz
    exact ⟨hG₂.contMDiffAt ((isOpen_Ioo.prod hU₂).mem_nhds hz), hP₂ z.1 z.2 hz⟩
  · filter_upwards [hU₁.mem_nhds hx₁] with x hx
    exact hi₁ x hx
  · filter_upwards [hU₂.mem_nhds hx₂] with x hx
    exact hi₂ x hx

/-- The complete actual local family required by native compact gluing, on the SAME H/nu.
Source: main.tex539–550. Choose the genuinely constructed local solution at every sourcepoint;
actual native competitor uniqueness gives the joint germ at each overlap point. No desired
local solution, jet dictionary, invertibility or overlap equality is an additional hypothesis. -/
theorem collarHopf_local_cauchy_family (H ν : FreeHopfProduct C → L)
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, L) ω H)
    (hν : ContMDiff (freeHopfModel C) 𝓘(ℝ, L) ω ν)
    (hLI : ∀ x, LinearIndependent ℝ
      (Sum.elim (fun _ : Unit ↦ ν x) (freeFlowColumns (freeHopfProductFlow C) H x))) :
    ∃ U : FreeHopfProduct C → Set (FreeHopfProduct C), ∃ r : FreeHopfProduct C → ℝ,
      ∃ g : FreeHopfProduct C → ℝ × FreeHopfProduct C → L,
        (∀ i, IsOpen (U i)) ∧ (∀ i, 0 < r i) ∧ (∀ x, x ∈ U x) ∧
        (∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C)) 𝓘(ℝ, L) ω (g i)
          (Set.Ioo (-(r i)) (r i) ×ˢ U i)) ∧
        (∀ i j x, x ∈ U i → x ∈ U j → g i =ᶠ[𝓝 ((0 : ℝ), x)] g j) ∧
        (∀ i x, x ∈ U i → g i (0, x) = H x ∧ hopfCollarRDeriv (g i) 0 x = ν x) ∧
        ∀ i t x, (t, x) ∈ Set.Ioo (-(r i)) (r i) ×ˢ U i →
          (hopfCollarSquarePairing C (g i) t x).IsInvertible ∧
            deriv (fun s ↦ hopfCollarRDeriv (g i) s x) t =
              (hopfCollarSquarePairing C (g i) t x).inverse
                (hopfCollarSquareForcing C (g i) t x) := by
  choose U hU hx r hr g hg hi hp using
    (fun x ↦ collarHopfLocalCK_native C x H ν hH hν (hLI x))
  refine ⟨U, r, g, hU, hr, hx, hg, ?_, hi, hp⟩
  intro i j x hxi hxj
  exact collarHopf_native_tubes_germ_unique C x H ν hH hν (hLI x)
    (U i) (U j) (hU i) (hU j) hxi hxj (r i) (r j) (hr i) (hr j)
    (g i) (g j) (hg i) (hg j) (hi i) (hi j) (hp i) (hp j)

end ChartJet

#print axioms collarHopf_native_tubes_germ_unique
#print axioms collarHopf_local_cauchy_family
#print axioms collarHopf_native_germ_unique
#print axioms collarHopf_native_CK_competitor
#print axioms collarHopfChartFunction
#print axioms collarHopfChartFunction_analyticAt
#print axioms collarHopfReconstruct_chartFunction_germ
#print axioms collarHopfLocalCK_native
#print axioms collarHopfReconstruct_omega
#print axioms collarHopfSolutionJet_analyticAt
#print axioms collarHopfSolutionJet_initial
end GlobalEmbedding.Paper
