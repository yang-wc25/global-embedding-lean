import GlobalEmbedding.Paper.CollarCKAnalyticPDEBridge
import GlobalEmbedding.Paper.CollarCKAnalyticTaylorCalculus
import GlobalEmbedding.Paper.CollarCKTaylorScalarCoordinate
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Analytic realization and actual analytic-germ uniqueness for the same normalized CK system

Source: Gantumur, notes2, Theorem18. Reuse the canonical actual formal solution and shared
Taylor dictionaries. The actual geometric coefficient bound is supplied by the separate
majorant proof; every actual derivative, nonlinear substitution and competitor identity is
proved here. No dimension positivity, supplied solution or generic dictionary premise remains.
-/

noncomputable section
open scoped Topology
namespace GlobalEmbedding.Paper
variable {n m : ℕ}
local notation "S" => (CollarCKFullIndex n → ℝ)
local notation "V" => (Fin m → ℝ)
local notation "A" => ((Fin n ⊕ CollarCKSlot n m) → ℝ)

/-- A genuine analytic competitor whose literal Taylor package solves the same formal
Cauchy problem agrees with the actual canonical representative as a germ.
Source: Gantumur, Theorem18, formal uniqueness followed by analytic uniqueness. Reuse the
existing unflattening, exact actual formal uniqueness and reverse-germ theorem. The normal
constant and formal PDE hypotheses are intermediate obligations to be derived from the
competitor's actual whole Cauchy data and actual PDE in the full parent, not new CK premises. -/
theorem collarCKAnalyticFormalCompetitor_germ
    (G : CollarCKRHS n m) (u v : S → V)
    (p q : FormalMultilinearSeries ℝ S V)
    (hu : HasFPowerSeriesAt u p 0) (hv : HasFPowerSeriesAt v q 0)
    (hcanonical : ∀ d j, collarCKTaylorCoeff p d j =
      MvPowerSeries.coeff d (collarCKFlatten (collarCKFormalSolution G) j))
    (hzero : PowerSeries.constantCoeff
      (collarCKUnflatten (fun j d ↦ collarCKTaylorCoeff q d j)) = 0)
    (hequation : PowerSeries.derivative
      (collarCKUnflatten (fun j d ↦ collarCKTaylorCoeff q d j)) =
        collarCKSubstitutedRHS G
          (collarCKUnflatten (fun j d ↦ collarCKTaylorCoeff q d j))) :
    u =ᶠ[𝓝 0] v := by
  let U := collarCKUnflatten (fun j d ↦ collarCKTaylorCoeff q d j)
  have hU : U = collarCKFormalSolution G :=
    collarCKFormalSolution_unique G U hzero hequation
  apply collarCKAnalyticGerm_of_coefficients u v p q hu hv
  intro d
  funext j
  rw [hcanonical]
  have hflat : collarCKFlatten U j =
      (fun d ↦ collarCKTaylorCoeff q d j : MvPowerSeries (CollarCKFullIndex n) ℝ) :=
    collarCKFlatten_unflatten _ j
  rw [hU] at hflat
  exact congrArg (MvPowerSeries.coeff d) hflat

/-- Actual zero Cauchy data force every genuine coefficient with zero normal exponent to
vanish. Source: Gantumur, Theorem18. Restrict the actual expansion to time0. Native uniqueness
of diagonal terms of a zero analytic function kills its homogeneous terms. The accepted
homogeneous polynomial, with all time variables killed by native `killCompl`, therefore has
zero evaluations and is zero. Its native coefficient formula selects the original spatial
coefficient, without a new Taylor convention or word-fiber bijection. -/
theorem collarCKTaylorCoeff_zero_initial
    (f : S → ℝ) (p : FormalMultilinearSeries ℝ S ℝ)
    (hp : HasFPowerSeriesAt f p 0)
    (hinitial : ∀ᶠ x : Fin n → ℝ in 𝓝 0,
      f (Sum.elim (fun _ : Unit ↦ (0 : ℝ)) x) = 0) (β : Fin n →₀ ℕ) :
    collarCKTaylorCoeff p (collarCKMultiIndex 0 β) = 0 := by
  classical
  let L : (Fin n → ℝ) →L[ℝ] S := ContinuousLinearMap.pi
    (Sum.elim (fun _ : Unit ↦ 0) (fun i ↦ ContinuousLinearMap.proj i))
  have hL (x : Fin n → ℝ) : L x = Sum.elim (fun _ : Unit ↦ (0 : ℝ)) x := by
    funext a
    rcases a with ⟨⟩ | i <;> rfl
  have hpL : HasFPowerSeriesAt (fun x ↦ f (L x)) (p.compContinuousLinearMap L) 0 := by
    have h : HasFPowerSeriesAt f p (L 0) := by simpa only [map_zero] using hp
    exact h.compContinuousLinearMap
  have hz : HasFPowerSeriesAt (0 : (Fin n → ℝ) → ℝ)
      (p.compContinuousLinearMap L) 0 := by
    apply hpL.congr
    filter_upwards [hinitial] with x hx
    exact (congrArg f (hL x)).trans hx
  have hdiag (k : ℕ) (x : Fin n → ℝ) : p k (fun _ ↦ L x) = 0 := by
    simpa only [FormalMultilinearSeries.compContinuousLinearMap_apply,
      Function.comp_def] using hz.apply_eq_zero k x
  let P : MvPolynomial (CollarCKFullIndex n) ℝ :=
    MvPowerSeries.truncFinset ℝ
      (Finset.univ.image (collarCKWordIndex (σ := CollarCKFullIndex n) (k := β.degree)))
      (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries (CollarCKFullIndex n) ℝ)
  let X0 : CollarCKFullIndex n → MvPolynomial (Fin n) ℝ :=
    Sum.elim (fun _ : Unit ↦ 0) MvPolynomial.X
  have hkill : MvPolynomial.killCompl (R := ℝ)
      (Sum.inr_injective : Function.Injective (Sum.inr : Fin n → CollarCKFullIndex n)) =
        MvPolynomial.aeval X0 := by
    apply MvPolynomial.algHom_ext
    intro a
    rcases a with ⟨⟩ | i
    · simp [MvPolynomial.killCompl, X0]
    · simpa only [MvPolynomial.rename_X, MvPolynomial.aeval_X, X0, Sum.elim_inr] using
        MvPolynomial.killCompl_rename_app
          (Sum.inr_injective : Function.Injective (Sum.inr : Fin n → CollarCKFullIndex n))
          (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)
  have hzero : P.killCompl Sum.inr_injective = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [hkill, MvPolynomial.aeval_def, MvPolynomial.eval_eval₂]
    have hc : (MvPolynomial.eval x).comp (algebraMap ℝ (MvPolynomial (Fin n) ℝ)) =
        RingHom.id ℝ := by ext r; simp
    rw [hc, MvPolynomial.eval₂_id]
    have hx : (fun a ↦ MvPolynomial.eval x (X0 a)) = L x := by
      funext a
      rcases a with ⟨⟩ | i <;> simp [X0, hL]
    rw [hx]
    have heval : MvPolynomial.eval (L x) P = p β.degree (fun _ ↦ L x) :=
      collarCKTaylorHomogeneous_eval p β.degree (L x)
    rw [heval, hdiag, map_zero]
  have hco := congrArg (fun Q : MvPolynomial (Fin n) ℝ ↦ Q.coeff β) hzero
  rw [MvPolynomial.coeff_killCompl] at hco
  have hdegree : (β.mapDomain (Sum.inr : Fin n → CollarCKFullIndex n)).degree = β.degree := by
    simp
  have hP : P.coeff (β.mapDomain (Sum.inr : Fin n → CollarCKFullIndex n)) =
      collarCKTaylorCoeff p (β.mapDomain (Sum.inr : Fin n → CollarCKFullIndex n)) := by
    simpa only [hdegree, ite_true] using
      collarCKTaylorHomogeneous_coeff p β.degree
        (β.mapDomain (Sum.inr : Fin n → CollarCKFullIndex n))
  have hindex : β.mapDomain (Sum.inr : Fin n → CollarCKFullIndex n) =
      collarCKMultiIndex 0 β := by
    calc
      _ = β.embDomain (Function.Embedding.inr : Fin n ↪ CollarCKFullIndex n) :=
        (Finsupp.embDomain_eq_mapDomain _ β).symm
      _ = Finsupp.sumElim 0 β := Finsupp.embDomain_inr β
      _ = _ := by simp [collarCKMultiIndex]
  rw [← hindex]
  exact hP.symm.trans hco

/-- The entire normal-constant spatial series of an actual zero-Cauchy competitor vanishes.
Source: Gantumur, Theorem18. Project its actual vector expansion, apply the preceding genuine
zero-initial coefficient theorem, and use the already accepted exact unflattening formula. -/
theorem collarCKUnflatten_zero_initial
    (u : S → V) (q : FormalMultilinearSeries ℝ S V)
    (hu : HasFPowerSeriesAt u q 0)
    (hinitial : ∀ᶠ x : Fin n → ℝ in 𝓝 0,
      u (Sum.elim (fun _ : Unit ↦ (0 : ℝ)) x) = 0) :
    PowerSeries.constantCoeff
      (collarCKUnflatten (fun j d ↦ collarCKTaylorCoeff q d j)) = 0 := by
  let F : Fin m → MvPowerSeries (CollarCKFullIndex n) ℝ :=
    fun j d ↦ collarCKTaylorCoeff q d j
  change PowerSeries.constantCoeff (collarCKUnflatten F) = 0
  funext j
  apply MvPowerSeries.ext
  intro β
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  change collarCKCoeff (collarCKUnflatten F) 0 β j = 0
  rw [collarCKUnflatten_coeff]
  change collarCKTaylorCoeff q (collarCKMultiIndex 0 β) j = 0
  let p : FormalMultilinearSeries ℝ S ℝ :=
    (ContinuousLinearMap.proj j).compFormalMultilinearSeries q
  have hp : HasFPowerSeriesAt (fun z ↦ u z j) p 0 := by
    obtain ⟨r, hr⟩ := hu
    exact ((ContinuousLinearMap.proj j).comp_hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
  have hi : ∀ᶠ x : Fin n → ℝ in 𝓝 0,
      u (Sum.elim (fun _ : Unit ↦ (0 : ℝ)) x) j = 0 := by
    filter_upwards [hinitial] with x hx
    exact congrFun hx j
  have h := collarCKTaylorCoeff_zero_initial (fun z ↦ u z j) p hp hi β
  rw [collarCKTaylorCoeff_component] at h
  exact h

/-- An actual analytic competitor with genuine zero Cauchy data and the actual PDE has
Taylor coefficients satisfying the original iterated formal PDE. Source: Gantumur, Theorem18.
Reuse the accepted actual slot identification argument, now for the native unflattening of
this competitor's literal coefficients. Zero initial data supplies its true normalconstant0.
Actual composition/partial calculus and actual germ equality transport the PDE to full formal
coefficients, and the accepted flattening equivalence recovers the same normal formal system. -/
theorem collarCKAnalyticFormalEquation
    (g : A → V) (p : FormalMultilinearSeries ℝ A V) (hg : HasFPowerSeriesAt g p 0)
    (u : S → V) (q : FormalMultilinearSeries ℝ S V) (hu : HasFPowerSeriesAt u q 0)
    (hinitial : ∀ᶠ x : Fin n → ℝ in 𝓝 0,
      u (Sum.elim (fun _ : Unit ↦ (0 : ℝ)) x) = 0)
    (hPDE : ∀ᶠ z in 𝓝 (0 : S), ∀ j,
      fderiv ℝ (fun y ↦ u y j) z (Pi.single (Sum.inl ()) 1) =
        g (Sum.elim (fun i ↦ z (Sum.inr i))
          (Sum.elim (fun _ ↦ z (Sum.inl ()))
            (Sum.elim (fun j ↦ u z j)
              (fun ij ↦ fderiv ℝ (fun y ↦ u y ij.2) z (Pi.single (Sum.inr ij.1) 1))))) j) :
    PowerSeries.derivative (collarCKUnflatten (fun j d ↦ collarCKTaylorCoeff q d j)) =
      collarCKSubstitutedRHS (collarCKTaylorRHS p)
        (collarCKUnflatten (fun j d ↦ collarCKTaylorCoeff q d j)) := by
  classical
  let F : Fin m → MvPowerSeries (CollarCKFullIndex n) ℝ :=
    fun j d ↦ collarCKTaylorCoeff q d j
  let U := collarCKUnflatten F
  change PowerSeries.derivative U = collarCKSubstitutedRHS (collarCKTaylorRHS p) U
  have hzero : PowerSeries.constantCoeff U = 0 :=
    collarCKUnflatten_zero_initial u q hu hinitial
  let qj (j : Fin m) : FormalMultilinearSeries ℝ S ℝ :=
    (ContinuousLinearMap.proj j).compFormalMultilinearSeries q
  have huj (j : Fin m) : HasFPowerSeriesAt (fun z ↦ u z j) (qj j) 0 := by
    obtain ⟨r, hr⟩ := hu
    exact ((ContinuousLinearMap.proj j).comp_hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
  have hcj (j : Fin m) :
      (fun d ↦ collarCKTaylorCoeff (qj j) d : MvPowerSeries (CollarCKFullIndex n) ℝ) =
        collarCKFlatten U j := by
    rw [show collarCKFlatten U j = F j from collarCKFlatten_unflatten F j]
    apply MvPowerSeries.ext
    intro d
    change collarCKTaylorCoeff (qj j) d = collarCKTaylorCoeff q d j
    exact collarCKTaylorCoeff_component q j d
  have hderiv (i : CollarCKFullIndex n) (j : Fin m) :
      AnalyticAt ℝ (fun z ↦ fderiv ℝ (fun y ↦ u y j) z (Pi.single i 1)) 0 :=
    ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : S)).analyticAt _).comp
      (huj j).analyticAt.fderiv
  let v : S → A := fun z ↦ Sum.elim (fun i ↦ z (Sum.inr i))
    (Sum.elim (fun _ ↦ z (Sum.inl ()))
      (Sum.elim (fun j ↦ u z j)
        (fun ij ↦ fderiv ℝ (fun y ↦ u y ij.2) z (Pi.single (Sum.inr ij.1) 1))))
  have hv : AnalyticAt ℝ v 0 := by
    apply AnalyticAt.pi
    intro a
    rcases a with i | (_ | (j | ⟨i, j⟩))
    · exact (ContinuousLinearMap.proj (Sum.inr i) : S →L[ℝ] ℝ).analyticAt _
    · exact (ContinuousLinearMap.proj (Sum.inl ()) : S →L[ℝ] ℝ).analyticAt _
    · exact (huj j).analyticAt
    · exact hderiv (Sum.inr i) j
  obtain ⟨s, hs⟩ := hv
  let si (a : Fin n ⊕ CollarCKSlot n m) : FormalMultilinearSeries ℝ S ℝ :=
    (ContinuousLinearMap.proj a).compFormalMultilinearSeries s
  have hsi (a) : HasFPowerSeriesAt (fun z ↦ v z a) (si a) 0 := by
    obtain ⟨r, hr⟩ := hs
    exact ((ContinuousLinearMap.proj a).comp_hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
  have hslots (a) :
      (fun d ↦ collarCKTaylorCoeff (si a) d : MvPowerSeries (CollarCKFullIndex n) ℝ) =
        collarCKFullSlots U a := by
    rcases a with i | (_ | (j | ⟨i, j⟩))
    · exact (collarCKTaylorPackage_scalar_coordinate (Sum.inr i) (si (Sum.inl i))
        (hsi (Sum.inl i))).trans
        (collarCKFullSlots_spatial U i).symm
    · exact (collarCKTaylorPackage_scalar_coordinate (Sum.inl ()) (si (Sum.inr (Sum.inl ())))
        (hsi (Sum.inr (Sum.inl ())))).trans
        (collarCKFullSlots_time U).symm
    · have heq :
          (fun d ↦ collarCKTaylorCoeff (si (Sum.inr (Sum.inr (Sum.inl j)))) d :
            MvPowerSeries (CollarCKFullIndex n) ℝ) =
          (fun d ↦ collarCKTaylorCoeff (qj j) d : MvPowerSeries (CollarCKFullIndex n) ℝ) := by
        apply MvPowerSeries.ext
        intro d
        exact collarCKTaylorCoeff_unique (fun z ↦ u z j)
          (si (Sum.inr (Sum.inr (Sum.inl j)))) (qj j)
          (hsi (Sum.inr (Sum.inr (Sum.inl j)))) (huj j) d
      exact (heq.trans (hcj j)).trans (collarCKFullSlots_value U j).symm
    · have heq := collarCKTaylorPackage_partial (fun z ↦ u z j) (qj j)
        (si (Sum.inr (Sum.inr (Sum.inr (i, j))))) (huj j) (Sum.inr i)
        (hsi (Sum.inr (Sum.inr (Sum.inr (i, j)))))
      rw [hcj] at heq
      exact heq.trans (collarCKFullSlots_gradient U i j).symm
  have hv0 : v 0 = 0 := by
    funext a
    have hz := ((collarCKFullSlots_hasSubst U
      hzero).const_coeff a).eq_zero
    rw [← hslots] at hz
    exact (collarCKTaylorPackage_constantCoeff (fun z ↦ v z a) (si a) (hsi a)).symm.trans hz
  let pj (j : Fin m) : FormalMultilinearSeries ℝ A ℝ :=
    (ContinuousLinearMap.proj j).compFormalMultilinearSeries p
  have hgj (j : Fin m) : HasFPowerSeriesAt (fun z ↦ g z j) (pj j) 0 := by
    obtain ⟨r, hr⟩ := hg
    exact ((ContinuousLinearMap.proj j).comp_hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
  have hgpkg (j : Fin m) :
      (fun d ↦ collarCKTaylorCoeff (pj j) d : MvPowerSeries (Fin n ⊕ CollarCKSlot n m) ℝ) =
        collarCKFullRHS (collarCKTaylorRHS p) j := by
    apply MvPowerSeries.ext
    intro d
    rw [collarCKFullRHS, collarCKUngroup_coeff, collarCKTaylorRHS_full_coeff]
    exact collarCKTaylorCoeff_component p j d
  have hfull (j : Fin m) :
      MvPowerSeries.pderiv (Sum.inl ()) (collarCKFlatten U j) =
        MvPowerSeries.subst (collarCKFullSlots U) (collarCKFullRHS (collarCKTaylorRHS p) j) := by
    obtain ⟨pd, hd⟩ := hderiv (Sum.inl ()) j
    have hR : AnalyticAt ℝ (fun z ↦ g (v z) j) 0 :=
      (hgj j).analyticAt.comp_of_eq hs.analyticAt hv0
    obtain ⟨r, hr⟩ := hR
    have hD := collarCKTaylorPackage_partial (fun z ↦ u z j) (qj j) pd
      (huj j) (Sum.inl ()) hd
    rw [hcj] at hD
    have hRpkg := collarCKTaylorCoeff_analytic_comp v (fun z ↦ g z j)
      (pj j) s r hs (hgj j) hr hv0
    have hcomponents : (fun a ↦ (fun d ↦ collarCKTaylorCoeff
        ((ContinuousLinearMap.proj a).compFormalMultilinearSeries s) d :
          MvPowerSeries (CollarCKFullIndex n) ℝ)) = collarCKFullSlots U := by
      funext a
      exact hslots a
    rw [hcomponents, hgpkg] at hRpkg
    have hactual : (fun z ↦ fderiv ℝ (fun y ↦ u y j) z (Pi.single (Sum.inl ()) 1)) =ᶠ[𝓝 0]
        (fun z ↦ g (v z) j) := by
      filter_upwards [hPDE] with z hz
      exact hz j
    have hsame : (fun e ↦ collarCKTaylorCoeff pd e : MvPowerSeries (CollarCKFullIndex n) ℝ) =
        (fun e ↦ collarCKTaylorCoeff r e : MvPowerSeries (CollarCKFullIndex n) ℝ) := by
      apply MvPowerSeries.ext
      intro e
      exact collarCKTaylorCoeff_congr _ _ pd r hd hr hactual e
    exact hD.symm.trans (hsame.trans hRpkg)
  have hfun : collarCKFlatten (PowerSeries.derivative U) =
      collarCKFlatten (collarCKSubstitutedRHS (collarCKTaylorRHS p) U) := by
    funext j
    rw [collarCKFlatten_normalDeriv, collarCKFlattenSubstitution _ U hzero j]
    exact hfull j
  exact (collarCKUnflatten_flatten _).symm.trans
    ((congrArg collarCKUnflatten hfun).trans (collarCKUnflatten_flatten _))

/-- Every actual analytic competitor with the same genuine Cauchy data and actual PDE
agrees with the canonical analytic representative near0. Source: Gantumur, Theorem18.
The preceding two theorems discharge both formal-competitor obligations from actual data;
then actual formal uniqueness and the accepted reverse-germ theorem finish the proof. -/
theorem collarCKAnalyticCompetitor_germ
    (g : A → V) (p : FormalMultilinearSeries ℝ A V) (hg : HasFPowerSeriesAt g p 0)
    (u : S → V) (pu : FormalMultilinearSeries ℝ S V) (hu : HasFPowerSeriesAt u pu 0)
    (hcanonical : ∀ d j, collarCKTaylorCoeff pu d j = MvPowerSeries.coeff d
      (collarCKFlatten (collarCKFormalSolution (collarCKTaylorRHS p)) j))
    (v : S → V) (q : FormalMultilinearSeries ℝ S V) (hv : HasFPowerSeriesAt v q 0)
    (hinitial : ∀ᶠ x : Fin n → ℝ in 𝓝 0,
      v (Sum.elim (fun _ : Unit ↦ (0 : ℝ)) x) = 0)
    (hPDE : ∀ᶠ z in 𝓝 (0 : S), ∀ j,
      fderiv ℝ (fun y ↦ v y j) z (Pi.single (Sum.inl ()) 1) =
        g (Sum.elim (fun i ↦ z (Sum.inr i))
          (Sum.elim (fun _ ↦ z (Sum.inl ()))
            (Sum.elim (fun j ↦ v z j)
              (fun ij ↦ fderiv ℝ (fun y ↦ v y ij.2) z (Pi.single (Sum.inr ij.1) 1))))) j) :
    u =ᶠ[𝓝 0] v :=
  collarCKAnalyticFormalCompetitor_germ (collarCKTaylorRHS p) u v pu q hu hv hcanonical
    (collarCKUnflatten_zero_initial v q hv hinitial)
    (collarCKAnalyticFormalEquation g p hg v q hv hinitial hPDE)

/-- The actual SAMEsolution PDE with every scalar dictionary parameter eliminated by the
accepted sole providers. Source: Gantumur, Theorem18. This is a direct instantiation of the
accepted PDE bridge, not another derivative/substitution proof. -/
theorem collarCKAnalyticPDE
    (g : A → V) (p : FormalMultilinearSeries ℝ A V) (hg : HasFPowerSeriesAt g p 0)
    (u : S → V) (q : FormalMultilinearSeries ℝ S V) (hu : HasFPowerSeriesAt u q 0)
    (hcoeff : ∀ d j, collarCKTaylorCoeff q d j =
      MvPowerSeries.coeff d
        (collarCKFlatten (collarCKFormalSolution (collarCKTaylorRHS p)) j)) :
    ∀ᶠ z in 𝓝 (0 : S), ∀ j,
      fderiv ℝ (fun y ↦ u y j) z (Pi.single (Sum.inl ()) 1) =
        g (Sum.elim (fun i ↦ z (Sum.inr i))
          (Sum.elim (fun _ ↦ z (Sum.inl ()))
            (Sum.elim (fun j ↦ u z j)
              (fun ij ↦ fderiv ℝ (fun y ↦ u y ij.2) z (Pi.single (Sum.inr ij.1) 1))))) j := by
  exact collarCKAnalyticPDE_of_dictionaries collarCKTaylorPackage_constantCoeff
    collarCKTaylorPackage_scalar_coordinate g p hg u q hu hcoeff

/-- From a genuine geometric bound on the same canonical formal solution, construct the
actual analytic map with wholezero initial data and its actual nonlinear PDE. Source: Gantumur,
Theorem18. All scalar calculus dictionary parameters are discharged; only the actual geometric
bound remains to be supplied by W4's genuine majorant argument in the full original theorem. -/
theorem collarCKAnalyticRealizationGeometric
    (g : A → V) (p : FormalMultilinearSeries ℝ A V) (hg : HasFPowerSeriesAt g p 0)
    (M s : ℝ) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hbound : ∀ d j,
      |MvPowerSeries.coeff d
        (collarCKFlatten (collarCKFormalSolution (collarCKTaylorRHS p)) j)| ≤
          M * s ^ d.degree) :
    ∃ q : FormalMultilinearSeries ℝ S V,
      HasFPowerSeriesAt q.sum q 0 ∧
      (∀ d j, collarCKTaylorCoeff q d j = MvPowerSeries.coeff d
        (collarCKFlatten (collarCKFormalSolution (collarCKTaylorRHS p)) j)) ∧
      (∀ z : S, z (Sum.inl ()) = 0 → q.sum z = 0) ∧
      (∀ᶠ z in 𝓝 (0 : S), ∀ j,
        fderiv ℝ (fun y ↦ q.sum y j) z (Pi.single (Sum.inl ()) 1) =
          g (Sum.elim (fun i ↦ z (Sum.inr i))
            (Sum.elim (fun _ ↦ z (Sum.inl ()))
              (Sum.elim (fun j ↦ q.sum z j)
                (fun ij ↦ fderiv ℝ (fun y ↦ q.sum y ij.2) z
                  (Pi.single (Sum.inr ij.1) 1))))) j) := by
  exact collarCKAnalyticRealization_of_bound collarCKTaylorPackage_constantCoeff
    collarCKTaylorPackage_scalar_coordinate g p hg M s hM hs hbound

/-- Genuine analytic existence and analytic-germ uniqueness for the actual normalized PDE,
from a geometric bound on its same canonical formal solution. Source: Gantumur, Theorem18.
All scalar dictionary, formal compatibility and formal-competitor premises have been discharged.
The actual geometric bound remains the sole majorant obligation for the full original CK
statement, and must be supplied there by the independent genuine Goursat domination proof. -/
theorem collarCKAnalyticExistenceUniqueGeometric
    (g : A → V) (p : FormalMultilinearSeries ℝ A V) (hg : HasFPowerSeriesAt g p 0)
    (M s : ℝ) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hbound : ∀ d j,
      |MvPowerSeries.coeff d
        (collarCKFlatten (collarCKFormalSolution (collarCKTaylorRHS p)) j)| ≤
          M * s ^ d.degree) :
    ∃ u : S → V, AnalyticAt ℝ u 0 ∧
      (∀ z : S, z (Sum.inl ()) = 0 → u z = 0) ∧
      (∀ᶠ z in 𝓝 (0 : S), ∀ j,
        fderiv ℝ (fun y ↦ u y j) z (Pi.single (Sum.inl ()) 1) =
          g (Sum.elim (fun i ↦ z (Sum.inr i))
            (Sum.elim (fun _ ↦ z (Sum.inl ()))
              (Sum.elim (fun j ↦ u z j)
                (fun ij ↦ fderiv ℝ (fun y ↦ u y ij.2) z
                  (Pi.single (Sum.inr ij.1) 1))))) j) ∧
      ∀ v : S → V, AnalyticAt ℝ v 0 →
        (∀ᶠ x : Fin n → ℝ in 𝓝 0, v (Sum.elim (fun _ : Unit ↦ (0 : ℝ)) x) = 0) →
        (∀ᶠ z in 𝓝 (0 : S), ∀ j,
          fderiv ℝ (fun y ↦ v y j) z (Pi.single (Sum.inl ()) 1) =
            g (Sum.elim (fun i ↦ z (Sum.inr i))
              (Sum.elim (fun _ ↦ z (Sum.inl ()))
                (Sum.elim (fun j ↦ v z j)
                  (fun ij ↦ fderiv ℝ (fun y ↦ v y ij.2) z
                    (Pi.single (Sum.inr ij.1) 1))))) j) →
        u =ᶠ[𝓝 0] v := by
  obtain ⟨q, hq, hcoeff, hinitial, hPDE⟩ :=
    collarCKAnalyticRealizationGeometric g p hg M s hM hs hbound
  refine ⟨q.sum, hq.analyticAt, hinitial, hPDE, ?_⟩
  intro v hv hvi hvPDE
  obtain ⟨r, hr⟩ := hv
  exact collarCKAnalyticCompetitor_germ g p hg q.sum q hq hcoeff v r hr hvi hvPDE

#print axioms collarCKAnalyticFormalCompetitor_germ
#print axioms collarCKTaylorCoeff_zero_initial
#print axioms collarCKUnflatten_zero_initial
#print axioms collarCKAnalyticFormalEquation
#print axioms collarCKAnalyticCompetitor_germ
#print axioms collarCKAnalyticExistenceUniqueGeometric
#print axioms collarCKAnalyticPDE
#print axioms collarCKAnalyticRealizationGeometric
end GlobalEmbedding.Paper
