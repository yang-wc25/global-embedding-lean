import GlobalEmbedding.Paper.CollarCKCanonicalAnalyticReconstruction
import GlobalEmbedding.Paper.CollarCKTaylorComposition
import GlobalEmbedding.Paper.CollarCKAnalyticGermInjectivity
import GlobalEmbedding.Paper.CollarCKFlattenSubstitution
import GlobalEmbedding.Paper.CollarCKTaylorCoordinatePartial

/-!
# Actual analytic PDE bridge for the same canonical CK formal solution

Source: Gantumur, notes2, Theorem18. Reuse the sole actual formal solution, shared Taylor
coefficients, nonlinear composition dictionary and actual analytic derivative dictionary.
The original word-enumeration checkpoint is preserved as history and is not republished.
-/

noncomputable section
open scoped Topology
namespace GlobalEmbedding.Paper

variable {n m : ℕ}
local notation "S" => (CollarCKFullIndex n → ℝ)
local notation "A" => ((Fin n ⊕ CollarCKSlot n m) → ℝ)
local notation "V" => (Fin m → ℝ)

/-- Actual derivatives and nonlinear evaluation of a genuine analytic representative of the
same canonical formal solution satisfy the actual componentwise CK PDE near the origin.
Source: Gantumur, Theorem18. The two explicit scalar dictionary laws are the independently
owned W3 providers, instantiated in the final interface after their normal publication.
All other data are actual expansions and the exact coefficient identity produced by canonical
reconstruction. In particular the PDE, origin of inner slots and substitution identity are
proved here. This intermediate theorem is not the full original CK existence/uniqueness result. -/
theorem collarCKAnalyticPDE_of_dictionaries
    (hconstant : ∀ (f : S → ℝ) (p : FormalMultilinearSeries ℝ S ℝ),
      HasFPowerSeriesAt f p 0 →
      MvPowerSeries.constantCoeff
        (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries (CollarCKFullIndex n) ℝ) = f 0)
    (hcoordinate : ∀ i (p : FormalMultilinearSeries ℝ S ℝ),
      HasFPowerSeriesAt (fun z ↦ z i) p 0 →
      (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries (CollarCKFullIndex n) ℝ) =
        MvPowerSeries.X i)
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
  classical
  let U := collarCKFormalSolution (collarCKTaylorRHS p)
  let qj (j : Fin m) : FormalMultilinearSeries ℝ S ℝ :=
    (ContinuousLinearMap.proj j).compFormalMultilinearSeries q
  have huj (j : Fin m) : HasFPowerSeriesAt (fun z ↦ u z j) (qj j) 0 := by
    obtain ⟨r, hr⟩ := hu
    exact ((ContinuousLinearMap.proj j).comp_hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
  have hcj (j : Fin m) :
      (fun d ↦ collarCKTaylorCoeff (qj j) d : MvPowerSeries (CollarCKFullIndex n) ℝ) =
        collarCKFlatten U j := by
    apply MvPowerSeries.ext
    intro d
    change collarCKTaylorCoeff (qj j) d = _
    rw [collarCKTaylorCoeff_component]
    exact hcoeff d j
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
    · exact (hcoordinate (Sum.inr i) (si (Sum.inl i)) (hsi (Sum.inl i))).trans
        (collarCKFullSlots_spatial U i).symm
    · exact (hcoordinate (Sum.inl ()) (si (Sum.inr (Sum.inl ())))
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
      (collarCKFormalSolution_spec (collarCKTaylorRHS p)).1).const_coeff a).eq_zero
    rw [← hslots] at hz
    exact (hconstant (fun z ↦ v z a) (si a) (hsi a)).symm.trans hz
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
  have hevent (j : Fin m) : ∀ᶠ z in 𝓝 (0 : S),
      fderiv ℝ (fun y ↦ u y j) z (Pi.single (Sum.inl ()) 1) = g (v z) j := by
    obtain ⟨pd, hd⟩ := hderiv (Sum.inl ()) j
    have hR : AnalyticAt ℝ (fun z ↦ g (v z) j) 0 :=
      (hgj j).analyticAt.comp_of_eq hs.analyticAt hv0
    obtain ⟨r, hr⟩ := hR
    have hD := collarCKTaylorPackage_partial (fun z ↦ u z j) (qj j) pd (huj j) (Sum.inl ()) hd
    rw [hcj] at hD
    have hRpkg := collarCKTaylorCoeff_analytic_comp v (fun z ↦ g z j)
      (pj j) s r hs (hgj j) hr hv0
    have hcomponents : (fun a ↦ (fun d ↦ collarCKTaylorCoeff
        ((ContinuousLinearMap.proj a).compFormalMultilinearSeries s) d :
          MvPowerSeries (CollarCKFullIndex n) ℝ)) = collarCKFullSlots U := by
      funext a
      exact hslots a
    rw [hcomponents, hgpkg] at hRpkg
    have hsame : (fun e ↦ collarCKTaylorCoeff pd e : MvPowerSeries (CollarCKFullIndex n) ℝ) =
        (fun e ↦ collarCKTaylorCoeff r e : MvPowerSeries (CollarCKFullIndex n) ℝ) := by
      exact hD.trans ((collarCKFormalSolution_fullEquation (collarCKTaylorRHS p) j).trans
        hRpkg.symm)
    apply collarCKAnalyticGerm_of_coefficients _ _ pd r hd hr
    intro e
    exact congrArg (MvPowerSeries.coeff e) hsame
  exact Filter.eventually_all.mpr hevent

/-- The same canonical convergent formal solution gives an actual analytic map solving the
actual full-variable normalized PDE and the entire zero initial hypersurface. Source: Gantumur,
Theorem18. All convergence and coefficient data come from the accepted canonical reconstruction;
this theorem then invokes the actual derivative/substitution proof above. The explicit generic
scalar dictionary laws are eliminated in the final interface by their sole W3 providers. -/
theorem collarCKAnalyticRealization_of_bound
    (hconstant : ∀ (f : S → ℝ) (p : FormalMultilinearSeries ℝ S ℝ),
      HasFPowerSeriesAt f p 0 →
      MvPowerSeries.constantCoeff
        (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries (CollarCKFullIndex n) ℝ) = f 0)
    (hcoordinate : ∀ i (p : FormalMultilinearSeries ℝ S ℝ),
      HasFPowerSeriesAt (fun z ↦ z i) p 0 →
      (fun d ↦ collarCKTaylorCoeff p d : MvPowerSeries (CollarCKFullIndex n) ℝ) =
        MvPowerSeries.X i)
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
  obtain ⟨q, u, δ, _, _, hq, heval, hinitial, hcoeff⟩ :=
    collarCKCanonicalAnalyticReconstruction (collarCKTaylorRHS p) M s hM hs hbound
  refine ⟨q, hq, hcoeff, ?_,
    collarCKAnalyticPDE_of_dictionaries hconstant hcoordinate g p hg q.sum q hq hcoeff⟩
  intro z hz
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ z (Sum.inr i))
  have heq : Sum.elim (fun _ : Unit ↦ (0 : ℝ)) (fun i ↦ x i) = z := by
    funext a
    rcases a with ⟨⟩ | i
    · exact hz.symm
    · rfl
  rw [← heq, ← heval 0 x, hinitial x]

#print axioms collarCKAnalyticPDE_of_dictionaries
#print axioms collarCKAnalyticRealization_of_bound
end GlobalEmbedding.Paper
