import GlobalEmbedding.Paper.FreeHopfOrbitLift
import GlobalEmbedding.Paper.FreeHopfUnitComplements
import GlobalEmbedding.Paper.DirectionalDerivativeBound

/-!
# Actual original column jets along genuine Hopf orbits

Source: `main.tex`, prop:collar, lines520–534.
DAG: `collar-hopf-column-orbit-jet-bound`; exclusive AS2b owner W2.
Reuse the ACCEPTED directional contraction bound, rather than proving it again.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- Bounds for the true observable orbit jets through n+2 bound the nth orbit
jet of EVERY original first/sortedsecond column by the same constant.

Proof: the accepted native lift identities identify the actual columns with
one or two true coordinate derivatives. Apply the accepted directional jet
contraction once or twice, in the actual Euclidean unit directions. Thus n<=3
requires only five observable derivatives, including all nonlinear action terms.
Source: actual ambient C5 input discharge in prop:collar, lines520–534. -/
theorem collarHopf_column_orbit_jet_bound {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (U : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hU : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (x : FreeHopfProduct C) (y : EuclideanSpace ℝ (Fin a)) (n : ℕ)
    (M : ℝ) (hM : ∀ i ≤ n + 2,
      ‖iteratedFDeriv ℝ i (U ∘ freeHopfOrbitLift C x) y‖ ≤ M)
    (k : BalancedPairingIndex a) :
    ‖iteratedFDeriv ℝ n (fun t : EuclideanSpace ℝ (Fin a) ↦
      freeFlowColumns (freeHopfProductFlow C) U (freeHopfOrbitLift C x t) k) y‖ ≤ M := by
  let G := U ∘ freeHopfOrbitLift C x
  have hG : ContDiff ℝ ∞ G :=
    (hU.comp (freeHopfOrbitLift_contMDiff C x)).contDiff
  have hdir (i : Fin a) :
      ContDiff ℝ ∞ (fun t ↦ fderiv ℝ G t (EuclideanSpace.single i 1)) :=
    (hG.fderiv_right (by simp)).clm_apply contDiff_const
  have hcol (t : EuclideanSpace ℝ (Fin a)) :
      freeFlowColumns (freeHopfProductFlow C) U (freeHopfOrbitLift C x t) =
        balancedPairingColumns U (freeHopfGenerator C) (freeHopfOrbitLift C x t) :=
    (freeHopf_balanced_pairing_columns C U hU _).symm
  cases k with
  | inl i =>
    have he : (fun t : EuclideanSpace ℝ (Fin a) ↦
        freeFlowColumns (freeHopfProductFlow C) U (freeHopfOrbitLift C x t) (.inl i)) =
        (fun t ↦ fderiv ℝ G t (EuclideanSpace.single i 1)) := by
      funext t
      rw [hcol]
      exact freeHopf_first_orbitLift C U hU x t i
    rw [he]
    have hb := (directional_derivative_iterated_bound n G
      (hG.of_le (by simp)) (EuclideanSpace.single i 1) y y).1
    have hunit : ‖(EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin a))‖ = 1 := by simp
    rw [hunit, one_mul] at hb
    exact hb.trans (hM (n + 1) (by omega))
  | inr ij =>
    have he : (fun t : EuclideanSpace ℝ (Fin a) ↦
        freeFlowColumns (freeHopfProductFlow C) U (freeHopfOrbitLift C x t) (.inr ij)) =
        (fun t ↦ fderiv ℝ (fun z ↦ fderiv ℝ G z (EuclideanSpace.single ij.val.2 1)) t
          (EuclideanSpace.single ij.val.1 1)) := by
      funext t
      rw [hcol]
      exact freeHopf_second_orbitLift C U hU x t ij.val.1 ij.val.2
    rw [he]
    have hb := (directional_derivative_iterated_bound n _
      ((hdir ij.val.2).of_le (by simp)) (EuclideanSpace.single ij.val.1 1) y y).1
    have hc := (directional_derivative_iterated_bound (n + 1) G
      (hG.of_le (by simp)) (EuclideanSpace.single ij.val.2 1) y y).1
    have hunit (i : Fin a) : ‖(EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin a))‖ = 1 := by simp
    rw [hunit, one_mul] at hb hc
    exact hb.trans (hc.trans (hM (n + 2) (by omega)))

end GlobalEmbedding.Paper
