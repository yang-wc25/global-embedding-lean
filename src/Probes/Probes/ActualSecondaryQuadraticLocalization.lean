import Probes.ActualSecondaryRawTensorForcing

/-!
# The actual signed quadratic coefficient supplies the actual local hR/hI

The coefficient is the physical coefficient of the literal primary wave.
Every signed ordered forcing is first assembled as its true native tensor,
then pulled back by the genuine inverse transition on both slots and
multiplied by the ordinary subordinate cutoff. Full joint profiles, symmetry
and actual pair support are all produced; none is assumed for the chosen h.
-/

noncomputable section
open Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

 theorem actual_secondary_quadratic_localization_profiles
    (n N : ℕ) (MD Kcut : ℝ) (hMD : 0 ≤ MD) (hKcut : 0 ≤ Kcut)
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) :
    ∃ CH : ℝ, 0 ≤ CH ∧
      ∀ {Ep Label Sub : Type*} [Fintype Sub] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
        (phi : Label → Ep → D → ℝ) (tau : ℝ) (chi : Label → Ep → Sub → D → ℝ)
        (P Q : Label → Ep → Sub → D → EuclideanSpace ℝ (Fin N)) (nu mu : Label) (q : Fin 4)
        (e : OpenPartialHomeomorph (Ep × D) (Ep × D))
        (cutoff : Ep × D → ℝ) (hc : ContDiffOn ℝ ∞ cutoff e.source)
        (he : ContDiffOn ℝ ∞ e.symm e.target)
        (S : Set (Ep × D)) (hS : S ⊆ e.target) (ell delta : ℝ) (hell : 0 < ell)
        (hnu : ContDiffOn ℝ ∞ (fun z => incrementsSecondaryPhysicalCoefficient
          phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) z nu) e.source)
        (hmu : ContDiffOn ℝ ∞ (fun z => incrementsSecondaryPhysicalCoefficient
          phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) z mu) e.source)
        (hnub : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r
          (fun y => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
            (fun i _ => EuclideanSpace.single i 1) y nu) (e.symm z)‖ ≤ MD*|delta|)
        (hmub : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r
          (fun y => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
            (fun i _ => EuclideanSpace.single i 1) y mu) (e.symm z)‖ ≤ MD*|delta|)
        (hcut : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r cutoff (e.symm z)‖ ≤ Kcut)
        (hinv : ∀ r, 1 ≤ r → r ≤ n+1 → ∀ z ∈ S,
          ell^(r-1)*‖iteratedFDeriv ℝ r e.symm z‖ ≤ T r),
      let H := incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) nu mu q
      let HR := fun z => actualRealTensorAssembly (H z)
      let HI := fun z => actualImaginaryTensorAssembly (H z)
      let hR := actualSecondaryInverseForcing e cutoff HR
      let hI := actualSecondaryInverseForcing e cutoff HI
      ContDiffOn ℝ ∞ hR e.target ∧ ContDiffOn ℝ ∞ hI e.target ∧
      (∀ z ∈ e.target, ∀ i j, hR z i j = hR z j i) ∧
      (∀ z ∈ e.target, ∀ i j, hI z i j = hI z j i) ∧
      (∀ z ∈ e.target, z ∈ tsupport hR ∪ tsupport hI →
        e.symm z ∈ tsupport cutoff ∩
          (tsupport (fun y => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
            (fun i _ => EuclideanSpace.single i 1) y nu) ∩
          tsupport (fun y => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
            (fun i _ => EuclideanSpace.single i 1) y mu))) ∧
      (∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r hR z‖ ≤ CH*delta^2) ∧
      (∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r hI z‖ ≤ CH*delta^2) := by
  obtain ⟨CR,hCR,hraw⟩ := actual_secondary_quadratic_native_forcing_profiles (m := m) n N MD hMD
  have hloc := actualSecondaryLocalizationCost_nonneg T hT n Kcut hKcut
  refine ⟨actualSecondaryLocalizationCost T n Kcut*CR, mul_nonneg hloc hCR, ?_⟩
  intro Ep Label Sub _ _ _ phi tau chi P Q nu mu q e cutoff hc he S hS ell delta hell
    hnu hmu hnub hmub hcut hinv H HR HI hR hI
  let S0 := e.symm '' S
  have hS0 : S0 ⊆ e.source := by
    rintro y ⟨z,hz,rfl⟩
    exact e.symm.map_source (hS hz)
  have hn : ∀ r ≤ n, ∀ y ∈ S0, ell^r*‖iteratedFDeriv ℝ r
      (fun w => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) w nu) y‖ ≤ MD*|delta| := by
    intro r hr y hy
    rcases hy with ⟨z,hz,rfl⟩
    exact hnub r hr z hz
  have hm : ∀ r ≤ n, ∀ y ∈ S0, ell^r*‖iteratedFDeriv ℝ r
      (fun w => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) w mu) y‖ ≤ MD*|delta| := by
    intro r hr y hy
    rcases hy with ⟨z,hz,rfl⟩
    exact hmub r hr z hz
  obtain ⟨hHR,hHI,hRsymm,hIsymm,hsR,hsI,hRb,hIb⟩ := hraw phi tau chi P Q nu mu q e.source S0
    e.open_source hS0 ell delta hell hnu hmu hn hm
  obtain ⟨hhr,hhrb⟩ := actual_secondary_inverse_forcing_weighted_jets T hT n Kcut (CR*delta^2)
    hKcut (by positivity) e cutoff HR he hc hHR ell hell S hS hcut
    (fun r hr z hz => hRb r hr _ ⟨z,hz,rfl⟩) hinv
  obtain ⟨hhi,hhib⟩ := actual_secondary_inverse_forcing_weighted_jets T hT n Kcut (CR*delta^2)
    hKcut (by positivity) e cutoff HI he hc hHI ell hell S hS hcut
    (fun r hr z hz => hIb r hr _ ⟨z,hz,rfl⟩) hinv
  refine ⟨hhr,hhi,?_,?_,?_,?_,?_⟩
  · intro z hz i j
    exact actual_secondary_inverse_forcing_symmetric e cutoff HR (fun y _ => hRsymm y) z hz i j
  · intro z hz i j
    exact actual_secondary_inverse_forcing_symmetric e cutoff HI (fun y _ => hIsymm y) z hz i j
  · intro z hz hsupport
    rcases hsupport with hs | hs
    · have h := actual_secondary_inverse_forcing_support e cutoff HR z hz hs
      exact ⟨h.1,hsR h.2⟩
    · have h := actual_secondary_inverse_forcing_support e cutoff HI z hz hs
      exact ⟨h.1,hsI h.2⟩
  · intro r hr z hz
    exact (hhrb r hr z hz).trans_eq (by ring)
  · intro r hr z hz
    exact (hhib r hr z hz).trans_eq (by ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_quadratic_localization_profiles
