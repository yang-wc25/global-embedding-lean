import NormalPolar.JointSecondaryCoefficients
import NormalPolar.ActualRepairModelFirstDefectCoefficientSupport
import Probes.ActualSecondaryQuadraticConstruction

/-! A genuine joint-parameter mixed secondary piece for the same common primary array.
The complete background and prescribed raw sources produce all coefficients;
the actual negative signed quadratic forcing, both inverse-chart tensor slots,
its support, symmetry and CH*delta^2 bounds are then constructed internally.
No coefficient, forcing or secondary-wave output budget is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M Ep Tr : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N p r : ℕ}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem jointSecondary_mixed_piece_from_raw_uniform
    (nInput nSolve q probeLength Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (hbackgroundOrder : nSolve+2+(q+2) ≤ nInput) (hprobeOrder : nSolve+2+probeLength ≤ nInput)
    (reserve Bnd Mg Kcut Bchi Bnu Ku Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku) (hMphase : 0 ≤ Mphase)
    (weight : Fin r → ℝ) (Tbackground Tprobe Tinv : ℕ → ℝ)
    (hTbackground : ∀ k, 0 ≤ Tbackground k) (hTprobe : ∀ k, 0 ≤ Tprobe k) (hTinv : ∀ k, 0 ≤ Tinv k) :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∀
      (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (label : (Fin r × Bool) ↪ Fin p)
      (c : Fin r → Ep → D → M) (chi : Fin r → X → ℝ)
      (nu : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
      (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (phase : Fin r → Ep × M → ℝ)
      (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (tau ell delta Delta : ℝ) (hdelta : 0 ≤ delta)
      (W : Set (Ep × M)) (K : (Λ ⊕ Fin r) → Set (Ep × M)) (j : ℕ)
      (d : ActualSecondaryRawGeometry F hF nSolve j ell Mg W)
      (e : OpenPartialHomeomorph M D)
      (he : ContMDiffOn IM 𝓘(ℝ,D) ∞ e e.source)
      (heInv : ContMDiffOn 𝓘(ℝ,D) IM ∞ e.symm e.target)
      (hhost : d.chart.source ⊆ ((OpenPartialHomeomorph.refl Ep).prod e).source)
      (l l' : Λ ⊕ Fin r) (branch : Fin 4),
    let host := (OpenPartialHomeomorph.refl Ep).prod e
    let transition := host.symm.trans d.chart
    let vf := fun l => actualProbeNormalAmplitude F (c l) (chi l) (nu l) delta tau (weight l)
    let phases := Sum.elim g.phase phase
    let R := jointSecondaryCombinedAmplitude F hF g label c vf tau delta (q+2) probeLength a input
    let psi := fun z => ![phases l z+phases l' z,phases l z-phases l' z,
      -phases l z+phases l' z,-phases l z-phases l' z] branch
    ∀ (hphase : d.phase = psi) (cutoff : X → ℝ)
      (hcutoff : ContDiffOn ℝ ∞ cutoff transition.source)
      (hInv : ContDiffOn ℝ ∞ transition.symm transition.target)
      (hcutSupport : ∀ y ∈ host.target, host.symm y ∈ W → y ∈ tsupport cutoff →
        host.symm y ∈ K l ∩ K l' → host.symm y ∈ d.support)
      (background : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nInput (q+2) nSolve Rsub Lprimary
        reserve Bnd Mg Tbackground F hF g input inputbar W (fun l => K (Sum.inl l)) e transition.source
        (transition.symm '' d.sample) tau ell Delta)
      (prescribed : ActualPrescribedObservationProfiles F hF c chi nu a W (fun l => K (Sum.inr l))
        nInput (nSolve+1) ell Mg Bchi Bnu (fun z : X => (z.1,e.symm z.2)) transition.source
        (transition.symm '' d.sample) Tprobe phase Mphase)
      (hcut : ∀ k ≤ nSolve, ∀ z ∈ d.sample, ell^k*‖iteratedFDeriv ℝ k cutoff (transition.symm z)‖ ≤ Kcut)
      (hinv : ∀ k, 1 ≤ k → k ≤ nSolve+1 → ∀ z ∈ d.sample,
        ell^(k-1)*‖iteratedFDeriv ℝ k transition.symm z‖ ≤ Tinv k)
      (u : Ep → Fin p → ℝ)
      (hu : ContDiffOn ℝ ∞ (fun z : X => u z.1) transition.source)
      (hub : ∀ k ≤ nSolve, ∀ z ∈ transition.symm '' d.sample,
        ell^k*‖iteratedFDeriv ℝ k (fun y : X => u y.1) z‖ ≤ Ku),
    let H := incrementsSecondaryQuadraticForcing (fun l b x => phases l (b,e.symm x)) tau
      (fun (_ : Λ ⊕ Fin r) (_ : Ep) (_ : Unit) _ => 1)
      (fun l b (_ : Unit) x => R u false l (b,e.symm x))
      (fun l b (_ : Unit) x => R u true l (b,e.symm x))
      (fun i _ => EuclideanSpace.single i 1) l l' branch
    let hR := actualSecondaryInverseForcing transition cutoff (fun z => actualRealTensorAssembly (H z))
    let hI := actualSecondaryInverseForcing transition cutoff (fun z => actualImaginaryTensorAssembly (H z))
    ∃ out : ActualSecondaryPhysicalPieceData F hF nSolve j ell Mg CH delta W,
      out.base.c = d.c ∧ out.base.chart = d.chart ∧ out.base.phase = psi ∧
      out.base.support = d.support ∧ out.base.sample = d.sample ∧
      out.base.hR = hR ∧ out.base.hI = hI ∧
      ∀ tau' length, out.base.wave tau' length =
        actualSecondarySupportedWave F hF d.c hR hI d.chart psi tau' length := by
  obtain ⟨MD,hMD,hcoeff⟩ := jointSecondary_common_coefficients_from_raw_uniform
    (I := IM) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (p := p) (Λ := Λ) (Β := Β)
    nInput q probeLength nSolve Rsub Lprimary hq hbackgroundOrder hprobeOrder
    reserve Bnd Mg Bchi Bnu Ku Mphase hreserve hBnd hMg hBchi hBnu hKu hMphase
    weight Tbackground Tprobe hTbackground hTprobe
  obtain ⟨CH,hCH,hconstruct⟩ := actual_secondary_quadratic_piece_from_geometry
    (m := m) (N := N) (Ep := Ep) (M := M) nSolve MD Kcut hMD hKcut Tinv hTinv
  refine ⟨CH,hCH,?_⟩
  intro F hF g label c chi nu a phase input inputbar tau ell delta Delta hdelta W K j d e he heInv hhost
    l l' branch host transition vf phases R psi hphase cutoff hcutoff hInv hcutSupport background prescribed hcut hinv u hu hub H hR hI
  have hTarget : ∀ z ∈ transition.source, z.2 ∈ e.target := fun z hz => hz.1.2
  have hc := hcoeff F hF g label c chi nu a phase input inputbar tau ell delta Delta hdelta W K e he heInv
    transition.source (transition.symm '' d.sample) background hTarget prescribed u hu hub
  have hamp := jointSecondary_common_amplitude_support F hF g label c chi nu a input W K
    background.prim nInput (nSolve+1) (q+2) probeLength ell Mg Bchi Bnu tau delta weight prescribed.raw u
  let phi := fun l b x => phases l (b,e.symm x)
  let RR := fun l b (_ : Unit) x => R u false l (b,e.symm x)
  let QQ := fun l b (_ : Unit) x => R u true l (b,e.symm x)
  have hSupportActual : ∀ y ∈ host.target, host.symm y ∈ W → y ∈ tsupport cutoff →
      y ∈ tsupport (fun z => incrementsSecondaryPhysicalCoefficient phi tau (fun _ _ (_ : Unit) _ => 1)
        RR QQ (fun i _ => EuclideanSpace.single i 1) z l) ∩
      tsupport (fun z => incrementsSecondaryPhysicalCoefficient phi tau (fun _ _ (_ : Unit) _ => 1)
        RR QQ (fun i _ => EuclideanSpace.single i 1) z l') → host.symm y ∈ d.support := by
    intro y hy hyW hyCut hyPair
    have hcont : ContinuousAt (fun z : X => (z.1,e.symm z.2)) y :=
      continuousAt_fst.prodMk ((e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hy.2)).comp continuousAt_snd)
    apply hcutSupport y hy hyW hyCut
    exact ⟨actualRepairModelFirstDefect_coefficient_support_of_amplitudes phases tau (R u false) (R u true)
        W background.prim.hW K (fun l => hamp false l) (fun l => hamp true l)
        (fun z : X => (z.1,e.symm z.2)) y hcont hyW l hyPair.1,
      actualRepairModelFirstDefect_coefficient_support_of_amplitudes phases tau (R u false) (R u true)
        W background.prim.hW K (fun l => hamp false l) (fun l => hamp true l)
        (fun z : X => (z.1,e.symm z.2)) y hcont hyW l' hyPair.2⟩
  obtain ⟨out,hc0,hchart,hp,hs,hsample,hr,hi,hw⟩ := hconstruct F hF j ell Mg delta W d host hhost
    phi tau (fun _ _ (_ : Unit) _ => 1) RR QQ l l' branch cutoff hcutoff hInv hSupportActual
    (background.htau.trans_le background.htaul) (hc l).1 (hc l').1
    (fun k hk z hz => (hc l).2 k hk (transition.symm z) ⟨z,hz,rfl⟩)
    (fun k hk z hz => (hc l').2 k hk (transition.symm z) ⟨z,hz,rfl⟩) hcut hinv
  refine ⟨out,hc0,hchart,hp.trans hphase,hs,hsample,hr,hi,?_⟩
  intro tau' length
  rw [hw tau' length,hphase]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_mixed_piece_from_raw_uniform

