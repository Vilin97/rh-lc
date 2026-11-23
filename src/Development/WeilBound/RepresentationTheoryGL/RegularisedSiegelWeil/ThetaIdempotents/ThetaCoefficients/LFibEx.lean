module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasuresStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhatStatement
public import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibExA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSetsStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSchwartzOrbitalIntegralStatement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfTR
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianFormulaStatement

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.FinCptOfIntegrable

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace PositivityTheory.Rg.Rsw.L.LatticeFibreBump

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem archBump [IsTotallyReal F] {M n : ℕ} (C : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (hC : IsCompact C) :
    ∃ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ,
      GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ ∧ ∀ Y ∈ C, φ Y = 1 := by
  obtain ⟨k, eK, hK⟩ := PI.VolStabS.exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := PI.VolStabS.exists_coord_pi eK hK (Fin M)
  obtain ⟨N, eV, hV⟩ := PI.VolStabS.exists_coord_pi e1 h1 (Fin n)
  let eA : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ) := { eV.toEquiv with map_add' := hV }
  obtain ⟨ρ, hρ⟩ := (hC.image eV.continuous).isBounded.subset_closedBall 0
  let β : ContDiffBump (0 : Fin N → ℝ) :=
    ⟨max ρ 1, max ρ 1 + 1, lt_max_of_lt_right one_pos, lt_add_one _⟩
  have hs : HasCompactSupport fun z => ((β z : ℝ) : ℂ) := β.hasCompactSupport.comp_left Complex.ofReal_zero
  let f : SchwartzMap (Fin N → ℝ) ℂ := hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)
  refine ⟨fun X => f (eA X), ⟨N, eA, eV.continuous, eV.symm.continuous, f, fun _ => rfl⟩, fun Y hY => ?_⟩
  show ((β (eA Y) : ℝ) : ℂ) = 1
  have hm : eA Y ∈ Metric.closedBall (0 : Fin N → ℝ) β.rIn :=
    Metric.closedBall_subset_closedBall (le_max_left ρ 1) (hρ ⟨Y, hY, rfl⟩)
  rw [β.one_of_mem_closedBall hm, Complex.ofReal_one]

omit [NumberField F] [NumberField E] in
theorem repr_natCast_mul' {d : ℕ} (b : Module.Basis (Fin d) F E) {R : Type} [CommRing R]
    [Algebra F R] (N : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr ((N : R ⊗[F] E) * y) k =
      (N : R) * (Algebra.TensorProduct.basis R b).repr y k := by
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem scaled_cpt_open {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (hN : 0 < N) (hL : IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧
      IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) :
    IsCompact {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} ∧
      IsOpen {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} := by
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  set u : Fv F v ⊗[F] E := algebraMap F _ ((N : F)⁻¹) with hu
  have hNu : (N : Fv F v ⊗[F] E) * u = 1 := by
    rw [hu, ← map_natCast (algebraMap F (Fv F v ⊗[F] E)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]
  have hc : ∀ c : Fv F v ⊗[F] E, Continuous fun Y : Fin n → Fin M → Fv F v ⊗[F] E => fun a i => c * Y a i :=
    fun c => continuous_pi fun a => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have heq : {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} =
      (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => fun a i => u * Y a i) '' latV b v := by
    ext Y
    constructor
    · intro hY
      refine ⟨_, hY, ?_⟩
      funext a i
      show u * ((N : Fv F v ⊗[F] E) * Y a i) = Y a i
      rw [← mul_assoc, mul_comm u, hNu, one_mul]
    · rintro ⟨Z, hZ, rfl⟩
      show (fun a i => (N : Fv F v ⊗[F] E) * (u * Z a i)) ∈ latV b v
      simpa only [← mul_assoc, hNu, one_mul] using hZ
  exact ⟨heq ▸ hL.1.image (hc u), hL.2.preimage (hc _)⟩


omit [NumberField E] in
theorem scaled_eq_lat {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (hN : 0 < N) (hv : (algebraMap F (Af F) ((N : F)⁻¹)) v ∈ v.adicCompletionIntegers F) :
    {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} = latV b v := by
  have hw : algebraMap F (Fv F v) ((N : F)⁻¹) ∈ v.adicCompletionIntegers F := by
    have h : (algebraMap F (Af F) ((N : F)⁻¹)) v = algebraMap F (Fv F v) ((N : F)⁻¹) :=
      (evalV F v).commutes _
    rwa [h] at hv
  have hwN : algebraMap F (Fv F v) ((N : F)⁻¹) * (N : Fv F v) = 1 := by
    rw [← map_natCast (algebraMap F (Fv F v)) N, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]
  have key : ∀ c : Fv F v, (N : Fv F v) * c ∈ v.adicCompletionIntegers F ↔ c ∈ v.adicCompletionIntegers F := by
    intro c
    constructor
    · intro h
      have := mul_mem hw h
      rwa [← mul_assoc, hwN, one_mul] at this
    · exact fun h => mul_mem (natCast_mem _ N) h
  ext Y
  simp only [Set.mem_ofPred_eq, latV, repr_natCast_mul', key]

theorem finCpt_of_integrable (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (n : ℕ) (h2n : 2 * n < M) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hν : ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ,
      GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := F) (E := E) Φ → Integrable Φ ν) :
    IsFiniteMeasureOnCompacts ν := by
  classical
  have : IsTotallyReal F := hCM.1
  refine ⟨fun K hK => ?_⟩
  let b := Module.finBasis F E
  obtain ⟨N, R, hN, -, hsub⟩ := (GlobalTheory.T.adelic_tuple_compact_sets F E σ hCM _ b n M).2 K hK
  obtain ⟨hcInf, -, -, hlat, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hCM _ b n M
  obtain ⟨φ, hφ, hφ1⟩ := archBump (projInf '' K) (hK.image hcInf)
  let A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun v => {Y | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v}
  let y : Af F := algebraMap F (Af F) ((N : F)⁻¹)
  have hfin : {v : HeightOneSpectrum (𝓞 F) | y v ∉ v.adicCompletionIntegers F}.Finite := y.2
  have hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v) := fun v => scaled_cpt_open b v N hN (hlat v)
  have hAl : ∀ v, v ∉ hfin.toFinset → A v = latV b v := fun v hv =>
    scaled_eq_lat b v N hN (not_not.mp fun h => hv (hfin.mem_toFinset.mpr h))
  have hΦ := GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n _ b hfin.toFinset φ A hφ hA hAl
  have hint := hν _ hΦ
  have h1 : K ⊆ {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := by
    intro X hX
    have e1 : GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X = 1 := by
      unfold GlobalTheory.CompanionTheory.SiegelND.Coef.pureN
      rw [hφ1 _ ⟨X, hX, rfl⟩, Set.indicator_of_mem
        (show projFin X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.boxFN A from fun v => (hsub X hX).1 v), one_mul]
    simp [e1]
  calc ν K ≤ ν {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := measure_mono h1
    _ = 1 * ν {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := (one_mul _).symm
    _ ≤ ∫⁻ X, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ ∂ν := mul_meas_ge_le_lintegral₀ hint.1.enorm 1
    _ < ⊤ := hint.2

end PositivityTheory.Rg.Rsw.L.LatticeFibreBump

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibExB

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}

theorem thFin (V : HSp D) (hr : 2 * r < V.rank) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμH : μH.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (T : Matrix (Fin r) (Fin r) D.host.E)
    (hT : ∀ a b, D.sp.cm.sig (T b a) = T a b) (hdet : T.det ≠ 0) :
    IsFiniteMeasureOnCompacts (thM V μH 𝓕 T) :=
  PositivityTheory.Rg.Rsw.L.LatticeFibreBump.finCpt_of_integrable D.sp.cm.sig (GlobalTheory.DefiniteQuotient.cmExt D) V.rank V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V) r hr _ fun Φ hΦ =>
      thInt V hr μH 𝓕 hμH h𝓕 T hT hdet Φ hΦ

end PositivityTheory.Rg.Rsw.L.LFibEx

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibExC

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}


open GlobalTheory.CompanionTheory.SiegelND in
theorem tupOf_act (V : HSp D) (h : GA D V) (X : Fin r → Fin V.rank → AE D) :
    tupOf (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h X) = mm (mt V h) (tupOf X) := by
  ext i a
  rfl


open GlobalTheory.CompanionTheory.SiegelND in
theorem ip_tupOf (V : HSp D) (X : Fin r → Fin V.rank → AE D) :
    ip V (tupOf X) (tupOf X) = HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig V.gram X := by
  ext a b
  exact (GlobalTheory.CompanionTheory.SiegelND.hR_tup V (tupOf X) (tupOf X) a b).symm


open GlobalTheory.CompanionTheory.SiegelND in
def tupE (D : D7) (m r : ℕ) : (Fin r → Fin m → AE D) ≃ᵐ Mx D m r where
  toFun := tupOf
  invFun := tupInv
  left_inv := tupInv_tupOf
  right_inv := tupOf_tupInv
  measurable_toFun := by
    have := borel_tup (D := D) (m := m) (r := r)
    have : BorelSpace (Mx D m r) := ⟨rfl⟩
    exact continuous_tupOf.measurable
  measurable_invFun := by
    have := borel_tup (D := D) (m := m) (r := r)
    have : BorelSpace (Mx D m r) := ⟨rfl⟩
    exact continuous_tupInv.measurable


open GlobalTheory.CompanionTheory.SiegelND in
theorem finE {m : ℕ} (ν : Measure (Fin r → Fin m → AE D)) [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (ν.map (tupE D m r)) := by
  refine ⟨fun K hK => ?_⟩
  rw [MeasurableEquiv.map_apply]
  have hs : (tupE D m r) ⁻¹' K = tupInv '' K := by
    ext X
    exact ⟨fun hX => ⟨tupOf X, hX, rfl⟩, fun ⟨y, hy, hyX⟩ => by subst hyX; exact hy⟩
  rw [hs]
  exact (hK.image continuous_tupInv).measure_lt_top


open GlobalTheory.CompanionTheory.SiegelND in
theorem suppE (V : HSp D) (T : Matrix (Fin r) (Fin r) D.host.E) (ν : Measure (Fin r → Fin V.rank → AE D))
    (h : ν {X | HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig V.gram X = T.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))}ᶜ = 0) :
    ν.map (tupE D V.rank r) {x | ip V x x ≠ rat T} = 0 := by
  rw [MeasurableEquiv.map_apply]
  have hs : (tupE D V.rank r) ⁻¹' {x | ip V x x ≠ rat T} ⊆
      {X | HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig V.gram X = T.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))}ᶜ := by
    intro X hX h0
    apply hX
    change ip V (tupOf X) (tupOf X) = rat T
    rw [ip_tupOf]
    exact h0
  exact measure_mono_null hs h


open GlobalTheory.CompanionTheory.SiegelND in
theorem invE (V : HSp D) (ν : Measure (Fin r → Fin V.rank → AE D)) (h : GA D V)
    (hm : Measurable (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h : (Fin r → Fin V.rank → AE D) → _))
    (hν : ν.map (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h) = ν) :
    (ν.map (tupE D V.rank r)).map (fun x => mm (mt V h) x) = ν.map (tupE D V.rank r) := by
  set e := tupE D V.rank r
  have hg : Measurable fun x : Mx D V.rank r => mm (mt V h) x := by
    have : (fun x : Mx D V.rank r => mm (mt V h) x) =
        e ∘ GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h ∘ e.symm :=
      funext fun x => (tupOf_act V h (tupInv x)).symm
    rw [this]
    exact e.measurable.comp (hm.comp e.symm.measurable)
  have hc : (fun x : Mx D V.rank r => mm (mt V h) x) ∘ e = e ∘ GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h :=
    funext fun X => (tupOf_act V h X).symm
  rw [Measure.map_map hg e.measurable, hc, ← Measure.map_map e.measurable hm, hν]

end PositivityTheory.Rg.Rsw.L.LFibEx

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibEx

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}


open GlobalTheory.CompanionTheory.SiegelND in
theorem _root_.PositivityTheory.Rg.Rsw.L.fibEx : FibEx := by
  intro D r V hr ψ hψ θ hθ μ hμ lam hlam b₀ hb₀
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  obtain ⟨μH, 𝓕, hμH, h𝓕, -⟩ := GlobalTheory.Published.SiegelOneVector.exists_normalised D.sp.cm.sig V.gram hCM hJ
  obtain ⟨dx, db, hdx, hdb, hW⟩ := GlobalTheory.T.exists_self_dual_siegel_weil_measures D r V ψ hψ μ hμ lam hlam
  have hT : ∀ a b, D.sp.cm.sig (b₀.1 b a) = b₀.1 a b := fun a b => by
    have := congrFun (congrFun b₀.2 a) b
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable D.host.F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring _ _ D.sp.cm.sig hCM (AF D.host.F)
  have := hB r V.rank
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact _ _ D.sp.cm.sig hCM V.rank V.gram hJ (AF D.host.F)
  obtain ⟨ac, -, -, -⟩ := hact r
  have hTI := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_inv D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ μH 𝓕 hμH h𝓕 r b₀.1
  have hfin := thFin V hr μH 𝓕 hμH h𝓕 b₀.1 hT hb₀
  refine ⟨(thM V μH 𝓕 b₀.1).map (tupE D V.rank r), finE _, suppE V b₀.1 _ hTI.2,
    fun h => invE V _ h (ac.comp (continuous_const.prodMk continuous_id)).measurable (hTI.1 h), fun φ hφ => ?_⟩
  have hSB := GlobalTheory.T.schwartz_function_schwartz_bruhat D θ hθ V.rank r φ hφ
  have hI := thInt V hr μH 𝓕 hμH h𝓕 b₀.1 hT hb₀ _ hSB
  refine ⟨(tupE D V.rank r).measurableEmbedding.integrable_map_iff.2 hI, ?_⟩
  rw [hW φ b₀, (tupE D V.rank r).measurableEmbedding.integral_map]
  exact GlobalTheory.T.siegel_weil_hermitian_formula D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr ψ hψ dx hdx db hdb μH 𝓕 hμH h𝓕 _ hSB
    b₀.1 hT hb₀

end PositivityTheory.Rg.Rsw.L.LFibEx

end
end
end
