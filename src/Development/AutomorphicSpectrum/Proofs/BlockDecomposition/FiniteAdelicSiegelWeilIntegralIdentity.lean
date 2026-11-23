module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicIntegralInvariantOpenSubgroupStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLocalOrbitalIntegralBoundedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScaledIntegralHermitianInOpenSubgroupStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableDenominatorPowerOfLtStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.LocallyConstant.Basic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummablePeriodicBoundByDenominatorStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFiniteAdelesDenseRational

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

theorem sig_sig_of_isCM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (t : R ⊗[F] E) :
    sigR R σ (sigR R σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sigR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (h : F) (t : R ⊗[F] E) :
    sigR R σ (h • t) = h • sigR R σ t :=
  map_smul (Algebra.TensorProduct.map (AlgHom.id F R) σ) h t

theorem inclR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (h : F) (e : E) : inclR (F := F) R (h • e) = h • inclR (F := F) R e :=
  map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) h e

theorem sigR_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem denseRange_inclR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] (hd : DenseRange (algebraMap F R)) :
    DenseRange (inclR R : E →+* R ⊗[F] E) := by
  haveI : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  have hφ := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R).2.2.2.2.2.2.1 _ b
  let φ := hφ.homeomorph
  have hpi : DenseRange (Pi.map fun _ : Fin (Module.finrank F E) => (algebraMap F R)) :=
    DenseRange.piMap fun _ => hd
  have hc : DenseRange (φ.symm ∘ Pi.map fun _ : Fin (Module.finrank F E) => (algebraMap F R)) :=
    φ.symm.surjective.denseRange.comp hpi φ.symm.continuous
  refine hc.mono ?_
  rintro _ ⟨a, rfl⟩
  refine ⟨b.equivFun.symm a, ?_⟩
  apply φ.injective
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  funext k
  show (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] (b.equivFun.symm a)) k = _
  simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.single_apply, apply_ite]

theorem hermE_dense_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ g : HermR (Af F) σ n, ∃ c : hermE σ n, g - hermIn (Af F) σ n c ∈ U := by
  intro F E _ _ _ _ _ σ hCM n U hU g
  obtain ⟨hlc, hsc, ht2, -, -, hden, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨hTR, -, -, -, hsig, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)
  have hincl := denseRange_inclR F E σ hCM (Af F) hden
  have hσ := sig_sig_of_isCM σ hCM

  have hmat : DenseRange (fun c : Matrix (Fin n) (Fin n) E => c.map (inclR (Af F))) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hincl))

  let h : F := 1 / 2
  let Pm : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
    fun m a b => h • (m a b + sigR (Af F) σ (m b a))
  have hPm : ∀ m, Pm m ∈ HermR (Af F) σ n := by
    intro m a b
    show sigR (Af F) σ (h • (m b a + sigR (Af F) σ (m a b))) = h • (m a b + sigR (Af F) σ (m b a))
    rw [sigR_smul, map_add (f := _), sigR_sigR _ _ hσ, add_comm]
  have hsmul : Continuous fun x : Af F ⊗[F] E => h • x := by
    simp_rw [Algebra.smul_def]
    exact continuous_const.mul continuous_id
  have hPc : Continuous Pm := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    exact hsmul.comp ((continuous_id.matrix_elem a b).add
      (hsig.comp (continuous_id.matrix_elem b a)))
  let P : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → HermR (Af F) σ n := fun m => ⟨Pm m, hPm m⟩
  have hP : Continuous P := hPc.subtype_mk hPm
  have hW : IsOpen {m | g - P m ∈ U} :=
    hU.preimage (continuous_const.sub hP)
  have hg : P g.1 = g := by
    apply Subtype.ext
    ext a b
    show h • (g.1 a b + sigR (Af F) σ (g.1 b a)) = g.1 a b
    rw [g.2 a b, ← two_smul F, smul_smul]
    norm_num [h]
  have hne : ({m | g - P m ∈ U} : Set _).Nonempty := ⟨g.1, by simp [hg, U.zero_mem]⟩
  obtain ⟨c₀, hc₀⟩ := hmat.exists_mem_open hW hne
  let c : Matrix (Fin n) (Fin n) E := fun a b => h • (c₀ a b + σ (c₀ b a))
  have hc : c ∈ hermE σ n := by
    intro a b
    show σ (h • (c₀ b a + σ (c₀ a b))) = h • (c₀ a b + σ (c₀ b a))
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def, map_add (f := _), hσ, add_comm]
  refine ⟨⟨c, hc⟩, ?_⟩
  have hcP : hermIn (Af F) σ n ⟨c, hc⟩ = P (c₀.map (inclR (Af F))) := by
    apply Subtype.ext
    ext a b
    show inclR (Af F) (h • (c₀ a b + σ (c₀ b a))) =
      h • (inclR (Af F) (c₀ a b) + sigR (Af F) σ (inclR (Af F) (c₀ b a)))
    rw [inclR_smul, map_add (f := _), sigR_inclR]
  rw [hcP]
  exact hc₀

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFiniteAdelesDenseRationalStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField


theorem _root_.GlobalTheory.T.hermitian_finite_adeles_dense_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ g : HermR (Af F) σ n, ∃ c : hermE σ n, g - hermIn (Af F) σ n c ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOverLatticeQuotientLocallyConstant

section

@[expose] public section

open MeasureTheory Set

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

theorem integrable_of_summable_quotient_periodic :
    ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] (ν : Measure G) [ν.IsAddHaarMeasure] (U : AddSubgroup G),
    IsOpen (U : Set G) → IsCompact (U : Set G) → ∀ ι : H →+ G, (∀ g, ∃ h, g - ι h ∈ U) →
    ∀ f : G → ℂ, (∀ g, ∀ u ∈ U, f (g + u) = f g) →
    Summable (fun x : H ⧸ U.comap ι => ‖f (ι (Quotient.out x))‖) → Integrable f ν := by
  intro G H _ _ _ _ _ _ _ ν _ U hUo hUc ι hι f hf hs
  let r : H ⧸ U.comap ι → G := fun x => ι (Quotient.out x)
  let c : H ⧸ U.comap ι → Set G := fun x => (fun g => g - r x) ⁻¹' (U : Set G)
  have hcopen : ∀ x, IsOpen (c x) := fun x => hUo.preimage (by fun_prop)
  have hcov : ⋃ x, c x = univ := by
    refine eq_univ_of_forall fun g => mem_iUnion.2 ?_
    obtain ⟨h, hh⟩ := hι g
    refine ⟨(QuotientAddGroup.mk h : H ⧸ U.comap ι), ?_⟩
    have h1 : -h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι) ∈ U.comap ι :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
    have h2 : ι (-h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι)) ∈ U := h1
    have h3 := U.sub_mem hh h2
    have h4 : g - ι h - ι (-h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι))
        = g - r (QuotientAddGroup.mk h : H ⧸ U.comap ι) := by
      simp only [r, map_add (f := _), map_neg]; abel
    change g - r _ ∈ U
    rwa [h4] at h3
  have hdisj : Pairwise (Function.onFun Disjoint c) := by
    intro x y hxy
    refine Set.disjoint_left.2 fun g hgx hgy => hxy ?_
    have hgx' : g - r x ∈ U := hgx
    have hgy' : g - r y ∈ U := hgy
    have h1 : ι (-Quotient.out x + Quotient.out y) ∈ U := by
      have h3 := U.sub_mem hgx' hgy'
      have h4 : g - r x - (g - r y) = ι (-Quotient.out x + Quotient.out y) := by
        simp only [r, map_add (f := _), map_neg]; abel
      rwa [h4] at h3
    have h2 : (QuotientAddGroup.mk (Quotient.out x) : H ⧸ U.comap ι) = QuotientAddGroup.mk (Quotient.out y) :=
      QuotientAddGroup.eq.2 h1
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h2
  have hne : ∀ x, (c x).Nonempty := fun x => ⟨r x, by
    change r x - r x ∈ U
    simp⟩
  have hcount : Countable (H ⧸ U.comap ι) := by
    have hinj : Function.Injective c := by
      intro x y hxy
      by_contra hne'
      obtain ⟨g, hg⟩ := hne x
      exact Set.disjoint_left.1 (hdisj hne') hg (hxy ▸ hg)
    have hpd : (range c).PairwiseDisjoint id := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
      exact hdisj (fun h => hxy (by rw [h]))
    have := hpd.countable_of_isOpen (by rintro _ ⟨x, rfl⟩; exact hcopen x)
      (by rintro _ ⟨x, rfl⟩; exact hne x)
    have := this.to_subtype
    exact Function.Injective.countable (f := Set.rangeFactorization c)
      (fun x y h => hinj (congrArg Subtype.val h))
  have hconst : ∀ x, ∀ g ∈ c x, f g = f (r x) := by
    intro x g hg
    have := hf (r x) (g - r x) hg
    rw [← this]; congr 1; abel
  have hcont : Continuous f := by
    refine IsLocallyConstant.continuous ?_
    refine (IsLocallyConstant.iff_exists_open f).2 fun g => ?_
    refine ⟨(fun y => y - g) ⁻¹' (U : Set G), hUo.preimage (by fun_prop), by simp, ?_⟩
    intro y hy
    have := hf g (y - g) hy
    rw [← this]; congr 1; abel
  have hmeas : ∀ x, ν (c x) = ν (U : Set G) := by
    intro x
    have : c x = (fun g => g + (- r x)) ⁻¹' (U : Set G) := by
      ext g; simp [c, sub_eq_add_neg]
    rw [this, measure_preimage_add_right]
  have hUfin : ν (U : Set G) < ⊤ := hUc.measure_lt_top
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hsum : ∑' x, ‖f (r x)‖ₑ < ⊤ := by
    have h1 : ∑' x, ‖f (r x)‖ₑ = ∑' x, ENNReal.ofReal ‖f (r x)‖ := by
      simp [ofReal_norm_eq_enorm]
    rw [h1]
    exact hs.tsum_ofReal_lt_top
  have hint : ∫⁻ g, ‖f g‖ₑ ∂ν = (∑' x, ‖f (r x)‖ₑ) * ν (U : Set G) := by
    calc ∫⁻ g, ‖f g‖ₑ ∂ν = ∫⁻ g in ⋃ x, c x, ‖f g‖ₑ ∂ν := by rw [hcov, Measure.restrict_univ]
      _ = ∑' x, ∫⁻ g in c x, ‖f g‖ₑ ∂ν :=
          lintegral_iUnion (fun x => (hcopen x).measurableSet) hdisj _
      _ = ∑' x, ‖f (r x)‖ₑ * ν (U : Set G) := by
          refine tsum_congr fun x => ?_
          rw [setLIntegral_congr_fun (hcopen x).measurableSet
            (g := fun _ => ‖f (r x)‖ₑ) (fun g hg => by simp only [hconst x g hg]),
            setLIntegral_const, hmeas]
      _ = (∑' x, ‖f (r x)‖ₑ) * ν (U : Set G) := ENNReal.tsum_mul_right
  change ∫⁻ g, ‖f g‖ₑ ∂ν < ⊤
  rw [hint]
  exact ENNReal.mul_lt_top hsum hUfin

end GlobalTheory.CompanionTheory.SiegelND.Integ
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOverLatticeQuotientLocallyConstantStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField


theorem _root_.GlobalTheory.T.summable_over_lattice_quotient_locally_constant : ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] (ν : Measure G) [ν.IsAddHaarMeasure] (U : AddSubgroup G),
    IsOpen (U : Set G) → IsCompact (U : Set G) → ∀ ι : H →+ G, (∀ g, ∃ h, g - ι h ∈ U) →
    ∀ f : G → ℂ, (∀ g, ∀ u ∈ U, f (g + u) = f g) →
    Summable (fun x : H ⧸ U.comap ι => ‖f (ι (Quotient.out x))‖) → Integrable f ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic | exact GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicSiegelWeilIntegralIdentity

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

theorem integrable_starLoc_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Af F) σ n), ν.IsAddHaarMeasure →
  ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    Integrable (starLoc (Af F) σ J (psiFin F ψ) μ Q) ν := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ μ hμ ν hν Q hQ
  obtain ⟨hLC, hSC, hT2, -, -, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTR, -, hSC2, -, -, -, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)
  haveI := hTR
  haveI := hSC2
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Af F ⊗[F] E))
  haveI : SecondCountableTopology (HermR (Af F) σ n) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace (HermR (Af F) σ n) := inferInstance
  obtain ⟨U, hUo, hUc, hUp⟩ := GlobalTheory.T.finite_adelic_integral_invariant_open_subgroup F E σ hCM M J n ψ hψ μ hμ Q hQ
  obtain ⟨C, t, ht, hb⟩ := GlobalTheory.T.finite_local_orbital_integral_bounded F E σ hCM M J hJ n ψ hψ μ hμ Q hQ
  obtain ⟨τ, hτ, hc⟩ := GlobalTheory.T.scaled_integral_hermitian_in_open_subgroup F E σ hCM n U hUo t ht
  have hs : (n : ℝ) < (M : ℝ) / 2 := by
    have : ((2 * n : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast hn
    push_cast at this
    linarith
  have hsum := GlobalTheory.T.summable_periodic_bound_by_denominator F E σ n (U.comap (hermIn (Af F) σ n)) t ht τ hτ hc
    (fun c => ‖starLoc (Af F) σ J (psiFin F ψ) μ Q (hermIn (Af F) σ n c)‖) (fun _ => norm_nonneg _)
    (fun c l hl => by
      show ‖_‖ = ‖_‖
      rw [map_add (f := _), hUp _ _ hl]) C ((M : ℝ) / 2) hb (GlobalTheory.T.summable_denominator_power_of_lt F E σ hCM n _ hs)
  exact GlobalTheory.T.summable_over_lattice_quotient_locally_constant _ _ ν U hUo hUc (hermIn (Af F) σ n) (GlobalTheory.T.hermitian_finite_adeles_dense_rational F E σ hCM n U hUo) _ (fun g u hu => hUp g u hu) hsum

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end
