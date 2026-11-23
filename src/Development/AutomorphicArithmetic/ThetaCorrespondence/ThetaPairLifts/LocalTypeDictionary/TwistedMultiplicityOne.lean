module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingLevelOperators
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllTraceOfMiddleX
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDSComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPseudoCoefficientExistenceUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonFieldTypeVanishingX
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqXOfGeomExpansionX
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleRepHasTraceFiniteAdelicPureTensorFunctStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleIrreducibleTorusCharacters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffEqZeroOfSumTraceProjectionsInequivalentIrreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestFamiliesProjectedTranslationOperatorsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorTraceEqConstMulLocalTraceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthFilterFinRange

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleIrreducibleTorusCharactersStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.admissible_irreducible_torus_characters : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace → GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate → ∀ (D : D7) (V : HSp D) (U : AuxiliaryPlaceHermitianSpace V) (μ : Measure (Gv V U.u)), μ.IsHaarMeasure → ∀ (n : ℕ) (N : Fin n → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (π : ∀ i, Representation ℂ (Gv V U.u) (N i)), (∀ i, (π i).IsIrreducible) → (∀ i, IsAdmissible (π i)) → ∀ d : Fin n → ℂ, (∀ t ∈ strictTorus V.rank U.ϖ, ∀ b : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace μ (π i) (U.frame.cosetFn t) (b i)) → ∑ i, d i * b i = 0) → ∀ f ∈ CcLoc D.sp.cm.sig V.gram U.u, (∀ k ∈ U.frame.iwahori, ∀ g, f (k * g) = f g) → ∀ b : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace μ (π i) f (b i)) → ∑ i, d i * b i = 0 := by
  first | exact @GlobalTheory.IwahoriRel.relation_of_iwahoriTrace | exact GlobalTheory.IwahoriRel.relation_of_iwahoriTrace | (intros; apply GlobalTheory.IwahoriRel.relation_of_iwahoriTrace <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleAdmissibleLocalComponentFiniteA

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.LocCompFin

open GlobalTheory.CuspRep.LocEx GlobalTheory.AutMult

section Groups

variable {D : D7} (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F))

theorem finLoc_locFin (x : Gv V u) : finLoc V u (locFin V u x) = x :=
  GlobalTheory.AdelicU.proj_emb_self _ _ u x

theorem commute_locFin (x : Gv V u) {g : GfC V} (hg : finLoc V u g = 1) : Commute (locFin V u x) g :=
  Subtype.ext (GlobalTheory.AdelicU.commute_emb _ _ x hg).eq

theorem continuous_locFin : Continuous (locFin V u) :=
  (GlobalTheory.AdelicU.continuous_emb _ _ u).subtype_mk _

theorem continuous_finLoc : Continuous (finLoc V u) :=
  (GlobalTheory.AdelicU.continuous_proj _ _ u).comp continuous_subtype_val

theorem finLoc_inv_mul (g : GfC V) : finLoc V u ((locFin V u (finLoc V u g))⁻¹ * g) = 1 := by
  rw [map_mul, map_inv, finLoc_locFin, inv_mul_cancel]

end Groups

theorem exists_locComp : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (π : Representation ℂ (Gv V u) N),
      π.IsIrreducible ∧ IsAdmissible π ∧ FinHasLocComp V u π σ := by
  intro D V u W _ _ σ hirr hadm
  letI : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  obtain ⟨hnt, hinv⟩ := (GlobalTheory.CuspRep.isIrreducible_iff σ).1 hirr
  obtain ⟨x, hx0⟩ := exists_ne (0 : W)
  have hsplit : ∀ g (y : W), σ g y = σ (locFin V u (finLoc V u g)) (σ ((locFin V u (finLoc V u g))⁻¹ * g) y) :=
    fun g y => by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hcomm : ∀ g : GfC V, finLoc V u g = 1 → ∀ h (y : W),
      σ g (σ (locFin V u h) y) = σ (locFin V u h) (σ g y) := by
    intro g hg h y
    rw [← Module.End.mul_apply, ← map_mul, ← (commute_locFin V u h hg).eq, map_mul, Module.End.mul_apply]
  have hρ : GlobalTheory.PRep.IsSmooth (σ.comp (locFin V u)) := fun v => (hadm.1 v).preimage (continuous_locFin V u)
  let K₀ : Subgroup (GfC V) := stab σ x
  have hK₀ : IsOpen (K₀ : Set (GfC V)) := hadm.1 x
  let Kc : Subgroup (Gv V u) := K₀.comap (locFin V u) ⊓ Kv V u
  have hKco : IsOpen (Kc : Set (Gv V u)) :=
    (hK₀.preimage (continuous_locFin V u)).inter (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ u)
  have hKcc : IsCompact (Kc : Set (Gv V u)) :=
    (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ u).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKco) fun k hk => hk.2
  have hKcK₀ : ∀ k ∈ Kc, locFin V u k ∈ K₀ := fun k hk => hk.1
  have hxKc : x ∈ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) Kc := mem_fix.2 fun k hk => hKcK₀ k hk
  have hnull : nullPart (σ.comp (locFin V u)) Kc = ⊥ := by
    rcases hinv (nullPart (σ.comp (locFin V u)) Kc) (fun g y hy => by
      rw [hsplit g y]
      exact nullPart_act _ Kc (finLoc V u g) (nullPart_comm _ Kc (σ _)
        (fun h z => hcomm _ (finLoc_inv_mul V u g) h z) hy)) with h | h
    · exact h
    · exact absurd (eq_zero_of_mem_nullPart hρ hKcc hxKc (h ▸ Submodule.mem_top)) hx0
  have h2 : ∀ Y : Submodule ℂ W, (∀ g, ∀ v ∈ Y, σ.comp (locFin V u) g v ∈ Y) →
      Y ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) Kc = ⊥ → Y = ⊥ :=
    fun Y hY h => le_bot_iff.1 (hnull ▸ le_nullPart hρ hKcc Y hY h)
  let L' : Subgroup (GfC V) := K₀ ⊓ (finLoc V u).ker
  let U : Submodule ℂ W := GlobalTheory.PRep.fixed σ L'
  have hU : ∀ g, ∀ v ∈ U, σ.comp (locFin V u) g v ∈ U := fun g v hv => mem_fix.2 fun k hk => by
    change σ k (σ (locFin V u g) v) = σ (locFin V u g) v
    rw [hcomm k hk.2 g v, mem_fix.1 hv k hk]
  have hU0 : U ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨x, mem_fix.2 fun k hk => hk.1, hx0⟩
  obtain ⟨C, hCo, hCc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  have hfin : ∀ K' : Subgroup (Gv V u), IsOpen (K' : Set (Gv V u)) →
      FiniteDimensional ℂ ↥(U ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) K') := by
    intro K' hK'
    let M : Subgroup (GfC V) := (K₀ ⊓ (Kc ⊓ K').comap (finLoc V u)) ⊓ C
    have hMo : IsOpen (M : Set (GfC V)) :=
      (hK₀.inter ((hKco.inter hK').preimage (continuous_finLoc V u))).inter hCo
    have hMc : IsCompact (M : Set (GfC V)) :=
      hCc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hMo) fun k hk => hk.2
    have := hadm.2 M hMo hMc
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.PRep.fixed σ M) fun v hv => mem_fix.2 fun k hk => ?_
    have hk1 : (locFin V u (finLoc V u k))⁻¹ * k ∈ L' :=
      ⟨K₀.mul_mem (K₀.inv_mem (hKcK₀ _ hk.1.2.1)) hk.1.1, finLoc_inv_mul V u k⟩
    rw [hsplit k v, mem_fix.1 hv.1 _ hk1]
    exact mem_fix.1 hv.2 _ hk.1.2.2
  obtain ⟨π, ⟨f, hf0, hf⟩, hπ⟩ := exists_irred hρ hKco h2 U hU hU0 hfin
  refine ⟨π.V, inferInstance, inferInstance, π.ρ, π.irred, hπ, ?_⟩
  let F : π.ρ.IntertwiningMap (σ.comp (locFin V u)) :=
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext (hf g) }
  have hI : ∀ g, ∀ y ∈ isoPartAlg π.ρ (σ.comp (locFin V u)), σ g y ∈ isoPartAlg π.ρ (σ.comp (locFin V u)) := by
    intro g y hy
    refine Submodule.iSup_induction _ (motive := fun y => σ g y ∈ isoPartAlg π.ρ (σ.comp (locFin V u))) hy ?_ ?_ ?_
    · rintro T _ ⟨z, rfl⟩
      let T' : π.ρ.IntertwiningMap (σ.comp (locFin V u)) :=
        { toLinearMap := σ ((locFin V u (finLoc V u g))⁻¹ * g) ∘ₗ T.toLinearMap
          isIntertwining' := fun h => LinearMap.ext fun w => by
            change σ _ (T (π.ρ h w)) = σ (locFin V u h) (σ _ (T w))
            rw [T.isIntertwining]
            exact hcomm _ (finLoc_inv_mul V u g) h _ }
      refine Submodule.mem_iSup_of_mem T' ⟨π.ρ (finLoc V u g) z, ?_⟩
      change T' (π.ρ (finLoc V u g) z) = σ g (T z)
      rw [T'.isIntertwining, hsplit g (T z)]
      rfl
    · simp only [map_zero]; exact zero_mem _
    · intro a b ha hb; simp only [map_add (f := _)]; exact add_mem ha hb
  rcases hinv _ hI with h | h
  · refine absurd ?_ hf0
    have hr : LinearMap.range F.toLinearMap ≤ ⊥ :=
      h ▸ le_iSup (fun T : π.ρ.IntertwiningMap (σ.comp (locFin V u)) => LinearMap.range T.toLinearMap) F
    exact LinearMap.range_eq_bot.1 (le_bot_iff.1 hr)
  · exact h

end GlobalTheory.LocCompFin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleAdmissibleLocalComponentFiniteAStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.exists_irreducible_admissible_localComponent_finiteAdelic : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (π : Representation ℂ (Gv V u) N), π.IsIrreducible ∧ IsAdmissible π ∧ FinHasLocComp V u π σ := by
  first | exact @GlobalTheory.LocCompFin.exists_locComp | exact GlobalTheory.LocCompFin.exists_locComp | (intros; apply GlobalTheory.LocCompFin.exists_locComp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSeparationOfIwahoriTrace

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical

noncomputable section

namespace GlobalTheory.TrMultSep

theorem separation_of_iwahoriTrace (hI : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace) (hE : GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate) :
    Separation := by
  intro D V T U hU μf hμ hK ν hν n Ws _ _ σs hσ a hyp
  haveI : ν.IsHaarMeasure := hν.1
  obtain ⟨e, he, hP, hfam⟩ := GlobalTheory.T.exists_testFamilies_projectedTranslationOperators D V T U hU μf hμ hK ν hν
  have hex : ∀ i, ∃ P : Ws i →ₗ[ℂ] Ws i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν (σs i) (finFn V e) P ∧
      FiniteDimensional ℂ (LinearMap.range P) := by
    intro i
    obtain ⟨c, A, hA, hAf⟩ := (GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V ν e he (Ws i) (σs i) (hσ.2.1 i)).1
    exact ⟨A, hA, hAf.1⟩
  choose P hPint using hex
  have hidem : ∀ i, P i ∘ₗ P i = P i := fun i => (hP (Ws i) (σs i) (hσ.2.1 i).1 (P i) (hPint i).1).1
  have hne : ∀ i, HasTypeVec T (σs i) → P i ≠ 0 := fun i h => (hP (Ws i) (σs i) (hσ.2.1 i).1 (P i) (hPint i).1).2 h
  intro i hi
  refine GlobalTheory.T.coeff_eq_zero_of_sum_trace_projections_inequivalent_irreps (GfC V) n Ws σs hσ.1 hσ.2.2 P hidem (fun i => (hPint i).2) a ?_ i (hne i hi)
  intro g c hc
  obtain ⟨ff, hff, hffI, hffT, hffOp⟩ := hfam g
  have htr : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i) := fun i =>
    ⟨_, hffOp (Ws i) (σs i) (hσ.2.1 i).1 (P i) (hPint i).1, hc i⟩
  have hloc := fun i => GlobalTheory.T.exists_irreducible_admissible_localComponent_finiteAdelic D V U.u (Ws i) (σs i) (hσ.1 i) (hσ.2.1 i)
  choose N instA instM π hπ using hloc
  letI : ∀ i, AddCommGroup (N i) := instA
  letI : ∀ i, Module ℂ (N i) := instM
  have hfac := fun i => GlobalTheory.T.pure_tensor_trace_eq_const_mul_local_trace D V U.u μf hμ hK ν hν (Ws i) (σs i) (hσ.2.1 i) (N i) (π i) (hπ i).1
    (hπ i).2.1 (hπ i).2.2 ff hff
  choose c' hc' using hfac
  have hd : ∀ t ∈ strictTorus V.rank U.ϖ, ∀ b : Fin n → ℂ,
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf U.u) (π i) (U.frame.cosetFn t) (b i)) →
      ∑ i, (a i * c' i) * b i = 0 := by
    intro t ht b hb
    have h := hyp (Function.update ff U.u (U.frame.cosetFn t)) (hffT t ht).1 (hffT t ht).2 (fun i => c' i * b i)
      (fun i => (hc' i _ (U.frame.cosetFn_mem t)).2 (b i) (hb i))
    simpa [mul_assoc] using h
  have hb := fun i => (hc' i (ff U.u) (hff.1 U.u)).1
  choose b hb using hb
  have key := GlobalTheory.T.admissible_irreducible_torus_characters hI hE D V U (μf U.u) (hμ U.u) n N π (fun i => (hπ i).1) (fun i => (hπ i).2.1)
    (fun i => a i * c' i) hd (ff U.u) (hff.1 U.u) hffI b hb
  have hceq : ∀ i, c i = c' i * b i := by
    intro i
    have h := (hc' i (ff U.u) (hff.1 U.u)).2 (b i) (hb i)
    rw [Function.update_eq_self] at h
    exact (htr i).unique h
  simp_rw [hceq, ← mul_assoc]
  exact key

end GlobalTheory.TrMultSep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSeparationOfIwahoriTraceStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trace_separation_of_iwahori_trace : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace → GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate → Separation := by
  first | exact @GlobalTheory.TrMultSep.separation_of_iwahoriTrace | exact GlobalTheory.TrMultSep.separation_of_iwahoriTrace | (intros; apply GlobalTheory.TrMultSep.separation_of_iwahoriTrace <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.UnitaryThetaCorrespondenceOfHyp

section

@[expose] public section

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem UpperTheory.Lit.I5.unitary_theory_of_harishChandra_langlands_alt : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.CuspMult.MultEq R := by
  intro _ ds rd hf tc dm _ ze gl gc D G _ _ Pl0 T A Ks _ _ _ R F hG
  exact GlobalTheory.PsCo.Pc.multEq_of_sides GlobalTheory.T.localPseudoCoefficientExistence_unitaryGroup rd hf dm gc (GlobalTheory.PsCo.SpecX.main ds tc)
    (GlobalTheory.T.trace_separation_of_iwahori_trace GlobalTheory.IwahoriTraceProof.iwahoriTrace (GlobalTheory.SmGL.Exponents.exponentsSeparate gl ze))
    (GlobalTheory.PsCo.Plug.ellipticSideDirect tc) GlobalTheory.PsCo.Plug.ellipticT R F hG
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMultiplicityOne

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
namespace GlobalTheory.MultEqFinal
theorem twisted_multiplicity_eq : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → GlobalTheory.CuspMult.MultEq R.toRealDat := by
  intro a1 a2 a3 a4 a5 a6 a7 a12 a13 a14 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s h1 h2 h3 h4 h5 h6 h7 h8
  exact _root_.UpperTheory.Lit.I5.unitary_theory_of_harishChandra_langlands_alt a1 a2 a3 a4 a5 a6 a7 a12 a13 a14 R.toRealDat F.lv2
    (GlobalTheory.GivenOfTop.given_of_top R F h1 h2 h3 h4 h5 h6 h7 h8)
end GlobalTheory.MultEqFinal
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.twisted_multiplicity_one : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → GlobalTheory.CuspMult.MultEq R.toRealDat := by
  first | exact @_root_.GlobalTheory.MultEqFinal.twisted_multiplicity_eq | exact _root_.GlobalTheory.MultEqFinal.twisted_multiplicity_eq | (intros; apply _root_.GlobalTheory.MultEqFinal.twisted_multiplicity_eq <;> assumption)
end
end
end
