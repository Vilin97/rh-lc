module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaarLifted
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GamOrdNeZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistKernelDivPeriodIsAlgebraic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistRealProjectionAverageMonomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordIntOfJets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresentaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProductStatement
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeIsIntegralOverStandardLatticeStabilis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistIntegralEqBottomClassSum

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped ComplexOrder
open GlobalTheory.ClassRegroup GlobalTheory.DefiniteClassAvg GlobalTheory.DefiniteClassReal
namespace GlobalTheory.RowTest.BottomClassSum
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}
theorem integral_eq_bottom_classSum : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (v : ℝ) (N : ℕ) (z : Fin N → GA D A') (w : Fin N → ℕ) (κ : Measure (GinfC A')), 0 < v ∧ (∀ l, z l ∈ GfC A') ∧
      (∀ l, 0 < w l) ∧ κ.IsMulLeftInvariant ∧ IsProbabilityMeasure κ ∧
      ∀ (t : T) (P : PolF D WW.rank A'.rank), ∀ h ∈ GfC WW,
        X.I' W.ψ W.θ t P h = (v : ℂ) * ∑ l, ((w l : ℂ))⁻¹ * ∫ g, X.ker' W.ψ W.θ t P h (z l * (g : GA D A')) ∂κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL hX
  have hV : ∀ φ : D.host.E →+* ℂ, (A'.gram.map φ).PosDef := fun φ => by
    rw [hX.std'.1, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A' with sig := fun _ => (A'.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A' : Set (GA D A')) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  haveI : CompactSpace (GinfC A') := isCompact_iff_compactSpace.1 hGc
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A'
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  obtain ⟨K'', hK'', hr⟩ := level_all μ₀ hX
  have hfin0 : Finite (FinCl A' K'') := (finite_finCl_and_gamOrd A' K'' hV hK'').1
  let μ := X.m'
  haveI : μ.IsHaarMeasure := hX.is.meas'.1
  have hfd : IsFundamentalDomain (GQ A') X.fd' μ := hX.is.meas'.2
  let J : Subgroup (GA D A') := K''.comap (Lev.finE A')
  have hJo : IsOpen (J : Set (GA D A')) := hK''.1
  have hJc : IsCompact (J : Set (GA D A')) := by
    refine (hK''.2.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen J hK''.1) ?_
    intro k hk
    exact ⟨finPart A' k, finPart_mem_levA A' hk, realPart A' k, realPart_mem A' k, finPart_mul_realPart A' k⟩
  have hJtop : μ J ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hinfJ : GinfC A' ≤ J := by
    show GinfC A' ≤ K''.comap (Lev.finE A')
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact le_sup_right
  let κ : Measure (GinfC A') := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (GinfC A'))
  haveI hκH : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hκ1 : κ Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC A')))
    simpa using this
  haveI : IsProbabilityMeasure κ := ⟨hκ1⟩
  let e := finEquiv A'
  have he : ∀ γ, e (((finPt A').comp (GQ A').subtype) γ) = Bridge.ratF A' γ := fun γ => e.apply_symm_apply _
  have hJe : ∀ a, e a ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A' K'' ↔ a ∈ K''.comap (finG A') := fun a => Iff.rfl
  have hy := isReps_transfer _ _ e he _ _ hJe _ (isReps_out A' K'')
  let N := Nat.card (FinCl A' K'')
  let eq : FinCl A' K'' ≃ Fin N := Finite.equivFin _
  let y : FinCl A' K'' → Bridge.Gf A' := fun c => e (Quotient.out c)
  let zc : FinCl A' K'' → GA D A' := fun c => ((Quotient.out c : GfC A') : GA D A')
  have hz : ∀ c, (finHom A').rangeRestrict (zc c) = y c := fun c => rfl
  have hu0 : ∀ x : GA D A', ∃! c, ∃ γ ∈ GQ A', ∃ k ∈ J, x = γ * zc c * k :=
    existsUnique_doubleCoset (finHom A').rangeRestrict (GQ A') (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A' K'') y hy zc hz
  let z : Fin N → GA D A' := fun l => zc (eq.symm l)
  have hu : ∀ x : GA D A', ∃! l, ∃ γ ∈ GQ A', ∃ k ∈ J, x = γ * z l * k := fun x =>
    (eq.existsUnique_congr_left (p := fun c => ∃ γ ∈ GQ A', ∃ k ∈ J, x = γ * zc c * k)).1 (hu0 x)
  have hfinΓ : ∀ l, {γ : GQ A' | (z l)⁻¹ * (γ : GA D A') * z l ∈ J}.Finite := fun l =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ A') J hfd hJ0 hJtop (z l)
  have him : ∀ l, {γ : GA D A' | γ ∈ GQ A' ∧ (z l)⁻¹ * γ * z l ∈ J} =
      Subtype.val '' {γ : GQ A' | (z l)⁻¹ * (γ : GA D A') * z l ∈ J} := by
    intro l
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hfin : ∀ l, {γ : GA D A' | γ ∈ GQ A' ∧ (z l)⁻¹ * γ * z l ∈ J}.Finite := fun l =>
    him l ▸ (hfinΓ l).image _
  have hdec : ∀ k ∈ J, ∃ k' ∈ Lev.levA A' K'', ∃ w : GinfC A', k = k' * (GinfC A').subtype w := fun k hk =>
    ⟨finPart A' k, finPart_mem_levA A' hk, ⟨realPart A' k, realPart_mem A' k⟩, (finPart_mul_realPart A' k).symm⟩
  have hcomm : ∀ k ∈ Lev.levA A' K'', ∀ w : GinfC A', k * (GinfC A').subtype w = (GinfC A').subtype w * k :=
    fun k hk w => (Formalism.IndefR.Eqv.Act.comm_inf_fin w.2 (Subgroup.mem_inf.1 hk).1).symm
  have hrt : ∀ w : GinfC A', MeasurePreserving (· * (GinfC A').subtype w) μ μ := fun w =>
    measurePreserving_mul_right_of_mem μ J hJo hJ0 hJtop (hinfJ w.2)
  refine ⟨(μ J).toReal, N, z, fun l => {γ : GA D A' | γ ∈ GQ A' ∧ (z l)⁻¹ * γ * z l ∈ J}.ncard, κ,
    ENNReal.toReal_pos hJ0 hJtop, fun l => (Quotient.out (eq.symm l)).2, fun l => ?_, inferInstance, inferInstance,
    fun t P h _ => ?_⟩
  · exact (Set.ncard_pos (hfin l)).2 ⟨1, (GQ A').one_mem, by simp [J.one_mem]⟩
  · have hcont : Continuous (X.ker' W.ψ W.θ t P h) :=
      continuous_of_level A' K'' hK''.1 _ (fun k hk g => hr t P h k hk g) (ker'_cont hX t P h)
    obtain ⟨-, heq⟩ := integral_eq_sum_avg (GA D A') μ (GQ A') J (Lev.levA A' K'') X.fd' hfd hJo hJtop (GinfC A') κ
      (GinfC A').subtype continuous_subtype_val hrt hdec hcomm (Fin N) z hu hfin (X.ker' W.ψ W.θ t P h) hcont
      (ker'_left hX t P h) (fun k hk g => hr t P h k hk g)
    exact heq
end GlobalTheory.RowTest.BottomClassSum
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.twist_integral_eq_bottom_classSum : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (v : ℝ) (N : ℕ) (z : Fin N → GA D A') (w : Fin N → ℕ) (κ : Measure (GinfC A')), 0 < v ∧ (∀ l, z l ∈ GfC A') ∧
      (∀ l, 0 < w l) ∧ κ.IsMulLeftInvariant ∧ IsProbabilityMeasure κ ∧
      ∀ (t : T) (P : PolF D WW.rank A'.rank), ∀ h ∈ GfC WW,
        X.I' W.ψ W.θ t P h = (v : ℂ) * ∑ l, ((w l : ℂ))⁻¹ * ∫ g, X.ker' W.ψ W.θ t P h (z l * (g : GA D A')) ∂κ := by
  first | exact @_root_.GlobalTheory.RowTest.BottomClassSum.integral_eq_bottom_classSum | exact _root_.GlobalTheory.RowTest.BottomClassSum.integral_eq_bottom_classSum | (intros; apply _root_.GlobalTheory.RowTest.BottomClassSum.integral_eq_bottom_classSum <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomClassSumEqFormula

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
namespace GlobalTheory.BotFormulaI'
theorem bottomClassSum_formula : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ (n : ℕ) (c z : Fin n → ℂ), (∀ l, IsAlgebraic ℚ (c l)) ∧
      (∀ l, ∃ (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (h' : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (U : GlobalTheory.NormSum.Tup D P.a P.d P.n),
        z l = P.coord h' U) ∧
      X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h = Ω * ∑ l, c l * z l := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  obtain ⟨v, N, z, w, κ, hv, hz, hw, hκ1, hκ2, hcls⟩ := _root_.GlobalTheory.T.twist_integral_eq_bottom_classSum hP hI hL hX
  obtain ⟨n, hproj⟩ := _root_.GlobalTheory.T.twist_realProjection_average_monomial hP hI hL hX
  obtain ⟨Ω, hΩ, hdict⟩ := _root_.GlobalTheory.T.twist_kernel_div_period_isAlgebraic hP hI hL hX n
  obtain ⟨δ, hδ⟩ := GlobalTheory.NormSum.exists_crv_top D
  obtain ⟨t0, ht0⟩ := ((hI D).t0Ex ⊤ δ hδ).1
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  refine ⟨(v : ℂ) * Ω, mul_ne_zero hv' hΩ, fun t h hh k => ?_⟩
  choose m r U hr heq using fun l => hproj κ hκ1 hκ2 t (z l) (hz l) h hh k
  set S : ℂ := ∑ l, ((w l : ℂ))⁻¹ * ∑ p, r l p * (X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D (U l p)) h (z l) / Ω) with hSdef
  have hval : X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h = (v : ℂ) * Ω * S := by
    rw [hcls t _ h hh, hSdef]
    simp only [heq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro p _
    field_simp
  have hS : IsAlgebraic ℚ S := by
    rw [← mem_algebraicClosure_iff] at *
    refine sum_mem fun l _ => mul_mem (inv_mem ?_) (sum_mem fun p _ => mul_mem ?_ ?_)
    · rw [mem_algebraicClosure_iff]
      simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) ((w l : ℚ)))
    · rw [mem_algebraicClosure_iff]; exact hr l p
    · rw [mem_algebraicClosure_iff]; exact hdict t (z l) (hz l) h hh (U l p)
  refine ⟨1, fun _ => S, fun _ => 1, fun _ => hS,
    fun _ => ⟨δ, t0, 1, GlobalTheory.NormSum.RankZero.pair0 hδ ht0, 1, fun τ j => j.elim0,
      ((GlobalTheory.NormSum.RankZero.normSumPairRankZeroOfCurve_coord_norm hδ ht0).1 _ _).symm⟩, ?_⟩
  rw [hval]
  simp
end GlobalTheory.BotFormulaI'
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottomClassSum_eq_formula : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ (n : ℕ) (c z : Fin n → ℂ), (∀ l, IsAlgebraic ℚ (c l)) ∧
      (∀ l, ∃ (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (h' : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (U : GlobalTheory.NormSum.Tup D P.a P.d P.n),
        z l = P.coord h' U) ∧
      X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h = Ω * ∑ l, c l * z l := by
  first | exact @_root_.GlobalTheory.BotFormulaI'.bottomClassSum_formula | exact _root_.GlobalTheory.BotFormulaI'.bottomClassSum_formula | (intros; apply _root_.GlobalTheory.BotFormulaI'.bottomClassSum_formula <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumPairCoordinateAlgebraic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.NormSum.CoordAlg

open Classical Formalism.UG Formalism.UG.P Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.IntOver GlobalTheory.NormSum.RepAt GlobalTheory.NormSum.PtsMem

theorem exists_prime_integralOver_gt (D : D7) (N : ℕ) (h : GA D N) (Q : ℕ) :
    ∃ p : ℕ, Q < p ∧ p.Prime ∧ IntegralOver D p h := by
  set g : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((h : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hg
  choose m hm0 hm using fun ij : Fin N × Fin N => denom (F := ℚ) (E := D.host.E) (g ij.1 ij.2)
  set M := ∏ ij, m ij with hMdef
  have hM0 : 0 < M := Finset.prod_pos fun ij _ => hm0 ij
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + Q + 1)
  have hpM' : ¬ p ∣ M := fun hd => by have := Nat.le_of_dvd hM0 hd; omega
  obtain ⟨v, hv, hw⟩ := exists_place p hp
  have hMv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro hm'
    obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM'))).map
      (Int.castRingHom (𝓞 ℚ))
    refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e]
    exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hm')) (Ideal.mul_mem_left _ _ (by simpa using hv))
  have hi : ∀ i j, afsplitEps D.host.E v * g i j ∈ OhE D := fun i j => eps_mul_mem v M hMv _ (by
    rw [hMdef, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_assoc]
    exact mul_mem (natCast_mem _ _) (hm (i, j)))
  obtain ⟨k, hk, hint, htriv⟩ := exists_int (F := ℚ) (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) v
    (h : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) h.2 (Units.inv_eq_of_mul_eq_one_left ((mem_GA D _).1 h.2)) hi
  refine ⟨p, by omega, hp, ⟨k, hk⟩, (mem_intG _).2 hint, fun i j l => ?_⟩
  have := zero_at (F := ℚ) (E := D.host.E) v p hp hw (g i j - (1 : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j) l
  rw [← htriv i j] at this
  exact this

end GlobalTheory.NormSum.CoordAlg
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.NormSumCoefficientsIsAlgebraic

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.NormSum.CoordAlg
open Classical Formalism.UG Formalism.UG.P Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.IntOver GlobalTheory.NormSum.RepAt GlobalTheory.NormSum.PtsMem
theorem normSum_coordinate_isAlgebraic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ (D : D7) (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q)
    (h : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (U : GlobalTheory.NormSum.Tup D P.a P.d P.n), IsAlgebraic ℚ (P.coord h U) := by
  intro _hPr hI D δ t0 Q P h U
  obtain ⟨S, dl, hL⟩ := GlobalTheory.NormSum.Denom.exists_letters D
  obtain ⟨p, hpQ, hp, k', hk', htr⟩ := exists_prime_integralOver_gt D P.d h Q
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ0 := P.level_pos
  have hsp : p ∣ Q → SplitIn D p := fun hd => absurd (Nat.le_of_dvd hQ0 hd) (by omega)
  obtain ⟨hterm, -, -⟩ := GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D (hI D) ⊤ δ t0 Q P.crv P.pt0 P hQ0
  have hmem : P.coord h U ∈ Qbar := by
    unfold Pair.coord
    refine finsum_induction (· ∈ Qbar) (zero_mem _) (fun x y => add_mem) (fun x => ?_)
    refine mul_mem (inv_mem (natCast_mem _ _)) ?_
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := (hI D).rep P.a p hp x.out
    rw [← hterm γ (Subgroup.subset_closure ⟨γ', h1⟩) k (Subgroup.subset_closure h2)]
    exact (CoordBound.term_bound_of_jets GlobalTheory.T.jets_torsion_translates_cm_theta_product D (hI D) S dl hL δ t0 Q P p hsp
      (CoordBound.nonempty_place p).some _ h k' hk' h3 htr U).1
  exact mem_algebraicClosure_iff.1 hmem
end GlobalTheory.NormSum.CoordAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.normSum_coefficients_isAlgebraic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ (D : D7) (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q)
    (h : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (U : GlobalTheory.NormSum.Tup D P.a P.d P.n), IsAlgebraic ℚ (P.coord h U) := by
  first | exact @_root_.GlobalTheory.NormSum.CoordAlg.normSum_coordinate_isAlgebraic | exact _root_.GlobalTheory.NormSum.CoordAlg.normSum_coordinate_isAlgebraic | (intros; apply _root_.GlobalTheory.NormSum.CoordAlg.normSum_coordinate_isAlgebraic <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTwistedClassSumsAlgebraic

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
namespace GlobalTheory.BotAlgI'
theorem twistedClassSums_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  obtain ⟨Ω, hΩ, H⟩ := _root_.GlobalTheory.T.bottomClassSum_eq_formula hP hI hL hX
  refine ⟨Ω, hΩ, fun t h hh k => ?_⟩
  obtain ⟨n, c, z, hc, hz, he⟩ := H t h hh k
  rw [he, mul_div_cancel_left₀ _ hΩ]
  have hz' : ∀ l, IsAlgebraic ℚ (z l) := fun l => by
    obtain ⟨δ, t0, Q, P, h', U, e⟩ := hz l
    rw [e]; exact _root_.GlobalTheory.T.normSum_coefficients_isAlgebraic hP hI D δ t0 Q P h' U
  have : ∀ l, (c l * z l) ∈ algebraicClosure ℚ ℂ := fun l =>
    mul_mem (mem_algebraicClosure_iff.2 (hc l)) (mem_algebraicClosure_iff.2 (hz' l))
  exact mem_algebraicClosure_iff.1 (sum_mem fun l _ => this l)
end GlobalTheory.BotAlgI'
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottom_twistedClassSums_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  first | exact @_root_.GlobalTheory.BotAlgI'.twistedClassSums_isAlgebraic | exact _root_.GlobalTheory.BotAlgI'.twistedClassSums_isAlgebraic | (intros; apply _root_.GlobalTheory.BotAlgI'.twistedClassSums_isAlgebraic <;> assumption)
end
end
end
