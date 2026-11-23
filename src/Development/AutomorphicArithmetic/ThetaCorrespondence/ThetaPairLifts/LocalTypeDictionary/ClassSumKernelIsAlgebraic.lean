module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaar
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
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JetsDivPeriodIsAlgebraic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedTranslateEqAlgebraicCombination
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedRealAverageKernelIsAlgebraic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomClassSumIntegralNeg

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
open GlobalTheory.Grid (neg sgn ofSgn)
namespace GlobalTheory.RowTest.BottomClassSumNeg
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}
end GlobalTheory.RowTest.BottomClassSumNeg
namespace GlobalTheory.RowTest.BottomClassSumNeg
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}
theorem integral_eq_bottom_classSum : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (v : ℝ) (N : ℕ) (z : Fin N → GA D A) (w : Fin N → ℕ) (κ : Measure (GinfC A)), 0 < v ∧ (∀ l, z l ∈ GfC A) ∧
      (∀ l, 0 < w l) ∧ κ.IsMulLeftInvariant ∧ IsProbabilityMeasure κ ∧
      ∀ (t : T) (P : PolF D WW.rank A.rank), ∀ h ∈ GfC WW,
        X.I W.ψ W.θ t P h = (v : ℂ) * ∑ l, ((w l : ℂ))⁻¹ * ∫ g, X.ker W.ψ W.θ t P h (z l * (g : GA D A)) ∂κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL hX
  have hV : ∀ φ : D.host.E →+* ℂ, (A.gram.map φ).PosDef := fun φ => by
    rw [hX.std.1, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A with sig := fun _ => (A.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A : Set (GA D A)) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  haveI : CompactSpace (GinfC A) := isCompact_iff_compactSpace.1 hGc
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  obtain ⟨K'', hK'', hr⟩ := level_all μ₀ hX
  have hfin0 : Finite (FinCl A K'') := (finite_finCl_and_gamOrd A K'' hV hK'').1
  let μ := X.m
  haveI : μ.IsHaarMeasure := hX.is.meas.1
  have hfd : IsFundamentalDomain (GQ A) X.fd μ := hX.is.meas.2
  let J : Subgroup (GA D A) := K''.comap (Lev.finE A)
  have hJo : IsOpen (J : Set (GA D A)) := hK''.1
  have hJc : IsCompact (J : Set (GA D A)) := by
    refine (hK''.2.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen J hK''.1) ?_
    intro k hk
    exact ⟨finPart A k, finPart_mem_levA A hk, realPart A k, realPart_mem A k, finPart_mul_realPart A k⟩
  have hJtop : μ J ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hinfJ : GinfC A ≤ J := by
    show GinfC A ≤ K''.comap (Lev.finE A)
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact le_sup_right
  let κ : Measure (GinfC A) := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (GinfC A))
  haveI hκH : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hκ1 : κ Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC A)))
    simpa using this
  haveI : IsProbabilityMeasure κ := ⟨hκ1⟩
  let e := finEquiv A
  have he : ∀ γ, e (((finPt A).comp (GQ A).subtype) γ) = Bridge.ratF A γ := fun γ => e.apply_symm_apply _
  have hJe : ∀ a, e a ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A K'' ↔ a ∈ K''.comap (finG A) := fun a => Iff.rfl
  have hy := isReps_transfer _ _ e he _ _ hJe _ (isReps_out A K'')
  let N := Nat.card (FinCl A K'')
  let eq : FinCl A K'' ≃ Fin N := Finite.equivFin _
  let y : FinCl A K'' → Bridge.Gf A := fun c => e (Quotient.out c)
  let zc : FinCl A K'' → GA D A := fun c => ((Quotient.out c : GfC A) : GA D A)
  have hz : ∀ c, (finHom A).rangeRestrict (zc c) = y c := fun c => rfl
  have hu0 : ∀ x : GA D A, ∃! c, ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * zc c * k :=
    existsUnique_doubleCoset (finHom A).rangeRestrict (GQ A) (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A K'') y hy zc hz
  let z : Fin N → GA D A := fun l => zc (eq.symm l)
  have hu : ∀ x : GA D A, ∃! l, ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * z l * k := fun x =>
    (eq.existsUnique_congr_left (p := fun c => ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * zc c * k)).1 (hu0 x)
  have hfinΓ : ∀ l, {γ : GQ A | (z l)⁻¹ * (γ : GA D A) * z l ∈ J}.Finite := fun l =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ A) J hfd hJ0 hJtop (z l)
  have him : ∀ l, {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J} =
      Subtype.val '' {γ : GQ A | (z l)⁻¹ * (γ : GA D A) * z l ∈ J} := by
    intro l
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hfin : ∀ l, {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.Finite := fun l =>
    him l ▸ (hfinΓ l).image _
  have hdec : ∀ k ∈ J, ∃ k' ∈ Lev.levA A K'', ∃ w : GinfC A, k = k' * (GinfC A).subtype w := fun k hk =>
    ⟨finPart A k, finPart_mem_levA A hk, ⟨realPart A k, realPart_mem A k⟩, (finPart_mul_realPart A k).symm⟩
  have hcomm : ∀ k ∈ Lev.levA A K'', ∀ w : GinfC A, k * (GinfC A).subtype w = (GinfC A).subtype w * k :=
    fun k hk w => (Formalism.IndefR.Eqv.Act.comm_inf_fin w.2 (Subgroup.mem_inf.1 hk).1).symm
  have hrt : ∀ w : GinfC A, MeasurePreserving (· * (GinfC A).subtype w) μ μ := fun w =>
    measurePreserving_mul_right_of_mem μ J hJo hJ0 hJtop (hinfJ w.2)
  refine ⟨(μ J).toReal, N, z, fun l => {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.ncard, κ,
    ENNReal.toReal_pos hJ0 hJtop, fun l => (Quotient.out (eq.symm l)).2, fun l => ?_, inferInstance, inferInstance,
    fun t P h _ => ?_⟩
  · exact (Set.ncard_pos (hfin l)).2 ⟨1, (GQ A).one_mem, by simp [J.one_mem]⟩
  · have hcont : Continuous (X.ker W.ψ W.θ t P h) :=
      continuous_of_level A K'' hK''.1 _ (fun k hk g => hr t P h k hk g) (ker_cont hX t P h)
    obtain ⟨-, heq⟩ := integral_eq_sum_avg (GA D A) μ (GQ A) J (Lev.levA A K'') X.fd hfd hJo hJtop (GinfC A) κ
      (GinfC A).subtype continuous_subtype_val hrt hdec hcomm (Fin N) z hu hfin (X.ker W.ψ W.θ t P h) hcont
      (ker_left hX t P h) (fun k hk g => hr t P h k hk g)
    exact heq
end GlobalTheory.RowTest.BottomClassSumNeg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottom_class_sum_integral_neg : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (v : ℝ) (N : ℕ) (z : Fin N → GA D A) (w : Fin N → ℕ) (κ : Measure (GinfC A)), 0 < v ∧ (∀ l, z l ∈ GfC A) ∧
      (∀ l, 0 < w l) ∧ κ.IsMulLeftInvariant ∧ IsProbabilityMeasure κ ∧
      ∀ (t : T) (P : PolF D WW.rank A.rank), ∀ h ∈ GfC WW,
        X.I W.ψ W.θ t P h = (v : ℂ) * ∑ l, ((w l : ℂ))⁻¹ * ∫ g, X.ker W.ψ W.θ t P h (z l * (g : GA D A)) ∂κ := by
  first | exact @_root_.GlobalTheory.RowTest.BottomClassSumNeg.integral_eq_bottom_classSum | exact _root_.GlobalTheory.RowTest.BottomClassSumNeg.integral_eq_bottom_classSum | (intros; apply _root_.GlobalTheory.RowTest.BottomClassSumNeg.integral_eq_bottom_classSum <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFourierCoeffHeisenbergExpansion

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
namespace GlobalTheory.AlgWave
open GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
end GlobalTheory.AlgWave
namespace GlobalTheory.AlgWave
open GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
end GlobalTheory.AlgWave
namespace GlobalTheory.BotFourier
open GlobalTheory.PlaceModel GlobalTheory.AlgWave GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle
variable {D : D7}
end GlobalTheory.BotFourier
namespace GlobalTheory.BotFourier
open GlobalTheory.PlaceModel GlobalTheory.AlgWave

theorem finite_datum_eq_sum_heisenberg : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc}
    {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) →
    L.Is μ₀ → IsBottomTri W i j X →
    ∀ t : T, ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
      (∀ p, (w p).map (infPart D) = 0) ∧ X.f t = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t
  classical
  have hI := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hν := (hI.weil' t).hecT
  have hSd : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := by
    refine ⟨hI.rigA.1.1, fun y => (hI.rigA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩,
      fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [GlobalTheory.Grid.neg_gram, hc]
    · simp [GlobalTheory.Grid.neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  have hWd : IsSelfDualC WW X.rW.Λ := hI.rigW.1
  have he := hI.idem t
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hinf' := GlobalTheory.PlaceDatum.infPart_cA hinf
  set S := GlobalTheory.Grid.neg A with hSdef
  set e := X.e t with hedef
  set Λ : AddSubgroup (WO S WW) := latO S WW X.rA.Λ X.rW.Λ fun _ => True with hΛ
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := S)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSd)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hWd) X.rA.β X.rW.β
  have hSB := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_isSB hν.1 he (GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t) A WW X.rA.β X.rW.β Λ
    (GlobalTheory.PlaceDatum.exists_den_frMapO (S := S) hSd.1.fg hWd.1.fg X.rA.β X.rW.β)
    ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hI.fst t
  rw [hall Tm hTm]
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D W.ψ S WW X.rA.Λ X.rW.Λ hψ hSd hWd).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S WW _ _ hSd.1.fg hWd.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ ⊓ half S WW a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S WW _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have finX : ∀ x ∈ half S WW e, x.map (infPart D) = 0 := fun x hx =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf ((isHalf_iff S WW).2 hx)
  have finY : ∀ y ∈ half S WW (cA D e), y.map (infPart D) = 0 := fun y hy =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf' ((isHalf_iff S WW).2 hy)
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S WW => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S WW hk a, ← inv_smul_nsmul S WW hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S WW W.ψ
  obtain ⟨h1, k, hk, h2, h3⟩ := hSB
  have hmem := mem_algSpan (χ := fun x y : WO S WW => W.ψ (symplO S WW x y)) (X := half S WW e)
    (Y := half S WW (cA D e)) (L := Λ ⊓ half S WW e) (L' := Λ ⊓ half S WW (cA D e)) hb
    (fun x hx y hy => psi_mem hψ hSd hWd (finX x hx) (finY y hy)) inf_le_right inf_le_right
    (fun u hu y hy => (hdual u (finX u hu.2)).1 hu.1 y hy.1)
    (fun x hx h => ⟨(hdual x (finX x hx)).2 fun u hu => by
      have := h _ (hsm _ he' u hu)
      rwa [← symplO_smul, (mem_half S WW).1 hx] at this, hx⟩)
    (half_div S WW e) (half_div S WW _) tf
    (fun k hk => by
      obtain ⟨R, hR, h⟩ := hfin k hk
      refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
      obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
      refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e hee u hu, ?_⟩
      have := (mem_half S WW).1 ht.2
      rw [← this, htr, smul_add, smul_comm e k u])
    _ (fun x => stdFst_mem hν.1 he _ A WW X.rA.β X.rW.β x) (fun t ht => (isHalf_iff S WW).1 (h1 t ht)) k hk
    (fun u hu => h2 u hu.1 ((isHalf_iff S WW).2 hu.2))
    (fun t ht => ⟨h3 t ht, (half S WW e).nsmul_mem ((isHalf_iff S WW).1 (h1 t ht)) _⟩)
  set V : Submodule Qb (WO S WW → ℂ) := Submodule.span Qb
    {F | ∃ w : WO S WW, w.map (infPart D) = 0 ∧ F = heisO W.ψ S WW w X.vac} with hV
  have hvac : Tm (halfInd e Λ) = X.vac := by simpa using hTm.vac
  have s0 := GlobalTheory.isSBHalf_halfInd e Λ
  have hT : ∀ Ψ ∈ algSpan (fun x y : WO S WW => W.ψ (symplO S WW x y)) (half S WW e) (half S WW (cA D e))
      (Λ ⊓ half S WW e), Tm Ψ ∈ V := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem _ hh =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hh
      have s1 : IsSBHalf e Λ fun t => W.ψ (symplO S WW t y) * halfInd e Λ t := by
        obtain ⟨k, hk, hk'⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' (S := S) (T := WW)
          (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSd)
          (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hWd) y (finY y hy)
        obtain ⟨a1, k', hk1, a2, a3⟩ := s0
        refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
          fun t ht => ?_⟩
        · have e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t := by
            rw [mul_nsmul]
            exact a2 _ (nsmul_mem hu k) ((isHalf_iff S WW).2 (nsmul_mem ((isHalf_iff S WW).1 hh) k)) t
          have e2 : W.ψ (symplO S WW ((k * k') • u) y) = 1 := by
            rw [mul_nsmul']
            refine (hb.nsmul k _ y).trans ((hdual _ (finX _ (nsmul_mem ((isHalf_iff S WW).1 hh) k'))).1
              (nsmul_mem hu k') _ hk')
          simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
        · rw [mul_nsmul']
          exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
      have e1 : wave (fun x y : WO S WW => W.ψ (symplO S WW x y)) (Λ ⊓ half S WW e) x y =
          fun t => (fun t => W.ψ (symplO S WW t y) * halfInd e Λ t) (t + x) := by
        rw [halfInd_eq_ind]; rfl
      rw [e1, hTm.trans _ s1 x ((isHalf_iff S WW).2 hx), hTm.modul _ s0 y ((isHalf_iff S WW).2 hy), hvac]
      have e2 : heisO W.ψ S WW x (heisO W.ψ S WW y X.vac) =
          W.ψ (symplOH S WW x y) • heisO W.ψ S WW (x + y) X.vac := heisL_heisL S WW W.ψ x y X.vac
      rw [e2]
      refine smul_mem_of_mem (psiH_mem hψ hSd hWd (finX x hx) (finY y hy)) (Submodule.subset_span ⟨x + y, ?_, rfl⟩)
      refine Matrix.ext fun a b => ?_
      have q1 : infPart D (x a b) = 0 := congrFun (congrFun (finX x hx) a) b
      have q2 : infPart D (y a b) = 0 := congrFun (congrFun (finY y hy) a) b
      change infPart D (x a b + y a b) = 0
      rw [RingHom.map_add (f := _), q1, q2, add_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
    | smul c f _ hf =>
      change Tm ((c : ℂ) • f) ∈ V
      rw [map_smul]
      exact V.smul_mem c hf
  obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set').1 (hT _ hmem)
  choose w hw hgw using fun p => (g p).2
  refine ⟨n, fun p => (f p : ℂ), w, fun p => mem_algebraicClosure_iff.1 (f p).2, hw, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← hgw p]
  rfl
end GlobalTheory.BotFourier
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottom_fourier_coeff_heisenberg_expansion : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ t : T, ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
      (∀ p, (w p).map (infPart D) = 0) ∧ X.f t = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  first | exact @_root_.GlobalTheory.BotFourier.finite_datum_eq_sum_heisenberg | exact _root_.GlobalTheory.BotFourier.finite_datum_eq_sum_heisenberg | (intros; apply _root_.GlobalTheory.BotFourier.finite_datum_eq_sum_heisenberg <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ClassSumKernelIsAlgebraic

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
namespace GlobalTheory.BotAlgI
theorem classSum_kernel_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ dg : D.what₂.Tau →₀ ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A.rank →₀ ℕ,
      Finsupp.mapDomain Prod.fst k = dg → IsAlgebraic ℚ (X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h x / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX dg
  obtain ⟨Ω, hΩ, hjet⟩ := _root_.GlobalTheory.T.bottom_translate_jets_algebraic hP hI hL hX dg
  refine ⟨Ω, hΩ, fun t x hx h hh k hk => ?_⟩
  obtain ⟨n, c, w, hc, hw, hf⟩ := _root_.GlobalTheory.T.bottom_fourier_coeff_heisenberg_expansion hP hI hL hX t
  choose n' c' w' hc' hw' hm using fun p => _root_.GlobalTheory.T.twisted_moved_translate_algebraic hP hI hL hX t x hx h hh (w p) (hw p)
  have hψ := hX.is.isVac.1
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hv : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW X.vac := hX.is.isVac.2.theta
  set φ : PolF D WW.rank A.rank := MvPolynomial.monomial k 1 with hφ
  set pt : (WO (GlobalTheory.Grid.neg A) WW → ℂ) → (WO (GlobalTheory.Grid.neg A) WW → ℂ) := fun f =>
    pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B f φ with hpt
  have comb : ∀ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, (y p).map (infPart D) = 0) →
      pt (∑ p, a p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) X.vac) =
        ∑ p, a p • pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) X.vac) := fun n a y hy => by
    have h1 := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW hψ hθ (fun τ => -X.rA.s τ) X.rW.s
      X.rA.B X.rW.B X.vac hv n a y hy φ).1
    have h2 : ∀ p, heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) (pt X.vac) = pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) X.vac) :=
      fun p => by
        have := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW hψ hθ (fun τ => -X.rA.s τ) X.rW.s
          X.rA.B X.rW.B X.vac hv 1 (fun _ => 1) (fun _ => y p) (fun _ => hy p) φ).1
        simpa using this
    simp only [← h2]
    exact h1.symm
  have e1 : ∀ g, ((X.ω t).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm x, h) g = X.ω t (x, h) g := fun g => rfl
  have move : ∀ g, IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW g → X.ω t (x, h) (pt g) = pt (X.ω t (x, h) g) := fun g hg => by
    rw [← e1, ← e1]
    exact GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ (hX.is.weil t) W.θ hθ ((GlobalTheory.Grid.ofSgn true A).symm x) hx h hh
      (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B g φ hg
  have hval : X.ker W.ψ W.θ t φ h x / Ω =
      ∑ p, c p * ∑ q, c' p q * (pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w' p q) X.vac) 0 / Ω) := by
    have e2 : X.ker W.ψ W.θ t φ h x = X.ω t (x, h) (pt (X.f t)) 0 := rfl
    have e3 : ∀ p, X.ω t (x, h) (pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac)) =
        ∑ q, c' p q • pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w' p q) X.vac) := fun p => by
      rw [move _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv _), hm p, comb _ _ _ (hw' p)]

    rw [e2, hf, comb _ _ _ hw, map_sum]
    simp only [map_smul, e3, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  rw [hval, ← mem_algebraicClosure_iff]
  refine sum_mem fun p _ => mul_mem (mem_algebraicClosure_iff.2 (hc p)) (sum_mem fun q _ => mul_mem
    (mem_algebraicClosure_iff.2 (hc' p q)) (mem_algebraicClosure_iff.2 (hjet _ (hw' p q) k hk)))
theorem classSums_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  obtain ⟨v, N, z, w, κ, hv, hz, hw, hκ1, hκ2, hcls⟩ := _root_.GlobalTheory.T.bottom_class_sum_integral_neg hP hI hL hX
  obtain ⟨dg, hproj⟩ := _root_.GlobalTheory.T.twisted_real_average_kernel_isAlgebraic hP hI hL hX
  obtain ⟨Ω, hΩ, hdict⟩ := _root_.GlobalTheory.BotAlgI.classSum_kernel_isAlgebraic hP hI hL hX dg
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  refine ⟨(v : ℂ) * Ω, mul_ne_zero hv' hΩ, fun t h hh k => ?_⟩
  choose m r U hr hU heq using fun l => hproj κ hκ1 hκ2 t (z l) (hz l) h hh k
  have hval : X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / ((v : ℂ) * Ω) =
      ∑ l, ((w l : ℂ))⁻¹ * ∑ p, r l p * (X.ker W.ψ W.θ t (MvPolynomial.monomial (U l p) 1) h (z l) / Ω) := by
    rw [hcls t _ h hh]
    simp only [heq, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro p _
    field_simp
  rw [hval, ← mem_algebraicClosure_iff]
  refine sum_mem fun l _ => mul_mem (inv_mem ?_) (sum_mem fun p _ => mul_mem ?_ ?_)
  · rw [mem_algebraicClosure_iff]
    simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) ((w l : ℚ)))
  · rw [mem_algebraicClosure_iff]; exact hr l p
  · rw [mem_algebraicClosure_iff]; exact hdict t (z l) (hz l) h hh (U l p) (hU l p)
end GlobalTheory.BotAlgI
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottom_classSums_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  first | exact @_root_.GlobalTheory.BotAlgI.classSums_isAlgebraic | exact _root_.GlobalTheory.BotAlgI.classSums_isAlgebraic | (intros; apply _root_.GlobalTheory.BotAlgI.classSums_isAlgebraic <;> assumption)
end
end
end
