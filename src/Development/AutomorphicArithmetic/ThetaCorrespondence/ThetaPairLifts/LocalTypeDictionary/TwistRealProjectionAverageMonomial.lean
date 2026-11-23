module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AverageDetCharMonomialEqSumProdMinorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeMemUnitary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndex
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaarLifted
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRealPointFockVectorPositiveDefiniteDet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Polynomial.Basic
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanUnitaryWeights

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped Matrix

namespace GlobalTheory.BottomRealAct

theorem substF_one_eq_colSub {ι : Type} {N n : ℕ} (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) M = GlobalTheory.MinorFrame.colSub M := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [GlobalTheory.CompactHowe.substF_X]
  simp only [GlobalTheory.MinorFrame.colSub, MvPolynomial.aeval_X]
  rw [Finset.sum_eq_single v.2.1]
  · simp only [Matrix.one_apply_eq, one_mul]
  · intro x _ hx
    simp only [Matrix.one_apply_ne hx, zero_mul, MvPolynomial.C_0, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rightRegularAction_list_dLR_eq_append {G : Type*} [CommGroup G] (a x y e c : G) : a * x * e / (c * e) = a * y * e / (c * e) * (x * y⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

end GlobalTheory.BottomRealAct
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndexStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.exists_int_eq_exponent_add_half_index : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau) (a : ℚ), IsHeckeChar D χ → ResEta D χ n → HasInfExp D χ τ a → ∃ e : ℤ, (e : ℚ) = a + (n : ℚ) / 2 := by
  first | exact @GlobalTheory.SplitParity.exists_int_add_half | exact GlobalTheory.SplitParity.exists_int_add_half | (intros; apply GlobalTheory.SplitParity.exists_int_add_half <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealUnitaryFockColumnActionSurjective

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped Matrix

namespace GlobalTheory.RealColAct

theorem compAt_eq_infMat {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V h) = infMat D.sp.cm.sig V.gram (θ τ) h := rfl

theorem realCol_surjective {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) :
    Function.Surjective (GlobalTheory.RealColAct.realCol θ hθ V hV) := by
  classical
  intro u
  have hex : ∀ τ, ∃ h : GA D V, IsAtTau θ V τ ((u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) h := fun τ => by
    refine (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ _ ?_).exists
    have hu := transpose_mem_unitary (u τ).2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    show _ * _ * _ = _
    rw [gramAt_of_gram_one hV, Matrix.mul_one, hu]
  choose hτ hhτ using hex
  have key : ∀ (L : List D.what₂.Tau), L.Nodup → ∀ ρ,
      compAt θ ρ (Formalism.L2.Theta.mt V (L.map hτ).prod) =
        if ρ ∈ L then ((u ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) else 1 := by
    intro L
    induction L with
    | nil => intro _ ρ; simp only [List.map_nil, List.prod_nil, List.not_mem_nil, if_false]; exact GlobalTheory.StdUnn.CartanMove.compAt_mt_one θ ρ V
    | cons a L ih =>
      intro hL ρ
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, ih hL.2 ρ, compAt_eq_infMat]
      by_cases c : ρ = a
      · subst c
        rw [(hhτ ρ).2.1, if_neg hL.1, if_pos List.mem_cons_self, Matrix.mul_one]
      · rw [(hhτ a).2.2 ρ c, Matrix.one_mul]
        by_cases d : ρ ∈ L
        · rw [if_pos d, if_pos (List.mem_cons_of_mem a d)]
        · rw [if_neg d, if_neg (by simp [c, d])]
  let L := (Finset.univ : Finset D.what₂.Tau).toList
  have hmem : (L.map hτ).prod ∈ GinfC V := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact (hhτ τ).1
  refine ⟨(⟨(L.map hτ).prod, hmem⟩ : GinfC V)⁻¹, ?_⟩
  funext ρ
  apply Subtype.ext
  rw [realCol_apply]
  simp only [InvMemClass.coe_inv, inv_inv]
  rw [key L (Finset.nodup_toList _) ρ, if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ)), Matrix.transpose_transpose]

end GlobalTheory.RealColAct
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealUnitaryFockColumnActionSurjectiveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.realUnitaryFockColumnAction_surjective : ∀ {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1), Function.Surjective (GlobalTheory.RealColAct.realCol θ hθ V hV) := by
  first | exact @GlobalTheory.RealColAct.realCol_surjective | exact GlobalTheory.RealColAct.realCol_surjective | (intros; apply GlobalTheory.RealColAct.realCol_surjective <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BoundaryRealGroupAction

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
open scoped Matrix
namespace GlobalTheory.BottomRealAct
theorem boundary_real_group_action : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (m : D.what₂.Tau → ℤ) (ρ : GinfC A' →* (D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ)),
      (∀ τ a b, Measurable fun g => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ) a b) ∧ Function.Surjective ρ ∧
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ (g : GinfC A') (P : MvPolynomial (FVar D WW.rank A'.rank) ℂ),
        X.ker' W.ψ W.θ t P h (x * (g : GA D A')) =
          (∏ τ, (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ).det ^ (m τ)) *
            X.ker' W.ψ W.θ t (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) h x := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hV : HSpace.gram A' = 1 := hX.std'.1
  have hVW : HSpace.gram WW = 1 := hX.stdW.1
  have hW := fun t => GlobalTheory.RowTest.BottomClassSum.weil' hX t
  have hxi : ∀ t τ, HasInfExp D (L.xi t) τ 0 := fun t τ => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    exact GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  choose b hb using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ WW.rank τ hθ (hW μ₀).hecT (hW μ₀).resT
  have hrel : ∀ t, (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) =
      (L.mu μ₀ (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) / (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) *
        (L.xi t * (L.xi μ₀)⁻¹) := by
    intro t
    simp only [LevCh.mu, Lift.tup]
    exact rightRegularAction_list_dLR_eq_append _ _ _ _ _
  have hbt : ∀ t τ, HasInfExp D ((L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2))) τ (b τ) := by
    intro t τ
    rw [hrel t]
    have := GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hb τ)
      (GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hxi t τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hxi μ₀ τ)))
    simpa using this
  choose k hk using fun τ => GlobalTheory.T.exists_int_eq_exponent_add_half_index D _ WW.rank τ (b τ) (hW μ₀).hecT (hW μ₀).resT (hb τ)
  refine ⟨k, GlobalTheory.RealColAct.realCol W.θ hθ A' hV, ?_, GlobalTheory.T.realUnitaryFockColumnAction_surjective hθ A' hV, ?_⟩
  · intro τ a c
    simp only [GlobalTheory.RealColAct.realCol_apply, Matrix.transpose_apply]
    exact (((continuous_apply a).comp ((continuous_apply c).comp ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
      ((GlobalTheory.RealWeil.continuous_mt A').2.comp continuous_subtype_val))))).measurable
  · intro t x _ h _ g P
    choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ A'.rank τ hθ (hW t).hecS (hW t).resS
    choose e₁ he₁ using fun τ => GlobalTheory.T.exists_int_eq_exponent_add_half_index D _ A'.rank τ (a τ) (hW t).hecS (hW t).resS (ha τ)
    have hψ : Continuous W.ψ := hX.is.isVac.1.1.1
    have es : X.rA'.s = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).1
    have eB : X.rA'.B = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).2
    have esW : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
    have eBW : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
    have hf : IsThetaFunO W.ψ A' WW (X.f' t) := (GlobalTheory.ConstRatio.theta_f hX.is t).2
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.is.idem t)
    have hv : ∀ τ, IsFockVacAt (heisO W.ψ A' WW) W.θ τ (cplxO 1 1) (X.f' t) := fun τ => by
      have h0 := hX.is.isVac'.2.fock τ
      rw [es, esW] at h0
      exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ hθ ho.conj.infPart_eq ho.conj.conj.infPart_eq (hX.is.snd t)
        hX.is.isVac'.2.theta hf h0
    have hBS : ∀ τ, ((fun _ => (1 : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) τ)ᴴ * gramAt D A' τ * 1 = 1 := fun τ => by
      rw [GlobalTheory.RealColAct.gramAt_of_gram_one hV]; simp
    have hBT : ∀ τ, ((fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ)ᴴ * gramAt D WW τ * 1 = 1 := fun τ => by
      rw [GlobalTheory.RealColAct.gramAt_of_gram_one hVW]; simp
    have key0 := GlobalTheory.RealFockPos.om_pureTensorO_pos D W.ψ W.θ A' WW _ _ (X.ω' t) (hW t) hθ (fun _ => 1) (fun _ => 1) hBS hBT
      a b ha (hbt t) e₁ (fun τ => -k τ) he₁ (fun τ => by push_cast; rw [hk τ]) (X.f' t) hf hv (g : GA D A') g.2 1 (one_mem _) P
    simp only [inv_one, Matrix.one_mul, Matrix.mul_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.det_one, one_zpow, mul_one]
      at key0
    have hinv : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A')))⁻¹ =
        compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A')⁻¹) := fun τ =>
      Matrix.inv_eq_right_inv (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := W.θ) τ (g : GA D A'))
    have hsc : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A'))).det ^ (-k τ) =
        ((GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)).det ^ (k τ) := fun τ => by
      rw [GlobalTheory.RealColAct.realCol_apply, Matrix.det_transpose, ← hinv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
        inv_zpow', zpow_neg]
    have hsub : GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ))
        (fun τ => ((compAt W.θ τ (Formalism.L2.Theta.mt A' (g : GA D A')))⁻¹)ᵀ) =
        GlobalTheory.MinorFrame.colSub (fun τ => (GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) := by
      rw [substF_one_eq_colSub]
      congr 1
      funext τ
      rw [GlobalTheory.RealColAct.realCol_apply, hinv]
    have key : (X.ω' t) ((g : GA D A'), 1) ((pureTensorO W.ψ W.θ A' WW (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (X.f' t)) P) =
        (∏ τ, ((GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)).det ^ (k τ)) •
          (pureTensorO W.ψ W.θ A' WW (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (X.f' t))
            (GlobalTheory.MinorFrame.colSub (fun τ => (GlobalTheory.RealColAct.realCol W.θ hθ A' hV g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) := by
      rw [key0, ← hsub]
      congr 1
      exact Finset.prod_congr rfl fun τ _ => hsc τ
    unfold Tri.ker' thetaKO
    rw [es, eB, esW, eBW]
    have e : ((x * (g : GA D A'), h) : GA D A' × GA D WW) = (x, h) * ((g : GA D A'), 1) := by simp
    rw [e, map_mul, Module.End.mul_apply, key, map_smul, Pi.smul_apply, smul_eq_mul]
end GlobalTheory.BottomRealAct
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.twist_boundary_real_action : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (m : D.what₂.Tau → ℤ) (ρ : GinfC A' →* (D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ)),
      (∀ τ a b, Measurable fun g => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ) a b) ∧ Function.Surjective ρ ∧
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ (g : GinfC A') (P : MvPolynomial (FVar D WW.rank A'.rank) ℂ),
        X.ker' W.ψ W.θ t P h (x * (g : GA D A')) =
          (∏ τ, (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ).det ^ (m τ)) *
            X.ker' W.ψ W.θ t (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) h x := by
  first | exact @_root_.GlobalTheory.BottomRealAct.boundary_real_group_action | exact _root_.GlobalTheory.BottomRealAct.boundary_real_group_action | (intros; apply _root_.GlobalTheory.BottomRealAct.boundary_real_group_action <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistRealProjectionAverageMonomial

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
theorem GlobalTheory.RealProj.realProjection_average_monomial : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ n : D.what₂.Tau → ℕ, ∀ (κ : Measure (GinfC A')), κ.IsMulLeftInvariant → IsProbabilityMeasure κ →
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A'.rank →₀ ℕ,
        ∃ (m : ℕ) (r : Fin m → ℂ) (U : Fin m → GlobalTheory.NormSum.Tup D A'.rank WW.rank n), (∀ p, IsAlgebraic ℚ (r p)) ∧
          ∫ g, X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A')) ∂κ =
            ∑ p, r p * X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D (U p)) h x := by
  intro D T _ L μ₀ sc G W i j A A' WW X hPr hInp hL hB
  obtain ⟨m, ρ, hρm, hρs, hact⟩ := _root_.GlobalTheory.T.twist_boundary_real_action hPr hInp hL hB
  obtain ⟨n, hn⟩ := GlobalTheory.T.average_det_char_monomial_eq_sum_prod_minors (ι := D.what₂.Tau) A'.rank WW.rank m
  refine ⟨n, fun κ hκ hκp t x hx h hh k => ?_⟩
  let Λ : GlobalTheory.MinorFrame.Pol D.what₂.Tau WW.rank A'.rank →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : WO A' WW => ℂ) 0).comp
      ((X.ω' t (x, h)).comp (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t)))
  have hΛ : ∀ P, Λ P = X.ker' W.ψ W.θ t P h x := fun P => rfl
  obtain ⟨hTop, -, -, -, hBorel⟩ := Formalism.IndefR.Eqv.ga_facts D A'
  haveI : BorelSpace (GinfC A') := Subtype.borelSpace _
  have hleft (u : GinfC A') : AEMeasurable (u * ·) κ :=
    (continuous_const_mul u).measurable.aemeasurable
  obtain ⟨M, r, U, hr, hI⟩ := hn κ hκp hκ hleft ρ hρm hρs Λ k
  refine ⟨M, r, U, hr, ?_⟩
  have e : (fun g : GinfC A' => X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A'))) =
      fun g => (∏ τ, (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ).det ^ (m τ)) *
        Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) (MvPolynomial.monomial k 1)) := by
    funext g; rw [hact t x hx h hh g, hΛ]
  rw [e, hI]
  rfl
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.twist_realProjection_average_monomial : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ n : D.what₂.Tau → ℕ, ∀ (κ : Measure (GinfC A')), κ.IsMulLeftInvariant → IsProbabilityMeasure κ →
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A'.rank →₀ ℕ,
        ∃ (m : ℕ) (r : Fin m → ℂ) (U : Fin m → GlobalTheory.NormSum.Tup D A'.rank WW.rank n), (∀ p, IsAlgebraic ℚ (r p)) ∧
          ∫ g, X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A')) ∂κ =
            ∑ p, r p * X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D (U p)) h x := by
  first | exact @_root_.GlobalTheory.RealProj.realProjection_average_monomial | exact _root_.GlobalTheory.RealProj.realProjection_average_monomial | (intros; apply _root_.GlobalTheory.RealProj.realProjection_average_monomial <;> assumption)
end
end
end
