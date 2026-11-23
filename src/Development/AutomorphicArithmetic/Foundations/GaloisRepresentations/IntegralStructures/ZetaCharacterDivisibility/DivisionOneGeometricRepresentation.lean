module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.HtCocharOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PAlgOfFix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PCharOfZeta
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicLevelAwayNonsplit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDetEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivDet
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivSet
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivUniq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PGenPin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PInFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PIsoMove
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCount
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PJumpSeed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLocConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLocSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PPhiSeed
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSSBlock
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSatCent
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSchurU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSepPin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSmall
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSubLoc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSubSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PZetaEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PZetaLoc
public import Development.EtaleCohomology.DivisorCycles.GoalHolds

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PCoverIn

section

section

namespace UpperTheory.Gal.Int.Div

open GlobalTheory.BlockSum (blockRep)

theorem coverIn_of : CoverIn := by
  intro Γ k _ _ a d r ρ ⟨m, B, hB, hg⟩
  let n := Fintype.card (Σ _ : Fin m, Fin a)
  let e : (Σ _ : Fin m, Fin a) ≃ Fin n := Fintype.equivFin _
  let σ : Fin n ≃ Fin a × Fin m := e.symm.trans ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _))
  refine ⟨m, n, e, B.submatrix σ id, ?_, fun g => ?_⟩
  · have h := Matrix.rank_submatrix B σ (Equiv.refl _)
    simpa [hB] using h
  · have key : ((blockRep (a := fun _ : Fin m => a) e fun _ => r) g : Matrix (Fin n) (Fin n) k) =
        (Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k)).submatrix σ σ := by
      rw [GlobalTheory.BlockSum.blockRep_val]
      ext i j
      obtain ⟨⟨x, u⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨y, v⟩, rfl⟩ := e.surjective j
      simp [σ, Matrix.blockDiagonal'_apply, Matrix.one_apply, Matrix.kroneckerMap_apply]
    rw [key]
    have h1 : B.submatrix σ id = B.submatrix σ (Equiv.refl _) := rfl
    have h2 : (ρ g : Matrix (Fin d) (Fin d) k) = (ρ g : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl _) (Equiv.refl _) := by simp
    rw [h1, Matrix.submatrix_mul_equiv, hg g, h2, Matrix.submatrix_mul_equiv]
    simp

end UpperTheory.Gal.Int.Div
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDenseUs

section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.denseUs_of :
    DenseUs := by
  classical
  intro E Ω _ _ _ _ _ _ l _ a d hd U hU X
  have hfin := GlobalTheory.CongL.UnitLim.finite_not_sph a U hU
  refine (GlobalTheory.CongL.UnitLim.dense_frob_usable_off E Ω l Fact.out d hd (X ∪ hfin.toFinset)).mono ?_
  rintro g ⟨w, hw, hus, hl, -, A, hA, hg⟩
  refine ⟨w, fun h => hw (Finset.mem_union_left _ h), hus, hl, ?_, A, hA, hg⟩
  by_contra hB
  exact hw (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨hus.1, hB⟩))
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PJumpCard

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.jumpCard_of :
    JumpCard := by
  intro l _ P AI tied E Ω _ _ _ _ _ A O _ _ _ Bw a r hdR τ LL' τ' hτ
  obtain ⟨T⟩ := id tied
  obtain ⟨L₀, r₀, hm, hd⟩ := hdR
  have l₁ : L₀.1 ≤ (supExt L₀ LL').1 := le_sup_left
  have l₂ : LL'.1 ≤ (supExt L₀ LL').1 := le_sup_right
  have hm' := hm.enlarge l₁
  have hd' := (local_ext P Bw l₁ r₀).2.1.2 hd
  have hτ' : IsInduced Bw τ ((IntermediateField.inclusion l₂).comp τ') := fun x => hτ x
  have hdr' : IsDR (P.PD Bw.Kw) (Bw.repE (supExt L₀ LL') (mapRep (IntermediateField.inclusion l₁).toRingHom r₀)) := by
    rw [IsDR, Module.finrank_fin_fun]
    exact hd'
  obtain ⟨hfin, -, hrk⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T _ (supExt L₀ LL') _
    (Bw.repE (supExt L₀ LL') (mapRep (IntermediateField.inclusion l₁).toRingHom r₀))).1
      ((IntermediateField.inclusion l₂).comp τ')
  obtain ⟨J', h1, h2⟩ := @GlobalTheory.HtCardProof.exists_count _ _ _ _ _ T _ _
    ((mapRep (IntermediateField.inclusion l₁).toRingHom r₀).comp Bw.e.symm.toMonoidHom)
    ((IntermediateField.inclusion l₂).comp τ') hfin
  exact ⟨J', ⟨_, _, hm', hd', _, hτ', h2⟩, h1.trans ((hrk hdr').trans (Module.finrank_fin_fun _))⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLacBridge

section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.lacBridge_of :
    LacBridge := by
  intro E Ω _ _ _ _ _ l _ a dd ρ h
  obtain ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ, J₀, hc, hm, hL⟩ := h
  have hinj : Function.Injective (fun i => J₀.orderEmbOfFin hc i) := (J₀.orderEmbOfFin hc).injective
  refine ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ,
    fun i => J₀.orderEmbOfFin hc i, hinj, fun i => hm _ (Finset.orderEmbOfFin_mem J₀ hc i), ?_⟩
  intro S T hS hT' hd heq
  let f : Fin a ↪ ℤ := ⟨fun i => J₀.orderEmbOfFin hc i, hinj⟩
  have hsub : ∀ C : Finset (Fin a), C.map f ⊆ J₀ := by
    intro C x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.orderEmbOfFin_mem J₀ hc i
  refine hL (S.map f) (T.map f) (hsub S) (hsub T) ((Finset.disjoint_map f).2 hd)
    (hS.map) (hT'.map) ?_
  rw [Finset.card_map, Finset.card_map, Finset.sum_map, Finset.sum_map]
  have : ((T.card : ℤ) * ∑ i ∈ S, f i : ℚ) = (S.card : ℤ) * ∑ i ∈ T, f i := by
    simpa [f] using heq
  simpa using (by exact_mod_cast this : (T.card : ℤ) * ∑ i ∈ S, f i = (S.card : ℤ) * ∑ i ∈ T, f i)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PRootPin

section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.rootPin_of :
    RootPin := by
  intro p s m hp hdeg hdvd hprod hgen
  have hspl : p.Splits := IsAlgClosed.splits p
  have hq : rootPol s ^ m ≠ 0 := by
    apply pow_ne_zero
    exact (monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)).ne_zero
  have hle : p.roots ≤ (rootPol s ^ m).roots := Polynomial.roots.le_of_dvd hq hdvd
  have hroots : (rootPol s ^ m).roots = m • s := by
    rw [Polynomial.roots_pow]
    unfold rootPol
    rw [roots_multiset_prod_X_sub_C]
  have hcard : p.roots.card = s.card := by
    rw [splits_iff_card_roots.mp hspl, hdeg]
  have hmem : ∀ x ∈ p.roots, x ∈ s := by
    intro x hx
    have := Multiset.mem_of_le hle hx
    rw [hroots, Multiset.mem_nsmul] at this
    exact this.2
  have heq : p.roots = s := hgen _ hcard hmem hprod
  rw [hspl.eq_prod_roots_of_monic hp, heq]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.DivisionOneGeometricRepresentation

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU

namespace UpperTheory.Gal.Int.Div

theorem subLoc_holds : SubLoc := subLoc_of subSplit_of inFacts_of locConj_of locSum_of jumpCard_of
theorem phiSeed_holds : PhiSeed := phiSeed_of subLoc_holds locConj_of rootPin_of algGen_of
theorem centU_holds : CentU := centU_of zetaEx_of zetaLoc_of schurU_of charOfZeta_of algOfFix_of satCent_of
theorem detEx_holds : DetEx := detEx_of centU_holds
theorem divDet_holds : DivDet := divDet_of denseUs_of detFrob_of
theorem senWLac_holds : PositivityTheory.AutomorphicGaloisHodgeTate.Div.SenWLac := senWLac_of jumpCard_of
theorem divSet_holds : DivSet := divSet_of LateralTheory.DivDb.goal_holds senWLac_holds lacBridge_of inFacts_of
theorem divOne_holds : DivOne := divOne_of divSet_holds denseUs_of detFrob_of inFacts_of sepPin_of
theorem divAll_holds : DivAll :=
  divAll_of detEx_holds divDet_holds phiSeed_holds divOne_holds (divUniq_of denseUs_of) isoMove_of
    (frobSeed_of inFacts_of genPin_of algGen_of detFrob_of) (jumpSeed_of coverIn_of sSBlock_of subLoc_holds locConj_of jumpCard_of)
    subLoc_holds

end UpperTheory.Gal.Int.Div
end
end
