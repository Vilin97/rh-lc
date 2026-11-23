module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedBy
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSupportSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelCharacterEqBesselCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelGeneratedByLocalUnipotentsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlaceSetNotConjugatePlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotOfPlacedByStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColLevelMatchFamStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemRowJIffRTupStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelReductionCriterion

section

@[expose] public section

noncomputable section

namespace GlobalTheory.PrinFrame

section Alg

open Matrix

variable {A : Type} [CommRing A] {n : ℕ}

theorem conj_single_mem (S : Subring A) (p : S) (hp : p * p = p) (γ : GL (Fin n) A)
    (h : ∀ i j, i ≠ j → ∀ a b, (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S) (i j a b : Fin n) :
    (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S := by
  by_cases hij : i = j
  · subst hij
    by_cases hl : ∃ l, l ≠ i
    · obtain ⟨l, hl⟩ := hl
      have hp' : (p : A) * p = p := congrArg Subtype.val hp
      have e1 : ∑ c, γ.1 l c * (γ⁻¹).1 c l = 1 := by
        have := congrFun (congrFun γ.mul_inv l) l
        rwa [Matrix.mul_apply, Matrix.one_apply_eq] at this
      have e2 : (p : A) * ((γ⁻¹).1 a i * γ.1 i b) =
          ∑ c, ((p : A) * ((γ⁻¹).1 a i * γ.1 l c)) * ((p : A) * ((γ⁻¹).1 c l * γ.1 i b)) := by
        rw [← mul_one ((p : A) * _), ← e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        linear_combination (-((γ⁻¹).1 a i * γ.1 i b * γ.1 l c * (γ⁻¹).1 c l)) * hp'
      rw [e2]
      exact S.sum_mem fun c _ => S.mul_mem (h i l hl.symm a c) (h l i hl c b)
    · push Not at hl
      have e1 : (γ⁻¹).1 i i * γ.1 i i = 1 := by
        have := congrFun (congrFun γ.inv_mul i) i
        rwa [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i (fun c _ hc => absurd (hl c) hc)
          (fun hc => absurd (Finset.mem_univ i) hc)] at this
      rw [hl a, hl b, e1, mul_one]
      exact p.2
  · exact h i j hij a b

theorem red_conj_eq_one (S : Subring A) {k : Type} [CommRing k] (ρ : S →+* k) (p : S) (hρ : ρ p = 1) (γ : GL (Fin n) A)
    (h : ∀ i j a b, (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S) (y y₀ : Matrix (Fin n) (Fin n) S)
    (hy : y₀.map S.subtype = γ.1 * y.map S.subtype * (γ⁻¹).1) (h1 : y.map ρ = 1) : y₀.map ρ = 1 := by
  have e0 : ∀ {B : Type} [CommRing B] (f : S →+* B) (z : Matrix (Fin n) (Fin n) S), (z - 1).map f = z.map f - 1 := by
    intro B _ f z
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]
  have e1 : (y₀ - 1).map S.subtype = γ.1 * (y - 1).map S.subtype * (γ⁻¹).1 := by
    rw [e0, e0, hy, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv]
  have e2 : ∀ b a, ρ ((y - 1) b a) = 0 := fun b a => by
    have := congrFun (congrFun (e0 ρ y) b) a
    rwa [h1, sub_self] at this
  rw [← sub_eq_zero, ← e0]
  ext j i
  have e3 : p * (y₀ - 1) j i = ∑ a, ∑ b, (⟨_, h i j a b⟩ : S) * (y - 1) b a := by
    apply Subtype.ext
    have := congrFun (congrFun e1 j) i
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Subring.subtype_apply] at this
    rw [Subring.coe_mul, this]
    simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have e4 := congrArg ρ e3
  rw [map_mul, hρ, one_mul] at e4

  simp only [map_sum, map_mul, e2, mul_zero, Finset.sum_const_zero] at e4
  exact e4

theorem transv_entry (S : Subring A) (p : S) (β β₀ : GL (Fin n) A) (i j : Fin n) (z : Matrix (Fin n) (Fin n) S)
    (h : (p : A) • (β.1 * z.map S.subtype * (β⁻¹).1) =
      (p : A) • (β₀.1 * (Matrix.transvection i j (1 : S)).map S.subtype * (β₀⁻¹).1)) (a b : Fin n) :
    (p : A) * (((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b) ∈ S := by
  have h2 := congrArg (fun M => (β⁻¹).1 * M * β.1) h
  have e0 : (Matrix.transvection i j (1 : S)).map S.subtype = 1 + Matrix.single i j (1 : A) := by
    rw [Matrix.transvection, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single,
      map_one]
  have e1 : (β⁻¹).1 * (β.1 * z.map S.subtype * (β⁻¹).1) * β.1 = z.map S.subtype := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have e2 : (β⁻¹).1 * (β₀.1 * (1 + Matrix.single i j (1 : A)) * (β₀⁻¹).1) * β.1 =
      1 + ((β₀⁻¹ * β)⁻¹).1 * Matrix.single i j (1 : A) * (β₀⁻¹ * β).1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Units.inv_mul, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_smul, Matrix.smul_mul] at h2
  rw [e0, e1, e2] at h2
  have h3 := congrFun (congrFun h2 a) b
  have e3 : (((β₀⁻¹ * β)⁻¹).1 * Matrix.single i j (1 : A) * (β₀⁻¹ * β).1) a b =
      ((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b := by
    generalize ((β₀⁻¹ * β)⁻¹).1 = M
    generalize (β₀⁻¹ * β).1 = N
    simp [Matrix.mul_apply, Matrix.single, ite_and]
  simp only [Matrix.smul_apply, Matrix.add_apply, e3, smul_eq_mul, Matrix.map_apply, Subring.subtype_apply, mul_add] at h3
  rw [← sub_eq_iff_eq_add'] at h3
  rw [← h3]
  refine S.sub_mem (S.mul_mem p.2 (z a b).2) (S.mul_mem p.2 ?_)
  rw [Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

end Alg

end GlobalTheory.PrinFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrinFrame

variable {D : D7}



theorem redFn_eq_one_of_le (V : HSp D) (β β₀ : GL (Fin V.rank) (Lev.EAf D))
    (h₀ : Formalism.L2.DIV.IsFrame β₀ (Formalism.L2.Herm.crdLat V V.L0))
    (hle : ∀ κ ∈ GfC V, finE V κ ∈ Formalism.L2.DIV.St β₀ → finE V κ ∈ Formalism.L2.DIV.St β)
    (P : Formalism.L2.DIV.Pl D.host.E) (hP : ¬ Formalism.IndefR.Lev.IsConjPl P P) (x : GL (Fin V.rank) (Lev.EAf D))
    (hx : x ∈ Formalism.L2.DIV.St β) (hx₀ : x ∈ Formalism.L2.DIV.St β₀) (h1 : redFn β P x = 1) : redFn β₀ P x = 1 := by
  have hB : IsBaseFrame V β₀ (Formalism.L2.Herm.crdLat V V.L0) (1 ^ 0) := by
    refine ⟨h₀, GlobalTheory.LevelChoices.dualL_crdLat V, one_pos, fun x hx => ?_, fun x hx => ?_⟩
    · rw [pow_zero, Nat.cast_one, one_smul]
      rwa [← GlobalTheory.LevelChoices.coe_crdLat] at hx
    · rw [pow_zero, Nat.cast_one, one_smul, ← GlobalTheory.LevelChoices.coe_crdLat]
      exact hx
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt hP
  obtain ⟨p, hp, hpp, hres⟩ := GlobalTheory.ParahoricLift.exists_idem_int he
  have hoff : ∀ i j, i ≠ j → ∀ a b, (p : Lev.EAf D) * (((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j hij
    have hu' : p * (Matrix.transvection i j (1 : Formalism.L2.Herm.intAf D.host.F D.host.E)).det = p := by
      rw [Matrix.det_transvection_of_ne i j hij, mul_one]
    have hmm := GlobalTheory.ParahoricLift.conj_inv_part β₀ p p _ hu' hpp
    rw [hp] at hmm
    obtain ⟨κ, hs, hκ⟩ := GlobalTheory.ParahoricLift.split_lift_fin V he.1 _ _ hmm
    have hPI : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
    obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    have hsf := GlobalTheory.LevSplit.supp_fin V (f := e + cA D e) hs
    rw [← hp] at hκ
    have hf : GlobalTheory.LevSplit.finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
      rw [RingHom.map_add (f := _), GlobalTheory.LevSplit.finSw_cA, hp]
    have hSt : finE V κ ∈ Formalism.L2.DIV.St β₀ :=
      GlobalTheory.ParahoricLift.mem_St_of_part D.sp.cm.sig V.gram _ β₀ hB.1 (GlobalTheory.ParahoricLift.hatL_selfDual hB) p p hpp
        (GlobalTheory.LevSplit.sigR_int p.2) _ hu' (finE V κ) (GlobalTheory.LevSplit.finE_mem_UA V κ) _ hf hsf hκ
    obtain ⟨z, hz⟩ := hle κ ((T3 P e _ hPI).2.2.1 κ hs) hSt
    rw [← hz] at hκ
    exact transv_entry _ p β β₀ i j z.1 hκ
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y₀, hy₀⟩ := hx₀
  rw [redFn_frGL] at h1
  rw [← hy₀, redFn_frGL]
  have e1 : intGL D.host.F D.host.E V.rank y₀ = (β₀⁻¹ * β) * intGL D.host.F D.host.E V.rank y * (β₀⁻¹ * β)⁻¹ := by
    have e2 : β₀ * intGL D.host.F D.host.E V.rank y₀ * β₀⁻¹ = β * intGL D.host.F D.host.E V.rank y * β⁻¹ := hy₀
    rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq] at e2
    rw [e2]
    group
  exact Units.ext (red_conj_eq_one _ (resS D.host.F P) p hres (β₀⁻¹ * β) (conj_single_mem _ p hpp _ hoff) y.1 y₀.1
    (congrArg Units.val e1) (congrArg Units.val h1))

theorem kset_iff_finE (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0))
    (κ : GA D (D.sp.Y 0)) : (iotaX X h κ).2 ∈ X.B.I.Kset ↔ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ I.Kset ↔ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
    intro I hI
    subst hI
    have hL : (Formalism.L2.SG.InstExistsPf.instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 :=
      Formalism.L2.SG.InstExistsPf.Lv_eq_map D
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx := GlobalTheory.FlagBasis.kset_iff (Formalism.L2.SG.InstExistsPf.instOf D) (β := β) (hL ▸ hβ) (Formalism.IndefR.RationalEmbedding.iota D κ).2
    generalize Lev.finE (D.sp.Y 0) κ = y at e2 ⊢
    subst e2
    exact hx
  exact key X.B.I h

theorem edgeSum_symEdge_one {k : Type} [CommRing k] {n : ℕ} (ρ l : ℕ) : edgeSum (symEdge ρ l) (1 : GL (Fin n) k) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · refine Matrix.one_apply_ne ?_
    rintro rfl
    unfold symEdge at h
    omega
  · rfl

theorem rowChi_eq_one : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), GlobalTheory.Core.Mi.IdE X → ∀ (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St β) ↔ ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset)) → ∀ κ ∈ rowJ X h, (∀ PP ∈ Pg, redFn β PP (finE (D.sp.Y 0) κ) = 1) → rowChi X h κ = 1 := by
  intro D X h _ Pg hPg hIdem β hβ κ hκ hred
  have hnc := GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces Pg hPg hIdem
  have hψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1 := fun PP => by
    haveI := PP.isPrime
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero
    exact ⟨ψ, fun e => hψ (by rw [e]; rfl)⟩
  choose ψ0 hψ0 using hψ
  obtain ⟨β₀, h₀, hK⟩ := GlobalTheory.SeeConjRead.read_fin X h Pg hPg hnc ψ0 fun PP _ => hψ0 PP
  have hle : ∀ κ ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β₀ → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β :=
    fun κ h1 h2 => ((hβ κ).2 ⟨(GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h κ).2 h1, (kset_iff_finE X h β₀ h₀ κ).2 h2⟩).2
  have hS₀ := ((hK κ).1.1 hκ.2).1
  have hS := hle κ ((GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h κ).1 hκ.1) hS₀
  refine ((hK κ).2 hκ.2).trans (Finset.prod_eq_one fun PP hPP => ?_)
  rw [redFn_eq_one_of_le (D.sp.Y 0) β β₀ h₀ hle PP (hnc PP hPP PP hPP) _ hS hS₀ (hred PP hPP), edgeSum_symEdge_one,
    AddChar.map_zero_eq_one]

end GlobalTheory.PrinFrame

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarCharacterSquareEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChrMatch

variable {D : D7}

theorem suppAt_conj (e : AE D) (V : HSp D) (a n : GA D V) (hn : Formalism.L2.Theta.SuppAt e V n) :
    Formalism.L2.Theta.SuppAt e V (a * n * a⁻¹) := by
  have h1 : Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 =
      Formalism.L2.Theta.mt V a * (Formalism.L2.Theta.mt V n - 1) * Formalism.L2.Theta.mt V a⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  have h2 : (e + cA D e) • (Formalism.L2.Theta.mt V n - 1) = Formalism.L2.Theta.mt V n - 1 := by
    ext i j; exact hn i j
  intro i j
  have h3 : (e + cA D e) • (Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1) = Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 := by
    rw [h1, ← Matrix.smul_mul, ← Matrix.mul_smul, h2]
  exact congrFun (congrFun h3 i) j

theorem levChi_mul (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ levS V β L) (hk' : k' ∈ levS V β L) : levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have := (levChar D.sp.cm V.gram β L).map_mul ⟨finE V k, hk.2⟩ ⟨finE V k', hk'.2⟩
  unfold levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg Units.val this

theorem levChi_of_red_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (hs : L.s = 0)
    (hQ : L.Q = ∅) {k : GA D V} (hk : ∀ PP ∈ L.Pg, redFn β PP (finE V k) = 1) : levChi V β L k = 1 := by
  have h1 : rTup β L (finE V k) = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 (finE V k)) = 1
    rw [hk PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levChi levFn
  rw [h1, blockDiagonalExtendByOnePrimeField_one, hs, hQ]
  simp

end GlobalTheory.ChrMatch

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCharacterEqExtension

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZeroChr
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem rowChi_conj_of_mem_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hPl : _root_.GlobalTheory.MiTop.PlacedAlt f B) (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀)
    (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : β = (_root_.GlobalTheory.Fam.pk_z W).βY 0)
    (Lz : Formalism.L2.DIV.LevDat D.host.E ℂ (D.sp.Y 0).rank) (hLz : Lz = _root_.GlobalTheory.LevZero.datZero_alt W)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (hmem : ∀ k ∈ levS (D.sp.Y 0) β Lz, s * k * s⁻¹ ∈ rowJ W.S.X W.Q.instEq) :
    ∀ k ∈ levS (D.sp.Y 0) β Lz, rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) β Lz k := by
  obtain ⟨kk, i1, i2, i3, i4, ι, v, o, n, G, pl, hcis, hvis, htie, hshape, hpin, hread, hbot⟩ := hPl
  have hBot := _root_.GlobalTheory.T.bessel_local_type_data_alt W hW u f B kk ι v o n G pl ⟨hcis, hvis, htie, hshape, hpin, hread, hbot⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hBl := hbot.lev h0
  have hE : GlobalTheory.Core.Mi.IdE W.S.X := hW.bot.idE
  have hTP : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.BaseChain.com_z W).Pg := hBot.typ
  have hemb : ∀ b, embA B.d B.o b = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o b : GA D (f.c.V 0)) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (f.c.V 0)) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (f.c.bes 0 D.R.rS h0).d : Subgroup (GA D (f.c.V 0))) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  have hps : psiBes W.Q.Rl.ψ B.d 1 (vecB B.o B.ζ) =
      (psiBes f.c.ψ (f.c.bes 0 D.R.rS h0).d 1 (vecB (f.c.bes 0 D.R.rS h0).o (f.c.bes 0 D.R.rS h0).ζ) : GA D (f.c.V 0) → ℂ) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => psiBes W.Q.Rl.ψ L.d 1 (vecB L.o L.ζ)) hBl)
  have hred : ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (k : GA D (D.sp.Y 0)),
      redFn (finE (D.sp.Y 0) s * β) PP (finE (D.sp.Y 0) (s * k * s⁻¹)) = redFn β PP (finE (D.sp.Y 0) k) := fun PP k => by
    rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.redFn_conj]
  subst hβ hLz
  refine GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) h0 hBot
    (fun k : GA D (D.sp.Y 0) => rowChi W.S.X W.Q.instEq (s * k * s⁻¹) =
      levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k) ?_ ?_ ?_ ?_
  · intro (k : GA D (D.sp.Y 0)) hk (k' : GA D (D.sp.Y 0)) hk' q q'
    show rowChi W.S.X W.Q.instEq (s * (k * k') * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) (k * k')
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    have q₁ : rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k := q
    have q₂ : rowChi W.S.X W.Q.instEq (s * k' * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k' := q'
    rw [GlobalTheory.ChrMatch.levChi_mul (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) hk hk', ← q₁, ← q₂, e, rowChi, rowChi, rowChi,
      map_mul, Prod.snd_mul, W.S.Y.hK.2.2.2.1 _ (hmem k hk).2 _ (hmem k' hk').2, star_mul']
  · intro PP (n : GA D (D.sp.Y 0)) q hn hq hl hk
    have h2 := GlobalTheory.T.indexZeroLevelCharacter_eq_besselCharacter (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) h0 hBot
      PP n q hq hl hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      rw [hs]; group
    have hj := hmem (t⁻¹ * n * t) (by rw [ht]; exact hk)
    rw [e] at hj
    have h1 := GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes D W.S.X W.Q.instEq u W.Q.Rl.ψ _ B hE PP.1 (G (pl.symm PP)).q.e
      (G (pl.symm PP)).q.split (hBot.loc PP).idem (hTP.1 PP.1 PP.2) _
      (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn') (GlobalTheory.ChrMatch.suppAt_conj _ _ _ _ hl.1) hj
    subst ht
    show rowChi W.S.X W.Q.instEq
      (s * ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * n * (show GA D (D.sp.Y 0) from f.g.b 0)) * s⁻¹) = _
    refine (congrArg _ e).trans (h1.trans (Eq.trans ?_ h2.symm))
    rw [GlobalTheory.CharLaws.psiBes_conj]
    exact congrFun hps n
  · intro (b : GA D (D.sp.X 0)) hb hk
    have hk' : (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o b * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W := by
      rw [hemb b]; exact hk
    have h1 := (_root_.GlobalTheory.T.level_trace_adapted_translate_alt W hW u f B hbot.trace hbot.adapted a₀ hH0 b hb).2 hk'
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    subst ht
    have h3 := (congrArg (rowChi W.S.X W.Q.instEq) e).trans h1
    rw [hemb b] at h3
    exact h3
  · intro (k : GA D (D.sp.Y 0)) hk hr1
    show rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k
    rw [GlobalTheory.PrinFrame.rowChi_eq_one D W.S.X W.Q.instEq hE (_root_.GlobalTheory.BaseChain.com_z W).Pg hTP hBot.com.split _ hSt _ (hmem k hk)
      (fun PP hPP => (hred PP k).trans (hr1 PP hPP))]
    exact (GlobalTheory.ChrMatch.levChi_of_red_one _ _ _ rfl rfl hr1).symm

theorem row_character_eq_extension_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H → κ ∈ rowJ W.S.X W.Q.instEq → rowChi W.S.X W.Q.instEq κ = ((Formalism.L2.DIV.ext1 (_root_.GlobalTheory.LevZero.datZero_alt W).P.H (_root_.GlobalTheory.LevZero.datZero_alt W).P.chi (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hPl a₀ hH0 a ha hac hSt κ hκ hκS hP _
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by
    have := GlobalTheory.Chain.StepVac.rank_Yc (D := D) (j := 0) (Nat.zero_le _)
    exact le_of_eq (this.trans (by simp))
  have hM := _root_.GlobalTheory.T.central_adapted_element_property_alt W hW u f B hPl a₀ hH0 a ha hac hSt
  obtain ⟨β, hβ⟩ : ∃ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), β = (_root_.GlobalTheory.Fam.pk_z W).βY 0 := ⟨_, rfl⟩
  obtain ⟨Lz, hLz⟩ : ∃ Lz : Formalism.L2.DIV.LevDat D.host.E ℂ (D.sp.Y 0).rank, Lz = _root_.GlobalTheory.LevZero.datZero_alt W := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = _root_.GlobalTheory.MiTop.translationElement f B a₀ a := ⟨_, rfl⟩
  have hfr : _root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a = finE (D.sp.Y 0) s * β := by rw [hs, hβ]; rfl
  have hSt' : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset) := by
    rw [← hfr]; exact hSt
  have key := _root_.GlobalTheory.LevZeroChr.rowChi_conj_of_mem_alt W hW u f B hPl a₀ hH0 a hac _ s rfl hs β hβ Lz hLz hSt'
  have hM' : ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β) →
      rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ) ∈ Lz.P.H → κ ∈ rowJ W.S.X W.Q.instEq := by
    rw [← hfr, hLz]; exact fun κ h1 h2 h3 => (hM κ h1 h2).2 h3
  have hκS' : finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β) := by rw [← hfr]; exact hκS
  have hP' : rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ) ∈ Lz.P.H := by rw [← hfr, hLz]; exact hP
  suffices hgoal : rowChi W.S.X W.Q.instEq κ =
      ((ext1 Lz.P.H Lz.P.chi (rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) by
    rw [← hfr, hLz] at hgoal; exact hgoal
  have e1 : Lz.s = 0 := by rw [hLz]; rfl
  have e2 : Lz.Q = ∅ := by rw [hLz]; rfl
  have e3 : (D.sp.Y 0).rank ≤ Lz.r := by rw [hLz]; exact hn
  clear hκS hP hM hSt hfr hs hβ hLz
  have hfin : ∀ s k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) → s * k * s⁻¹ ∈ GfC (D.sp.Y 0) := fun s k hk => by
    rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq] at hk ⊢
    rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, hk, mul_one, Prod.fst_inv, mul_inv_cancel]
  have hfe : ∀ k : GA D (D.sp.Y 0), finE (D.sp.Y 0) (s * k * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k * (finE (D.sp.Y 0) s)⁻¹ := fun k => by rw [map_mul, map_mul, map_inv]
  have hmem : ∀ k ∈ levS (D.sp.Y 0) β Lz, s * k * s⁻¹ ∈ rowJ W.S.X W.Q.instEq := by
    intro k hk
    obtain ⟨hf, hl⟩ := hk
    change finE (D.sp.Y 0) k ∈ lev _ _ _ _ at hl
    rw [mem_lev, mem_parLev] at hl
    have hs' : finE (D.sp.Y 0) (s * k * s⁻¹) ∈ St (finE (D.sp.Y 0) s * β) := by
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff]; exact hl.1.2.1
    refine hM' _ (hfin s k hf) hs' ?_
    rw [hfe, GlobalTheory.FrameConj.rTup_conj]
    exact hl.2
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  rw [hfe, GlobalTheory.FrameConj.rTup_conj] at hP' ⊢
  have hk₀ : k₀ ∈ levS (D.sp.Y 0) β Lz := by
    refine ⟨?_, ?_⟩
    · have := hfin s⁻¹ _ hκ
      rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
    · show finE (D.sp.Y 0) k₀ ∈ lev _ _ _ _
      rw [mem_lev, mem_parLev]
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS'
      exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hκS', fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ e3 _,
        fun PP hPP => absurd (e2 ▸ hPP) (Finset.notMem_empty _)⟩, hP'⟩
  refine (key hmem k₀ hk₀).trans ?_
  unfold levChi levFn
  simp only [e1, e2, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
end GlobalTheory.LevZeroChr
end
end
end
end
