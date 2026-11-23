module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectors
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerTerStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectorsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_irreducible_fixed_vectors : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ), K ≤ KO (s.w.adicCompletion L) (Fin n) → (∀ h ∈ KOne (s.w.adicCompletion L) (Fin n), h ∈ K ∧ θ h = 1) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∃ y : σ.V, y ≠ 0 ∧ ∀ h ∈ K, σ.ρ h y = θ h • y := by
  first | exact @GlobalTheory.EigLocal.exists_eigen_local | exact GlobalTheory.EigLocal.exists_eigen_local | (intros; apply GlobalTheory.EigLocal.exists_eigen_local <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeVecBlockCharFixedPlace

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
open Filter Topology
namespace GlobalTheory.TypeBlockFix
variable {F : Type} [Field F] [NumberField F] {F' : Type} [Field F'] [NumberField F']
section loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end loc
end GlobalTheory.TypeBlockFix
namespace GlobalTheory.TypeBlockFix
open ValuativeRel
end GlobalTheory.TypeBlockFix
namespace GlobalTheory.TypeBlockFix
open Filter Topology
end GlobalTheory.TypeBlockFix
open GlobalTheory.TypeBlockFix in
theorem GlobalTheory.typeVec_blockChar_fixedPlace_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  intro hL D P S hS i k v s hw hsw _hT c hc hci Q
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp; omega⟩
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i Q)
  rw [P.H.av.typeV] at hy
  have hfT : (P.M.loc i).real y ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
  refine ⟨(P.M.loc i).real y, hy, fun h0 => hy0 ((P.M.loc i).real_inj (h0.trans (map_zero _).symm)), ?_⟩
  obtain ⟨ψ₀, ξ, hψ, hξ, hLv⟩ := P.H.level.uni i j hj k v s hsw
  intro x hx hblk
  set G := s.loc D.R.nV x with hG
  set h := Matrix.GeneralLinearGroup.map c.toRingHom G with hh
  have hent : ∀ a b, h.val a b = c (G.val a b) := fun a b => rfl
  have hient : ∀ a b, (h⁻¹).val a b = c ((G⁻¹).val a b) := by
    intro a b; rw [hh, ← map_inv]; rfl
  have hle : ∀ y, ValuativeRel.valuation _ (c y) ≤ 1 → Valued.v y ≤ 1 := fun y hy' =>
    (v_map_le_one_iff _ _ c hc y).1 ((complRel_le_one _ _).1 hy')
  have hlt : ∀ y, ValuativeRel.valuation _ (c y) < 1 → Valued.v y < 1 := fun y hy' =>
    (v_map_lt_one_iff _ _ c hc y).1 ((complRel_lt_one _ _).1 hy')
  have hI : ∀ a b, Valued.v (G.val a b) ≤ 1 := fun a b =>
    hle _ (by rw [← hent]; exact GlobalTheory.BlockType.val_le_one_of_mem_KO hblk.1 a b)
  have hI' : ∀ a b, Valued.v ((G⁻¹).val a b) ≤ 1 := fun a b =>
    hle _ (by rw [← hient]; exact GlobalTheory.BlockType.val_le_one_of_mem_KO ((KO _ _).inv_mem hblk.1) a b)
  have hcol : ∀ a (b : Fin D.R.nV), b.val < D.R.r → a ≠ b → Valued.v (G.val a b) < 1 := by
    intro a b hb hab
    refine hlt _ ?_
    have := hblk.2 a ⟨b.val, hb⟩
    rw [← hent]
    have e : b = Fin.castAdd D.R.t ⟨b.val, hb⟩ := Fin.ext rfl
    rw [← e] at this
    change ValuativeRel.valuation _ (h.val a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) _) a b) < 1 at this
    rw [Matrix.one_apply_ne hab, sub_zero] at this
    exact this
  have hdiag : ∀ (b : Fin D.R.nV), b.val < D.R.r → Valued.v (G.val b b - 1) < 1 := by
    intro b hb
    refine hlt _ ?_
    have := hblk.2 b ⟨b.val, hb⟩
    have e : b = Fin.castAdd D.R.t ⟨b.val, hb⟩ := Fin.ext rfl
    rw [← e] at this
    change ValuativeRel.valuation _ (h.val b b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) _) b b) < 1 at this
    rw [Matrix.one_apply_eq, hent] at this
    rwa [map_sub, map_one]
  have hpara : NG.ParaRT s D.R.r G := by
    refine ⟨mem_GLint_of_entries _ G (fun a b => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hI a b))
      (fun a b => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hI' a b)), ?_⟩
    · intro a b ha hb
      exact hcol a b hb (fun e => by rw [e] at ha; omega)
  have huni : NG.UniRT s D.R.r G := by
    refine ⟨hpara, fun a b ha hb => ⟨fun hab => hcol a b hb (fun e => by rw [e] at hab; omega), fun e => ?_⟩⟩
    subst e; exact hdiag a ha
  have hmem : x ∈ (P.M.loc i).J := (hLv.mem x hx).2 huni
  have hcdet : c (NG.detDD s D.R.r G) = (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {a : Fin D.R.nV // D.R.r ≤ a.val} :=
      { toFun := fun b => ⟨Fin.natAdd D.R.r b, by simp⟩
        invFun := fun a => ⟨a.1.val - D.R.r, by have h1 : a.1.val < D.R.r + D.R.t := a.1.2; omega⟩
        left_inv := fun b => by ext; simp
        right_inv := fun a => by ext; simp; have := a.2; omega }
    rw [NG.detDD, show c (Matrix.of fun a b : {x : Fin D.R.nV // D.R.r ≤ x.val} => G.val a.1 b.1).det =
      c.toRingHom (Matrix.of fun a b : {x : Fin D.R.nV // D.R.r ≤ x.val} => G.val a.1 b.1).det from rfl,
      RingHom.map_det, ← Matrix.det_submatrix_equiv_self e]
    congr 1
  have hdet : NG.detDD s D.R.r G ≠ 0 := by
    intro h0
    exact (det_ne_zero_of_mem_blockGrp _ _ _ _ hblk) (hcdet.symm.trans (by rw [h0, map_zero]))
  refine (hfT.2 ⟨x, hmem⟩).trans ?_
  congr 1
  rw [hLv.chr x hmem hx (Units.mk0 _ hdet) rfl]
  have hsd : Valued.v (NG.supDiag s D.R.r G) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    split_ifs with hab
    · exact hcol a b hab.2 (fun e => by rw [e] at hab; omega)
    · simp
  rw [hψ.1 _ hsd, one_mul, comp_agree _ s _ ξ _ c hc hci hξ (hS.mu i s.w hw j hj)]
  exact (GlobalTheory.BlockType.blockChar_eq _ _ _ hcdet).symm
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeVecBlockCharFixedPlaceStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.split_place_completion_iso_tame_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  exact _root_.GlobalTheory.typeVec_blockChar_fixedPlace_alt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisFurther

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TypeBlockPf
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ i w hw, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → TypeBlock S i w hw := by
  intro hL D P S hT i w hw ⟨k, hk⟩ htame
  refine ⟨htame, fun Q => ?_⟩
  obtain ⟨s, rfl⟩ := splitAt D w hw
  obtain ⟨c, T, hc, hcs, -, -, -⟩ := hT.rep i s hw Q
  have hf : ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧
      ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x →
        Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t →
        NG.rt D.host.E D.R.nV x f =
          blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
    obtain ⟨v, e | e⟩ := GlobalTheory.DimPartsCompare.cover k s.w hk
    · exact _root_.GlobalTheory.T.split_place_completion_iso_tame_alt hL D P S hT i k v s hw e htame c hc hcs Q
    · exact _root_.GlobalTheory.T.conjugate_place_completion_iso_tame_alt hL D P S hT i k v s hw e htame c hc hcs Q
  obtain ⟨f, hfS, hf0, hfe⟩ := hf
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.T.local_irreducible_fixed_vectors D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _
    (hT.rep i s hw Q) c hc hcs (blockGrp _ D.R.r D.R.t) (blockChar (S i s.w hw).mu) (fun h hh => hh.1)
    (fun h hh => ⟨kOne_le_blockGrp _ _ hh, blockChar_kOne _ htame hh⟩) f hfS hf0 hfe
  exact ⟨y, hy0, isBlockVec_of _ _ _ hy⟩
end GlobalTheory.TypeBlockPf
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisFurtherStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.type_block_of_tame_at_split_place : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ i w hw, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → TypeBlock S i w hw := by
  first | exact @_root_.GlobalTheory.TypeBlockPf.main_alt_alt | exact _root_.GlobalTheory.TypeBlockPf.main_alt_alt | (intros; apply _root_.GlobalTheory.TypeBlockPf.main_alt_alt <;> assumption)
end
end
end
