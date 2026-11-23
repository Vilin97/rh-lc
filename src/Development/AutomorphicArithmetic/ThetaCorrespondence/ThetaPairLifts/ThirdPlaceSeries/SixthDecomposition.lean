module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGalois
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecomposition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AdmissibleTemperedUnramified
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.HeckeCharacterEqualityOfRealisation

section

@[expose] public section

noncomputable section

namespace UpperTheory.GalN

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

def GalAwayN (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π →
    ∃ r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)),
      Continuous (fun g => ((r g : GL (Fin a) (Qbar (D.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i)))) ∧
      ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
        RelW D.nd D.naut (D.naut.wdOf i r w) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))

def IsStringRepN (D : D7) (i : D.nd.Loc) (p : Part D.naut.CG)
    (R : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i))) : Prop :=
  Continuous (fun g => ((R g : GL _ _) : Matrix (Fin p.a) (Fin p.a) (Qbar (D.nd.l i)))) ∧ IsSSRep R ∧
    ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut
      (D.naut.wdOf i R w) (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2))

theorem strN' {D : D7} {i : D.nd.Loc} {p : Part D.naut.CG} {R : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i))}
    (h : IsStringRepN D i p R) : IsStringRepN D i p R := h

theorem unr_part {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} {w : PlE H} :
    ∀ L : List (Part A.CG), A.unr (isoLoc N A L w) → ∀ p ∈ L, 1 ≤ p.d → A.unr (A.locG p.π w) := by
  intro L
  induction L with
  | nil =>
    intro _ _ hp _
    exact absurd hp List.not_mem_nil
  | cons q L ih =>
    intro hun p hp hd
    have h12 := (A.unr_sum (spehLoc N A q w) (isoLoc N A L w)).1 hun
    rcases List.mem_cons.1 hp with rfl | hp
    · have h := h12.1
      obtain ⟨d, hd'⟩ : ∃ d, p.d = d + 1 := ⟨p.d - 1, by omega⟩
      rw [GlobalTheory.StringDecomp.spehLoc_eq, hd', List.range_succ_eq_map, List.foldr_cons,
        A.unr_sum] at h
      exact (A.unr_tw (A.locG p.π w) _).1 h.1
    · exact ih h12.2 p hp hd

end UpperTheory.GalN
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.EtaPiece

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCGal

open Formalism.MainNotions.SumRepresentations.At GlobalTheory.TwistLG

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem galois_relation_away_from_l (hLP : TieLP N A) (hAut : TieAut N A) (hGal : TieGal N A) (hG : UpperTheory.GalS.AutomorphicGaloisAdmissible N A)
    {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) (hc : A.csd π) (m : ℤ)
    (hinf : ∀ τ, (A.infG π τ).Nodup ∧
      ∀ z ∈ A.infG π τ, ∃ n : ℤ, z + (((m : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    ∃ r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)), ContQ N i r ∧ IsSSRep r ∧ ∀ w, w ∉ placesOver H.E (N.l i) →
      UpperTheory.GalS.RelW N A (A.wdOf i r w) (A.lpTw (A.locG π w) ((m : ℝ) / 2 + (1 - (a : ℝ)) / 2)) := by
  obtain ⟨-, -, -, htw⟩ := hGal.2.2.2 i
  rcases Int.even_or_odd' m with ⟨k, hk | hk⟩ <;> subst hk
  ·
    have hralg : A.ralg π := (A.ralg_def π).2 fun τ => ⟨(hinf τ).1, fun z hz => by
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      exact ⟨n - k, by push_cast at hn ⊢; linear_combination hn⟩⟩
    obtain ⟨ρ1, c1, ss1, away1, -⟩ := (hG i).1 a ha π hc hralg
    obtain ⟨χA, cA, awayA, -⟩ := (hG i).2.2 A.etaT (1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut 0 τ).1 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    obtain ⟨χB, cB, awayB, -⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) - 1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut (k - 1) τ).2 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    let ρ2 := twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χA)
    have c2 : ContQ N i ρ2 := cont_twGL ρ1 χA c1 cA
    refine ⟨twGL ρ2 (Matrix.GeneralLinearGroup.det.comp χB), cont_twGL ρ2 χB c2 cB,
      isSSRep_twGL _ _ (isSSRep_twGL _ _ ss1), fun w hw => ?_⟩
    rw [(htw a ρ2 χB c2 cB).2.1 w (Or.inl hw) (Or.inl hw), (htw a ρ1 χA c1 cA).2.1 w (Or.inl hw) (Or.inl hw),
      awayA w hw, awayB w hw]
    have k1 := ((away1 w hw).char hLP (A.lpTw (A.locG A.etaT w) (1 / 2)) (by rw [A.lpDim_tw, A.locG_dim])
      ((A.unr_tw _ _).2 (A.etaT_unr w))).char hLP (A.lpTw (A.locG A.etaTinv w) ((k : ℝ) - 1 / 2))
      (by rw [A.lpDim_tw, A.locG_dim]) ((A.unr_tw _ _).2 (A.etaTinv_def w).1)
    rw [param_int N A hLP] at k1
    convert k1 using 2
    push_cast
    ring
  ·
    have hcsd : A.csd (A.tw π A.etaT) := A.csd_tw π A.etaT hAut.1.1 hc
    have hralg : A.ralg (A.tw π A.etaT) := (A.ralg_def _).2 fun τ => by
      obtain ⟨e, he⟩ := Multiset.card_eq_one.mp (A.infG_card A.etaT τ)
      rw [A.infG_tw π A.etaT τ e he]
      refine ⟨(hinf τ).1.map (add_left_injective e), fun y hy => ?_⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      obtain ⟨j, hj⟩ := (eta_alg N A hAut 0 τ).1 e (by rw [he]; exact Multiset.mem_singleton_self e)
      exact ⟨n + j - k - 1, by push_cast at hn hj ⊢; linear_combination hn + hj⟩
    obtain ⟨ρ1, c1, ss1, away1, -⟩ := (hG i).1 a ha _ hcsd hralg
    obtain ⟨χ1, cχ, awayχ, -⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) + 1 / 2) (eta_alg N A hAut k · |>.2)
    refine ⟨twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χ1), cont_twGL ρ1 χ1 c1 cχ, isSSRep_twGL _ _ ss1,
      fun w hw => ?_⟩
    rw [(htw a ρ1 χ1 c1 cχ).2.1 w (Or.inl hw) (Or.inl hw), awayχ w hw]
    have k1 := (away1 w hw).char hLP (A.lpTw (A.locG A.etaTinv w) ((k : ℝ) + 1 / 2))
      (by rw [A.lpDim_tw, A.locG_dim]) ((A.unr_tw _ _).2 (A.etaTinv_def w).1)
    rw [param_twist N A hLP] at k1
    convert k1 using 2
    push_cast
    ring

end GlobalTheory.BCGal
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StringDecompHolds

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
section Alg
variable {Γ : Type} [Group Γ] {K : Type} [Field K]
end Alg
end GlobalTheory.StringDecomp
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
section Frob
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
end Frob
end GlobalTheory.StringDecomp
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
section Eps
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
end Eps
end GlobalTheory.StringDecomp
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
theorem exists_stringRep_alt_alt (D : D7) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (i : D.nd.Loc) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)) (hBC : IsBCV D.nd D.naut i P Pa) (p : Part D.naut.CG) (hp : p ∈ Pa) :
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)), UpperTheory.GalS.IsStringRepN D i p ρ := by
  obtain ⟨⟨⟨hLP, hAut, hGal⟩, -, -, hG, -, -, -⟩, -⟩ := hA.1
  obtain ⟨ha, hd, hc⟩ := hBC.1 p hp
  have hw := GlobalTheory.BCGal.galois_relation_away_from_l D.nd D.naut i hLP hAut hGal (_root_.UpperTheory.GalS.weak' hG) ha p.π hc
    ((p.d : ℤ) - 1 + p.a - D.R.nV) fun τ => by
    have hW : (D.naut.infWt i τ).Nodup ∧
        ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
      rw [D.nbc.embAV_inf i P]
      exact D.nbc.infW_alg _ _ τ
    have hle : (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ D.naut.infWt i τ := by
      rw [← hBC.2.2.2.2.2 τ]
      refine le_trans (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ ?_)
        (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
      exact List.mem_map.2 ⟨0, by simp; exact ⟨0, by omega, by simp⟩, by simp⟩
    refine ⟨(Multiset.nodup_of_le hle hW.1).of_map _, fun z hz => ?_⟩
    obtain ⟨n, hn⟩ := hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz))
    exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
  obtain ⟨ρ, hcont, hss, hwd⟩ := hw
  refine ⟨ρ, hcont, hss, fun w hwl => ?_⟩
  convert hwd w hwl using 2
  push_cast
  ring_nf
theorem stringDecomp_holds_alt_alt :
    ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ r, GoodR D.nd i r →
    ∃ R : ∀ k : Fin Pa.length, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)),
      (∀ k, UpperTheory.GalS.IsStringRepN D i (Pa.get k) (R k)) ∧
      ∀ g, ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
        ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
          (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
            ((epsQ D i g)⁻¹ ^ a) := by
  intro D hA i x P Pa hx hBC r hr
  have hC := hA.1.1.2.2.2.2.2.2.2.2.1
  have hex : ∀ p : Part D.naut.CG, ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)),
      p ∈ Pa → UpperTheory.GalS.IsStringRepN D i p ρ := by
    intro p
    by_cases hp : p ∈ Pa
    · obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.StringDecomp.exists_stringRep_alt_alt D hA i P Pa hBC p hp
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose Rp hRp using hex
  refine ⟨fun k => Rp (Pa.get k), fun k => hRp _ (List.get_mem Pa k), ?_⟩
  have hrk : rkL Pa = D.R.nV := (rkL_eq Pa).trans hBC.2.2.1
  have hcL := cont_listRep Rp _ (cont_epsQU_inv D.nd D.naut i) Pa (fun p hp => (hRp p hp).1)
  obtain ⟨ρ', hρ'⟩ := exists_cast hrk (listRep Rp (epsQU D.nd D.naut i)⁻¹ Pa)
  have hQ := GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois D i x (r x) (hr x)
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) : Set (PlE D.host)).Finite :=
    ((placesOver_finite' D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).union (D.nd.S i).finite_toSet).union
      (D.nd.Q i).finite_toSet
  have key := GlobalTheory.charpoly_eq_of_eqOn_dense
    (fun g => ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))))
    (fun g => ((ρ' g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))))
    hQ.1 (hρ'.1 hcL) _ (dense_iff_closure_eq.2 (hC _ hfin)) (by
      rintro σ ⟨w, hw, hsp, B, hB, hσ⟩
      simp only [Set.mem_union, not_or, Finset.mem_coe] at hw
      have hso : SplitOut D.nd i w := ⟨hsp, hw.1.1, hw.1.2, hw.2⟩
      show _ = _
      rw [hQ.2.2 w hso B σ hB hσ, hρ'.2 σ, charpoly_listRep]
      apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
      rw [Polynomial.map_map, show (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) =
        ((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).comp (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
        from rfl, D.naut.pt_loc i P x hx w hso, ← hBC.2.2.2.1 w hsp]
      exact (iso_poly i w hso.2.1 B σ hB hσ Rp _ _ (epsQU_frob D.nd D.naut i hso.2.1 hB hσ) Pa
        (fun p hp => (hRp p hp).1) (fun p hp => ((hRp p hp).2.2 w hso.2.1).eq_of_unr ((D.naut.unr_tw _ _).2
          (UpperTheory.GalN.unr_part Pa (iso_unr i hBC w hso) p hp (hBC.1 p hp).2.1))) (iso_unr i hBC w hso)).symm)
  intro g
  rw [key g, hρ'.2 g, charpoly_listRep, epsQU_inv_val, ← prod_get]
  rfl
end GlobalTheory.StringDecomp
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthDecomposition

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.centred_string_decomposition : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt := by
  first | exact @_root_.GlobalTheory.StringDecomp.stringDecomp_holds_alt_alt | exact _root_.GlobalTheory.StringDecomp.stringDecomp_holds_alt_alt | (intros; apply _root_.GlobalTheory.StringDecomp.stringDecomp_holds_alt_alt <;> assumption)
end
end
end
