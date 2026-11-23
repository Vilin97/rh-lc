module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.InstMainA
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffGp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerExtraStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MAvGood
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointsEqualEigenMatch

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigAgree

end GlobalTheory.EigAgree

theorem GlobalTheory.EigAgree.cast_ne_zero {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (f : D.what₂.Mt μ a) (hf : f ≠ 0) :
    (h ▸ f : D.what₂.Mt μ b) ≠ 0 := by
  subst h
  exact hf
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportLabel

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
namespace GlobalTheory.LabelTransport

theorem is_split_of_hk3_good_transport_label : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (sp : SplitPlace D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (sp.w.under (𝓞 D.host.F)) → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) sp.w d → ∃ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) ∧ (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) ∧ {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite ∧ ∀ (f : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) (c : ℂ), (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d, X.fn hμ j f (g * γ) = c • X.fn hμ j f g) → NG.heckeD (P.M.loc i).J Ds ((P.M.loc i).real (hj ▸ f)) = c • (P.M.loc i).real (hj ▸ f) := by
  intro _ hL D P X hA _ _ _ i hμ j hj sp _ _ hJ d hd
  classical
  obtain ⟨e, f, ϖ, α, -, hef, -, -, -, -, -, -, -, hRs, hR1, hR2⟩ := GlobalTheory.SphLabelOps.sphOp_rep hd
  have hsupp := suppF_iff_trivOutside D sp hA.hF _ _ (hA.PV j) (hA.stdV j) e f hef
  have hpre : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d,
      (hA.PV j).ψ (Formalism.IndefR.principalLevelFrame.pre (hA.PV j) γ) = γ := by
    intro γ hγ
    have h := (hA.PV j).onto γ (hR1 γ hγ).1
    rw [Formalism.IndefR.principalLevelFrame.pre, dite_eq_left h]
    exact h.choose_spec
  obtain ⟨Ds, d1, d2, d3, d4⟩ := coset_transport (hA.PV j).ψ (GlobalTheory.InertSph.Gv D.host.E D.R.nV sp.v)
    (Umax D.host.E D.R.nV) (P.M.loc i).J {k | k ∈ Formalism.L2.Theta.KsphC (Formalism.IndefR.Links.Vc D j) ∅ ∧ Formalism.IndefR.Mult.SuppF (Formalism.IndefR.Links.Vc D j) f k} α (GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d)
    (fun x => and_congr ((hA.stdV j).2 x).symm (hsupp x)) (fun k hk => (hA.PV j).onto k hk.1.1)
    (fun x hx => (hJ x hx).1) (Formalism.IndefR.principalLevelFrame.pre (hA.PV j))
    (fun γ hγ => ⟨hpre γ hγ, (hsupp _).1 (by rw [hpre γ hγ]; exact hRs γ hγ)⟩) (fun γ hγ => (hR1 γ hγ).2) hR2
  refine ⟨Ds, d1, d2, d3, fun φ c hc => ?_⟩
  have key : ∀ (k : ℕ) (ek : j.1 + 1 = k) (k1 : 1 ≤ k) (k2 : k ≤ D.R.m) (g : GAf D.host.E D.R.nV),
      ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d,
        (P.M (D.nd.mu i) k k1 k2).real (ek ▸ φ) (g * Formalism.IndefR.principalLevelFrame.pre (hA.PV j) γ) =
        c • (P.M (D.nd.mu i) k k1 k2).real (ek ▸ φ) g := by
    intro k ek k1 k2 g
    subst ek
    have hr := hA.real (D.nd.mu i) hμ j φ

    rw [hr g, ← map_smul, ← hc, map_sum]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hr, ← mul_assoc, map_mul, hpre γ hγ]
  have hty : (P.M.loc i).real (hj ▸ φ) ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]
    exact ⟨_, rfl⟩
  funext g
  refine (d4 _ ((P.M.loc i).real (hj ▸ φ)) (fun x κ hκ hκ' => ?_) g).trans (key _ hj _ _ g)
  have h := congrFun (hty.2 ⟨κ, hκ⟩) x
  rw [(hJ κ hκ').2 hκ, Units.val_one, one_smul] at h
  exact h
end GlobalTheory.LabelTransport
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportLabelStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.is_split_of_hk3_good_at_split_place : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (sp : SplitPlace D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (sp.w.under (𝓞 D.host.F)) → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) sp.w d → ∃ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) ∧ (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) ∧ {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite ∧ ∀ (f : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) (c : ℂ), (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d, X.fn hμ j f (g * γ) = c • X.fn hμ j f g) → NG.heckeD (P.M.loc i).J Ds ((P.M.loc i).real (hj ▸ f)) = c • (P.M.loc i).real (hj ▸ f) := by
  first | exact @_root_.GlobalTheory.LabelTransport.is_split_of_hk3_good_transport_label | exact _root_.GlobalTheory.LabelTransport.is_split_of_hk3_good_transport_label | (intros; apply _root_.GlobalTheory.LabelTransport.is_split_of_hk3_good_transport_label <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigAgree

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigAgree
end GlobalTheory.EigAgree
theorem GlobalTheory.EigAgree.eig_agree_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (x : D.nd.X i) (Q Q' : D.naut.AV i), D.naut.ptV i Q = some x → D.naut.ptV i Q' = some x → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → Pp ∉ D.nd.S i → Pp ∉ D.nd.Q i → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∀ f₁ f₂ : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f₁ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → (hj ▸ f₂ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q' → f₁ ≠ 0 → f₂ ≠ 0 → ∀ c₁ c₂ : ℂ, (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c₁ • X.fn hμ j f₁ g) → (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c₂ • X.fn hμ j f₂ g) → c₁ = c₂ := by
  intro hAF hL D P X hA h41 h7 htie i hμ j hj x Q Q' hQ hQ' Pp hG hS hPS hPQ d hd f₁ f₂ hf₁ hf₂ h0₁ h0₂ c₁ c₂ e1 e2
  have hsplit : IsSplitPl D.host Pp := GlobalTheory.OffBad.isSplitPl_of_isSplit D Pp hS
  have hloc : D.naut.locV i Q Pp = D.naut.locV i Q' Pp :=
    (((h41 i).2.1 Q Q' (by rw [hQ]; exact Option.some_ne_none x) (hQ.trans hQ'.symm)).2 Pp hPS hPQ).1 hsplit
  obtain ⟨sp, hspw, hJ⟩ := _root_.GlobalTheory.OffBad.offbad_alt hAF hL D P X hA h41 h7 htie i Pp hG hS
  subst hspw
  obtain ⟨Ds, hD1, hD2, hD3, hDt⟩ := _root_.GlobalTheory.T.is_split_of_hk3_good_at_split_place hAF hL D P X hA h41 h7 htie i hμ j hj sp hG hS hJ d hd
  have E1 := hDt f₁ c₁ e1
  have E2 := hDt f₂ c₂ e2
  have m1 : (P.M.loc i).real (hj ▸ f₁) ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have := P.H.av.typeV i Q ▸ hf₁
    exact this
  have m2 : (P.M.loc i).real (hj ▸ f₂) ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q') := by
    have := P.H.av.typeV i Q' ▸ hf₂
    exact this
  have t1 : (P.M.loc i).real (hj ▸ f₁) ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ :=
    (P.M.loc i).real_range ▸ LinearMap.mem_range_self _ _
  have t2 : (P.M.loc i).real (hj ▸ f₂) ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ :=
    (P.M.loc i).real_range ▸ LinearMap.mem_range_self _ _
  have n1 : (P.M.loc i).real (hj ▸ f₁) ≠ 0 := fun h =>
    GlobalTheory.EigAgree.cast_ne_zero hj f₁ h0₁ ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  have n2 : (P.M.loc i).real (hj ▸ f₂) ≠ 0 := fun h =>
    GlobalTheory.EigAgree.cast_ne_zero hj f₂ h0₂ ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  exact _root_.GlobalTheory.T.double_coset_support_at_split_alt hAF hL D P i Q Q' sp hJ Ds hD1 hD2 hD3
    (fun σ σ' h h' => _root_.UpperTheory.One.M.cls_eq_of_locV_eq' hL D P i Q Q' sp σ σ' h h' hloc) _ m1 t1 n1 _ m2 t2 n2 c₁ c₂ E1 E2
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigAgreeStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.points_equal_eigen_match_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (x : D.nd.X i) (Q Q' : D.naut.AV i), D.naut.ptV i Q = some x → D.naut.ptV i Q' = some x → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → Pp ∉ D.nd.S i → Pp ∉ D.nd.Q i → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∀ f₁ f₂ : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f₁ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → (hj ▸ f₂ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q' → f₁ ≠ 0 → f₂ ≠ 0 → ∀ c₁ c₂ : ℂ, (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c₁ • X.fn hμ j f₁ g) → (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c₂ • X.fn hμ j f₂ g) → c₁ = c₂ := by
  first | exact @_root_.GlobalTheory.EigAgree.eig_agree_alt | exact _root_.GlobalTheory.EigAgree.eig_agree_alt | (intros; apply _root_.GlobalTheory.EigAgree.eig_agree_alt <;> assumption)
end
end
end
