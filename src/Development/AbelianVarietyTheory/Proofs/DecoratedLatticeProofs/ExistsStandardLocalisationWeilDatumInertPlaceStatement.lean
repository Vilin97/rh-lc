module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralFramePointOfInertHalfLatticePointStatement
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertSupportedPointIntegralFramesMemLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupActionInertSupportedPointsFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionaryStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplecticFormInertSupportedPointsAntidiagonalStatement
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepLatticeVacuumMemSpanInertTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFix
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalCharacterConjugationInverse

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

theorem secW_cA (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (hc : IsConjAt D.sp.cm.sig h c)
    (z : w.adicCompletion D.host.E) : secW hw h (c z) = cA D (secW hw h z) := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.LFun.InertChart.complEquiv hw h).surjective z
  have e1 : c (GlobalTheory.LFun.InertChart.complEquiv hw h y) =
      GlobalTheory.LFun.InertChart.complEquiv hw h (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig y) := hc y
  rw [e1]
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _) =
    cA D (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _))
  rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  exact (GlobalTheory.EmbChart.sigR_tensAt v _ y).symm

theorem thW_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsConjAt D.sp.cm.sig h c → (∀ z, c (c z) = z) → ∀ z, thW ψ hw h (k * c k) (c z) * thW ψ hw h (k * c k) z = 1 := by
  intro D ψ v w hw h c k hc hcc z
  have h1 : secW hw h (k * c k * c z) = cA D (secW hw h (k * c k * z)) := by
    rw [← secW_cA D hw h c hc]
    congr 1
    rw [map_mul c, map_mul c, hcc, mul_comm k (c k)]
  rw [thW_apply, thW_apply, h1, ← GlobalTheory.DualPairCheck.trace_cA (_ * cA D _), RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA,
    GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg, neg_mul, LinearMap.map_neg,
    ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

end GlobalTheory.InertFrameLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalCharacterConjugationInverseStatement

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc


theorem _root_.GlobalTheory.T.inert_place_local_character_conjugation_inverse : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsConjAt D.sp.cm.sig h c → (∀ z, c (c z) = z) → ∀ z, thW ψ hw h (k * c k) (c z) * thW ψ hw h (k * c k) z = 1 := by
  first | exact @GlobalTheory.InertFrameLoc.thW_conj | exact GlobalTheory.InertFrameLoc.thW_conj | (intros; apply GlobalTheory.InertFrameLoc.thW_conj <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegersStatement

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc


theorem _root_.GlobalTheory.T.inertPlace_localTraceCharacter_conductor_integers : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsStdChar D ψ (-1) → IsConjAt D.sp.cm.sig h c → IsUnramInv ϖ c (qV D.host.F v) → GlobalTheory.InertLoc.IsGen D w k → ∀ z, (∀ u ∈ Formalism.UG.intL (w.adicCompletion D.host.E), thW ψ hw h (k * c k) (z * u) = 1) ↔ z ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
  first | exact @GlobalTheory.InertFrameLoc.thW_cond | exact GlobalTheory.InertFrameLoc.thW_cond | (intros; apply GlobalTheory.InertFrameLoc.thW_cond <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuedTwoEqOneInertPlaceCmField

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertTwo

theorem valued_two_eq_one : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → Valued.v (2 : w.adicCompletion D.host.E) = 1 := by
  intro D v w hi
  have hu : w.under (𝓞 D.host.F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hi w).2 rfl
  have hc : Formalism.DivisionValues.conjPl w = w := GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hi hu
  have h : ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h2 => GlobalTheory.CoreThree.conj_ne_of_two w h2 hc
  rw [← map_ofNat (algebraMap D.host.E (w.adicCompletion D.host.E)) 2, GlobalTheory.Idele.valued_algebraMap,
    ← map_ofNat (algebraMap (𝓞 D.host.E) D.host.E) 2, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 h

end GlobalTheory.InertTwo
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuedTwoEqOneInertPlaceCmFieldStatement

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc


theorem _root_.GlobalTheory.T.valued_two_eq_one_inertPlace_cmField : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → Valued.v (2 : w.adicCompletion D.host.E) = 1 := by
  first | exact @GlobalTheory.InertTwo.valued_two_eq_one | exact GlobalTheory.InertTwo.valued_two_eq_one | (intros; apply GlobalTheory.InertTwo.valued_two_eq_one <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardLocalisationWeilDatumInertPlace

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertFrameLoc



theorem exists_isStd_inert : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ (∀ m : M, IsThetaFunO ψ S T m) ∧ ∀ x, ∃ u : WO S T, ∀ m : M, ((ρ x m : M) : WO S T → ℂ) = heisO ψ S T u m := by
  intro D ψ S T χS χT om hW v w h hw uS uT c ϖ eS eT hU hcS hcT f hf hf0
  obtain ⟨hconj, ⟨aS, haS, gS, eSa⟩, kSc⟩ := hcS
  obtain ⟨-, ⟨aT, haT, gT, eTa⟩, kTc⟩ := hcT
  obtain ⟨k, hk⟩ := GlobalTheory.InertLoc.exists_isGen D w
  have h2 := GlobalTheory.T.valued_two_eq_one_inertPlace_cmField D v w hw
  obtain ⟨δ, ψ', hδ, p1, p2, p3⟩ := GlobalTheory.InertLoc.exists_delta_psi hU h2 (thW ψ hw h (k * c k))
    (GlobalTheory.T.inert_place_local_character_conjugation_inverse D ψ v w hw h c k hconj hU.1) (GlobalTheory.T.inertPlace_localTraceCharacter_conductor_integers D ψ v w hw h c ϖ k hW.std hconj hU hk)
  have hadd : ∀ x y, uPt hw h k aS aT (x + y) = uPt hw h k aS aT x + uPt hw h k aS aT y := uPt_add
  have hMθ : spanT ψ (uPt hw h k aS aT) f ≤ GlobalTheory.FinWeilO.thetaSub ψ S T := Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    exact GlobalTheory.FinTranslate.isTheta_heisO_fin hW.std.1 (map_infPart_uPt (hw := hw) (h := h) (k := k) (aS := aS) (aT := aT) x) hf.1)
  let π : GU c S.rank × GU c T.rank →* Module.End ℂ (WO S T → ℂ) :=
    om.comp (((embV S v).comp eS.symm.toMonoidHom).prodMap ((embV T v).comp eT.symm.toMonoidHom))
  have hπ : ∀ p m, π p m = om (embV S v (eS.symm p.1), embV T v (eT.symm p.2)) m := fun _ _ => rfl
  have hstab : ∀ p, ∀ m ∈ spanT ψ (uPt hw h k aS aT) f, π p m ∈ spanT ψ (uPt hw h k aS aT) f := fun p m hm =>
    mem_spanT_of (fun y => by
      rw [hπ, hW.om_heis _ _ _ _ hf.1, GlobalTheory.T.local_group_action_inert_supported_points_frames]
      exact heis_mem_spanT hadd _
        (GlobalTheory.T.weilRep_latticeVacuum_mem_span_inertTranslates D ψ S T χS χT om hW v w hw h uS uT c ϖ k aS aT hU hconj hk haS haT gS gT f hf _ _)) hm
  have hint2 : (2⁻¹ : w.adicCompletion D.host.E) ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := (GlobalTheory.SphTheta.half h2).2
  have hvac : ∀ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E),
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) → heisO ψ S T (uPt hw h k aS aT x) f = f := fun x hx => by
    have h1 := hf.2.1 _ (GlobalTheory.T.inert_supported_point_integral_frames_mem_lattice D v w hw h S T k aS aT hk haS haT ((2⁻¹ : w.adicCompletion D.host.E) • x)
      fun i j => mul_mem hint2 (hx i j))
    rwa [two_nsmul, ← uPt_add, GlobalTheory.InertLoc.half_add_half] at h1
  have hfM : f ∈ spanT ψ (uPt hw h k aS aT) f := self_mem_spanT uPt_zero
  have dict := GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary D v w h
  have unr : ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → GlobalTheory.Hk3.UnrPl w χ := fun χ hχ =>
    dict.2.1 χ fun w' hw' => by rw [(GlobalTheory.LFun.InertChart.under_eq_iff hw w').1 hw']; exact hχ
  have hfix := GlobalTheory.ConjVacFix.vacFix_of_unrPl ψ S T χS χT om w hW (unr χS uS) (unr χT uT)
  refine ⟨δ, ψ', spanT ψ (uPt hw h k aS aT) f, rhoT ψ (uPt hw h k aS aT) f hadd, omT ψ (uPt hw h k aS aT) f π hstab,
    ⟨f, hfM⟩, ⟨⟨hU, GlobalTheory.InertLoc.odd_of_v_two hU h2, antiG_mem _, antiG_mem _, antiJ_herm c _, antiJ_herm c _, hδ, p1, p2,
      ?_, fun x y => ?_, ?_, fun g g' x => ?_, fun g g' hg hg' s hs => ?_⟩,
      fun e => hf0 (congrArg Subtype.val e), fun x hx => Subtype.ext (hvac x hx), span_rhoT_eq_top hadd hfM⟩,
    rfl, fun _ _ _ => rfl, fun m => hMθ m.2, fun x => ⟨uPt hw h k aS aT x, fun _ => rfl⟩⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [coe_rhoT, uPt_zero, GlobalTheory.SplitScalar.heisO_zero]
    rfl
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [Module.End.mul_apply, coe_rhoT, coe_rhoT, GlobalTheory.SplitScalar.heisO_heisO, LinearMap.smul_apply, Submodule.coe_smul,
      coe_rhoT, ← uPt_add, GlobalTheory.T.symplectic_form_inert_supported_points_antidiagonal D ψ v w hw h S T c k aS aT hconj gS gT, ← p3]
    simp only [GlobalTheory.Hk3.locH, one_mul]
  · refine eq_top_iff.2 ((span_rhoT_eq_top hadd hfM).symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨x, rfl⟩
    exact ⟨x, ⟨f, hfM⟩, fun y hy => Subtype.ext (hvac y hy), rfl⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    have hinv : (eS.symm g)⁻¹ = eS.symm g⁻¹ := (map_inv eS.symm g).symm
    show π (g, g') (heisO ψ S T (uPt hw h k aS aT x) m) = heisO ψ S T (uPt hw h k aS aT _) (π (g, g') m)
    rw [hπ, hπ, hW.om_heis _ _ _ _ (hMθ m.2), GlobalTheory.T.local_group_action_inert_supported_points_frames]
    refine congrArg (fun z => heisO ψ S T (uPt hw h k aS aT z) (om (embV S v (eS.symm g), embV T v (eT.symm g')) m)) ?_
    rw [← eTa, hinv, ← eSa]
    erw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  · refine Subtype.ext (hfix _ ⟨hMθ s.2, fun e e' he uu huu hh => ?_⟩ _
      ((dict.2.2.1 S _).2 ⟨eS.symm g, (kSc _).2 ((eS.apply_symm_apply g).symm ▸ GlobalTheory.SphTheta.mem_KU_iff.2 hg), rfl⟩) _
      ((dict.2.2.1 T _).2 ⟨eT.symm g', (kTc _).2 ((eT.apply_symm_apply g').symm ▸ GlobalTheory.SphTheta.mem_KU_iff.2 hg'), rfl⟩))
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.exists_integralFramePoint_of_inertHalf_latticePoint D v w hw h S T k aS aT hk haS haT e e' he uu huu hh
    exact congrArg Subtype.val (hs x hx)

end GlobalTheory.InertFrameLoc

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardLocalisationWeilDatumInertPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_standardLocalisation_weilDatum_inertPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ (∀ m : M, IsThetaFunO ψ S T m) ∧ ∀ x, ∃ u : WO S T, ∀ m : M, ((ρ x m : M) : WO S T → ℂ) = heisO ψ S T u m := by
  first | exact @GlobalTheory.InertFrameLoc.exists_isStd_inert | exact GlobalTheory.InertFrameLoc.exists_isStd_inert | (intros; apply GlobalTheory.InertFrameLoc.exists_isStd_inert <;> assumption)
end
end
