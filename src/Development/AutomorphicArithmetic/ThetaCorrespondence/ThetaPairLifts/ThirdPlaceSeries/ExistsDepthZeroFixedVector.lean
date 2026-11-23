module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Formalism.SharpRestriction.LevelLetterCocycles.FourthHypothesisOfLifting
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
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
public import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentIsCentralIdempotent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreLastStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharacterEqInvAtTransposeInvLowerBlockDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoric
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceUnitsCharacterEqOfAgreeOnField
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharOfLowerRightBlockDetEventuallyEqOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockType

theorem blockChar_eventually_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ → ∃ U : Set (GL (Fin (r + t)) k), IsOpen U ∧ (1 : GL (Fin (r + t)) k) ∈ U ∧ ∀ g ∈ U, GlobalTheory.BlockType.blockChar χ g = 1 := by
  intro k _ _ _ _ r t χ hχ
  have hval : Topology.IsOpenEmbedding (Units.val : kˣ → k) := IsOpenUnits.isOpenEmbedding_unitsVal
  have hV : IsOpen ((Units.val : kˣ → k) '' (χ.ker : Set kˣ)) := hval.isOpenMap _ hχ
  have hd : Continuous fun g : GL (Fin (r + t)) k =>
      (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det :=
    (Units.continuous_val.matrix_submatrix _ _).matrix_det
  refine ⟨(fun g : GL (Fin (r + t)) k => (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ⁻¹'
      ((Units.val : kˣ → k) '' (χ.ker : Set kˣ)), hV.preimage hd, ?_, ?_⟩
  · refine ⟨1, χ.ker.one_mem, ?_⟩
    simp only [Units.val_one]
    rw [Matrix.submatrix_one _ (Fin.natAdd_injective t r), Matrix.det_one]
  · rintro g ⟨u, hu, he⟩
    rw [blockChar_eq χ g u he, MonoidHom.mem_ker.1 hu, Units.val_one]

end GlobalTheory.BlockType
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharOfLowerRightBlockDetEventuallyEqOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.charOfLowerRightBlockDet_eventually_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ → ∃ U : Set (GL (Fin (r + t)) k), IsOpen U ∧ (1 : GL (Fin (r + t)) k) ∈ U ∧ ∀ g ∈ U, GlobalTheory.BlockType.blockChar χ g = 1 := by
  first | exact @GlobalTheory.BlockType.blockChar_eventually_one | exact GlobalTheory.BlockType.blockChar_eventually_one | (intros; apply GlobalTheory.BlockType.blockChar_eventually_one <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreTail

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.TypeVecEig
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ F ∈ D.naut.typeV i PI, ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  intro hL D P S hT i PI k v s hw hsw c hcont hci F _hF x hx hh
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp only; omega⟩
  obtain ⟨ψ₀, ξ, hψ, hξ, hlev⟩ := P.H.level.uni i j hj k v s hsw
  have hcv := GlobalTheory.SplitConjVal.valuation_eq s c hcont hci
  obtain ⟨h1, h2⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x) hh
  obtain ⟨i1, -⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x)⁻¹
    (by
      have := (GlobalTheory.BlockType.blockGrp _ _ _).inv_mem hh
      convert this using 1
      exact map_inv (Matrix.GeneralLinearGroup.map (n := Fin (D.R.r + D.R.t)) c.toRingHom) _)
  have huni : NG.UniRT s D.R.r (s.loc D.R.nV x) := by
    refine ⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩,
      fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h1 a b)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (i1 a b)
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at ha; omega
      · rwa [sub_zero] at this
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at hlt; omega
      · rwa [sub_zero] at this
    · subst he
      have := h2 a a ha
      split_ifs at this with e
      · exact this
      · exact absurd rfl e
  have hxJ : x ∈ (P.M.loc i).J := (hlev.mem x hx).2 huni
  have hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hrt := hTS.2 ⟨x, hxJ⟩
  let h : GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E) :=
    Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)
  have hh' : h ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := hh
  have hdet := GlobalTheory.BlockConjDet.val_det_mul_sub_one_lt hh'
  have hne2 : (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub, Valuation.map_neg, map_one] at hdet
    exact lt_irrefl _ hdet
  have hc_det : c (NG.detDD s D.R.r (s.loc D.R.nV x)) =
      (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {y : Fin D.R.nV // D.R.r ≤ y.val} :=
      { toFun := fun a => ⟨Fin.natAdd D.R.r a, by simp⟩
        invFun := fun y => ⟨y.1.val - D.R.r, by
          have h1 := y.1.2; have h2 := y.2; change y.1.val < D.R.r + D.R.t at h1; omega⟩
        left_inv := fun a => by ext; simp
        right_inv := fun y => by ext; simp; have := y.2; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e]
    exact c.toRingHom.map_det _
  have hF0 : NG.detDD s D.R.r (s.loc D.R.nV x) ≠ 0 := fun h0 => hne2 (by rw [← hc_det, h0, map_zero])
  let u := Units.mk0 _ hF0
  have hchr := hlev.chr x hxJ hx u rfl
  have hsup : ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV x)) = 1 := hψ.1 _ (by
    unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · have := h2 p q h.2
      split_ifs at this with e
      · rw [e] at h; omega
      · rwa [sub_zero] at this
    · rw [map_zero]; exact zero_lt_one)
  have hμ := hT.mu i s.w hw j hj
  have hξμ := GlobalTheory.ConjDense.eq_of_agree s c hcont hci (S i s.w hw).mu ξ hμ.1 hξ.1
    (fun k => by rw [hξ.2 k, hμ.2 k]) u
  have hbc : GlobalTheory.BlockType.blockChar (S i s.w hw).mu h =
      (((S i s.w hw).mu (Units.map c.toMonoidHom u) : ℂˣ) : ℂ) :=
    GlobalTheory.BlockType.blockChar_eq _ _ _ (by rw [← hc_det]; rfl)
  change _ = GlobalTheory.BlockType.blockChar (S i s.w hw).mu h • _
  rw [hbc, ← hξμ, hrt, hchr, hsup, one_mul]
end GlobalTheory.TypeVecEig
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreTailStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.completion_iso_split_place_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ F ∈ D.naut.typeV i PI, ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  exact _root_.GlobalTheory.TypeVecEig.main_alt_alt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VectorAtSplitPlace

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DzVecLoc
theorem vector_at_split_place (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (hC : GlobalTheory.HeightCounting.Up.CenLoc D P.M) (S : Reading P.T)
    (hT : _root_.GlobalTheory.NPin.IsFaithfulReading P S) (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E)
    (hw : IsSplitPl D.host s.w) (hs : s.w = D.naut.plGw k v) (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (hρ : CategoryTheory.Simple ρ) (hocc : PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ)) :
    ∃ x, IsBlockVec (S i s.w hw).mu ((S i s.w hw).rep PI).π x ∧ NotKilled ((S i s.w hw).rep PI).π (idemOf D k ρ) x := by
  classical
  have hrep := hT.rep i s hw PI
  rcases hrep with ⟨c, T, hc, hcs, -, -, -⟩
  obtain ⟨F, hF, hne⟩ := hocc
  set z := idemOf D k ρ with hz
  have hzc : ∀ b, z * b = b * z := by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exact (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).2
  have hcen := GlobalTheory.SeriesSupportTest.atPlace_central D k v z hzc
  obtain ⟨L, hLift, hCL⟩ := hC i
  have e : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) F) =
      actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) := by
    rw [NTypes.onMt, dite_eq_left hcen]; exact hCL ⟨_, hcen⟩ F
  have hne' : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) ≠ 0 := by
    rw [← e]; intro h0; apply hne; exact (P.M.loc i).real_inj (h0.trans (map_zero _).symm)
  let g : GL (Fin D.R.r) (ZMod (D.host.g k)) → G0g D.nd := fun h =>
    Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ h
  have hsum : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) =
      ∑ h, z.coeff h • NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) := by
    unfold actSum Formalism.MainNotions.ArithmeticCylinders.atPlace
    rw [MonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapDomain_index
      (h := fun g c => c • NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F))
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  have hg : ∀ h, ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧ IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧ NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := fun h =>
    _root_.GlobalTheory.T.lift_through_completion_iso_alt hL D P i PI k v s hs c hc hcs L hLift F hF h (g h) (by simp [g]) (fun kv hkv => by simp [g, Pi.mulSingle_eq_of_ne hkv])
  choose xs hxs using hg
  have hne'' : ∑ h, z.coeff h • NG.rt D.host.E D.R.nV (xs h) ((P.M.loc i).real F) ≠ 0 := by
    rw [hsum] at hne'
    simpa only [(hxs _).2.2] using hne'
  obtain ⟨U, hU, h1U, hθU⟩ := GlobalTheory.T.charOfLowerRightBlockDet_eventually_eq_one _ D.R.r D.R.t (S i s.w hw).mu (S i s.w hw).mu_ok.1
  have hFS : (P.M.loc i).real F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i PI) := by
    have := hF; rw [P.H.av.typeV] at this; exact this
  obtain ⟨y, hy, hyz⟩ := GlobalTheory.T.local_component_continuous_iso_fixed D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i PI) (P.H.av.irr i PI) s
    ((S i s.w hw).rep PI).toIrrRep (hT.rep i s hw PI) c hc hcs (GlobalTheory.BlockType.blockGrp _ D.R.r D.R.t)
    (GlobalTheory.BlockType.blockChar (S i s.w hw).mu) U (fun h hh => hh.1) (GlobalTheory.BlockType.kOne_le_blockGrp _ _) hU h1U
    (fun g hg _ => hθU g hg) _ hFS (_root_.GlobalTheory.T.completion_iso_split_place_alt hL D P S hT i PI k v s hw hs c hc hcs F hF) _ xs (fun h => z.coeff h)
    (fun h => (hxs h).1) hne''
  refine ⟨y, GlobalTheory.BlockType.isBlockVec_of _ _ _ hy, fun h => Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV (xs h)), fun h => (hxs h).2.1, ?_⟩
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact hyz
end GlobalTheory.DzVecLoc
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDepthZeroFixedVector

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DzVecLoc
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.HeightCounting.Up.CenLoc D P.M → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) ρ f, InSeries D k ρ f → PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ) → ∃ x, IsBlockVec (S i _ hw).mu ((S i _ hw).rep PI).π x ∧ NotKilled ((S i _ hw).rep PI).π (idemOf D k ρ) x := by
  intro _ hL D P hC S hT i PI k v hw ρ f hser hocc
  obtain ⟨s, hs⟩ := GlobalTheory.TypeBlockPf.splitAt D _ hw
  have key : ∀ (w : PlE D.host) (hw' : IsSplitPl D.host w), w = D.naut.plGw k v → ∃ x, IsBlockVec (S i w hw').mu ((S i w hw').rep PI).π x ∧ NotKilled ((S i w hw').rep PI).π (idemOf D k ρ) x := by
    intro w hw' hwv
    have e : w = s.w := hwv.trans hs.symm
    subst e
    exact _root_.GlobalTheory.DzVecLoc.vector_at_split_place hL D P hC S hT i PI k v s hw' hs ρ hser.1 hocc
  exact key _ hw rfl
end GlobalTheory.DzVecLoc
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_blockVec_notKilled_of_occurs : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.HeightCounting.Up.CenLoc D P.M → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) ρ f, InSeries D k ρ f → PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ) → ∃ x, IsBlockVec (S i _ hw).mu ((S i _ hw).rep PI).π x ∧ NotKilled ((S i _ hw).rep PI).π (idemOf D k ρ) x := by
  first | exact @_root_.GlobalTheory.DzVecLoc.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.DzVecLoc.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.DzVecLoc.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end
