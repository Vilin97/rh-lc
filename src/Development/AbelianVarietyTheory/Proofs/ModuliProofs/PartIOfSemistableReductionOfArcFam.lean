module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PelSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSystemsJointPropertiesOfLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRingStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelAmpleModelOfSemistableReductionStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalModelOfLocalModelsStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelStructureConditionsAndSplitFibresStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelsSiegelFamilyComparisonStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionFieldStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransitionMapRaisedModelsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMonoStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelFiniteCoverAmpleFrames
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamiliesExistStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSystemsJointPropertiesOfLawsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.modelSystems_jointProperties_of_laws : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ModelsSt → N0 → PartI := by
  first | exact @GlobalTheory.LN.partI_of_inputs | exact GlobalTheory.LN.partI_of_inputs | (intros; apply GlobalTheory.LN.partI_of_inputs <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocalModelSystemTransitionSiegelClauses

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

section Incl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H} {c : Coeff l}
  {c₂ : Coeff l₂} {W : ValuationSubring ℂ}

theorem exists_isIncl (hc : c.F ≤ c₂.F) : ∃ b : c.V W →+* c₂.V W, IsIncl b := by
  refine ⟨RingHom.codRestrict ((IntermediateField.inclusion hc).toRingHom.comp (c.V W).subtype) (c₂.V W)
    (fun x => x.2), fun x => rfl⟩

theorem isIncl_unique {b b' : c.V W →+* c₂.V W} (hb : IsIncl b) (hb' : IsIncl b') : b = b' := by
  refine RingHom.ext fun x => Subtype.ext (Subtype.ext ?_)
  exact (hb x).trans (hb' x).symm

end Incl

theorem system_clauses : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW, N2 (S.Y p W hp hW) := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hD hN S p W hp hW
  refine ⟨fun i => (GlobalTheory.T.localModel_oneModel_and_splitFibres hext L1 L2 L3 E H D Xo hD hN S p W hp hW i).1, ?_⟩
  obtain ⟨hnp, hodd, h3, h4⟩ := S.aux (S.ch p)
  have hcop := (GlobalTheory.T.exists_two_inert_odd_primes_coprime_level E H).2 _ (S.aux (S.ch p))
  obtain ⟨-, hl2, hl3⟩ := GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp
  have key : ∀ i i₂ : Idx H p, i.l.Dvd i₂.l → i.c.F ≤ i₂.c.F →
      ∃ π : (S.Y p W hp hW i₂).X ⟶ (S.Y p W hp hW i).X, ∀ b : i.c.V W →+* i₂.c.V W, IsIncl b →
        IsTransition (S.Y p W hp hW i) (S.Y p W hp hW i₂) b π := by
    intro i i₂ hl hc
    obtain ⟨b, hb⟩ := exists_isIncl (W := W) hc
    obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
    obtain ⟨l₀', h₀', hr'⟩ := S.raises p W hp hW i₂
    obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_transition_map_raised_models hext L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN l₀ l₀' _ _ i.l i.c _ _
      (S.Y p W hp hW i) i₂.l i₂.c _ _ (S.Y p W hp hW i₂) b hnp.pos ⟨_, dvd_rfl⟩ (hl3 _ _ _ _ h₀ h₀' hl)
      (hl2 _ _ h₀).1 (hl2 _ _ h₀').1 hl hc ((GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i.l i.c).2.2.2 p W hp hW).1
      ((GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i₂.l i₂.c).2.2.2 p W hp hW).1 hb hr hr'
    exact ⟨π, fun b' hb' => isIncl_unique hb hb' ▸ hπ⟩
  choose π hπ using key
  obtain ⟨Ag, hAg⟩ := GlobalTheory.T.cm_models_siegel_family_comparison L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN p hp (S.ch_ne p).symm hnp ⟨_, rfl⟩
  refine ⟨π, hπ, S.n (S.ch p), S.J (S.ch p), Ag, hnp, hodd, S.ch_ne p, ?_, hcop, ?_⟩
  · have h2 : 3 ≤ S.n (S.ch p) := by
      have := hnp.two_le
      obtain ⟨k, hk⟩ := hodd
      omega
    exact h2.trans (Nat.le_self_pow (by have := S.J_pos (S.ch p); omega) _)
  · intro i i₁ hl hc b z hb hz hM hMb hA hF
    obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
    obtain ⟨l₀', h₀', hr'⟩ := S.raises p W hp hW i₁
    have h₁ : IsPrimeToPart l₀' i.l p := by
      obtain ⟨a1, a2, a3⟩ := h₀'
      exact ⟨a1, hM ▸ a2, hMb ▸ a3⟩
    obtain rfl : l₀' = l₀ := (hl2 _ _ h₀).2.2 _ h₁
    exact hAg W l₀' _ i.l i₁.l i.c i₁.c _ _ b z _ hW h₀ (hcop _) hb hz hM hMb hA hF hr hr' (hπ i i₁ hl hc b hb)

end GlobalTheory.Models
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocalModelSystemTransitionSiegelClausesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.localModelSystem_transition_siegel_clauses : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW, N2 (S.Y p W hp hW) := by
  first | exact @GlobalTheory.Models.system_clauses | exact GlobalTheory.Models.system_clauses | (intros; apply GlobalTheory.Models.system_clauses <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelFiniteCoverAmpleFramesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.raised_model_finite_cover_ample_frames : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N k : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), n.Prime → Odd n → (∃ e, N = n ^ e) → IsUnit (n : O) → l₀.Dvd l → IsDedFrac β → Raises B Y → Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2)) → GlobalTheory.LN.Amp Y := by
  first | exact @GlobalTheory.RaisedAmple.amp_of_raises | exact GlobalTheory.RaisedAmple.amp_of_raises | (intros; apply GlobalTheory.RaisedAmple.amp_of_raises <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemsAmpleFrames

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.Models

theorem exists_localSystems_ample :
    GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → N1 → GlobalTheory.LN.ModelsSt := by
  intro hext hL hL2 hL3 htop hN1 E _ _ _ H D hpq Xo
  obtain ⟨-, hN⟩ := hN1
  have hlev : ToroidalLevelCompatibility (H := H) (D := D) := (hN E H D hpq).1

  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel hext hL hL2 hL3 htop E H D Xo hpq hlev
  refine ⟨S.Y, fun p W hp hW => ⟨GlobalTheory.T.localModelSystem_transition_siegel_clauses hext hL hL2 hL3 E H D Xo hpq hlev S p W hp hW, fun i => ?_⟩,
    GlobalTheory.T.exists_global_model_of_local_models hext hL hL2 hL3 E H D Xo hpq hlev S⟩
  refine ⟨(GlobalTheory.T.localModel_oneModel_and_splitFibres hext hL hL2 hL3 E H D Xo hpq hlev S p W hp hW i).2, ?_⟩

  obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
  obtain ⟨k, hk⟩ := hS (S.ch p)
  have hc := (GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW
  have hcop : (S.n (S.ch p)).Coprime p := (Nat.coprime_primes (S.aux _).1 hp).2 (S.ch_ne p)
  exact GlobalTheory.T.raised_model_finite_cover_ample_frames hL hL2 hL3 E H D Xo (S.n (S.ch p)) (S.n (S.ch p) ^ S.J (S.ch p)) k (S.T (S.ch p)) hlev
    l₀ i.l (S.B (S.ch p) l₀ h₀.1) i.c _ (i.c.V W).subtype (S.Y p W hp hW i) (S.aux _).1 (S.aux _).2.1
    ⟨_, rfl⟩ (hc.2.1 _ hcop) ((GlobalTheory.Models.primeToPart_spec E H p hp).2.1 i.l l₀ h₀).1 hc.1 hr hk

end GlobalTheory.Models
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemsAmpleFramesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_localModelSystems_ampleFrames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → N1 → GlobalTheory.LN.ModelsSt := by
  first | exact @GlobalTheory.Models.exists_localSystems_ample | exact GlobalTheory.Models.exists_localSystems_ample | (intros; apply GlobalTheory.Models.exists_localSystems_ample <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelsOfSemistableReduction

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem modelsSt_of_semistableReduction : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.LN.ModelsSt :=
  fun S => GlobalTheory.T.exists_localModelSystems_ampleFrames GlobalTheory.homExtension_semiAbelian_dvr GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1
    GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.1 (GlobalTheory.T.exists_fullLevelAmpleModel_of_semistableReduction S) GlobalTheory.T.moduliScheme_levelMaps_heckePoints'

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChangeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.twistedPrincipalPolarisation_sections_baseChange : DVR.TwistBaseChangeStatement := by
  first | exact @GlobalTheory.twistBaseChange | exact GlobalTheory.twistBaseChange | (intros; apply GlobalTheory.twistBaseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.PartIOfSemistableReductionOfArcFam

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem partI_of_semistableReduction_of_arcFam :
    GlobalTheory.Published.SemistableReductionSt → GlobalTheory.LN.ArcFamSt → PartI :=
  fun S A => by
    obtain ⟨L, L2, L3, L4, L5, L6⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
    exact GlobalTheory.T.modelSystems_jointProperties_of_laws GlobalTheory.T.twistedPrincipalPolarisation_sections_baseChange L L2 L3 L4 L5 L6 GlobalTheory.LN.ega_holds
      GlobalTheory.uniformisation_dvr_unconditional GlobalTheory.T.linearUniformisation_triples_torsion GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing A
      (GlobalTheory.modelsSt_of_semistableReduction S) GlobalTheory.T.siegelFamilies_exist

end GlobalTheory
end
end
