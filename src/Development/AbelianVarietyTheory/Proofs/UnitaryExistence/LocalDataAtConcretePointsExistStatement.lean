module

public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphicStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDegenerationDataAlgebraicPointModelStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint
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
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalDataPrescribedPointsFlagStatement
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Formalism.LocalToGlobal.ProjectiveLattices.TowerOfAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicFieldStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringComapEqNonunits
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLawsStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelAmpleModelOfSemistableReductionStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransitionMapRaisedModelsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRingStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHoldStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvrStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonemptyStatement
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndHalfEqPrimeProductStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PeriodFormAdditiveBalancedPosDefBoundedRank
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_flag_model_baseChange_integral_framed_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, algCls Xo c T io y → (∃ z, LiesOverBaseChange la Tw T io y z) ∧ ∀ z, LiesOverBaseChange la Tw T io y z → ∃ (g : T.V →+* intO ↥z.2.1.S) (ιT : Sp T.V ⟶ (Tw.Y z.1).X), Function.Injective g ∧ (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥z.2.1.S) : ↥z.2.1.S)‖ < 1) ∧ spMap g ≫ ιT = z.2.2.1.yt := by
  first | exact @GlobalTheory.Exist.FlagBaseChange.exists_lies_and_factor | exact GlobalTheory.Exist.FlagBaseChange.exists_lies_and_factor | (intros; apply GlobalTheory.Exist.FlagBaseChange.exists_lies_and_factor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTower

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor
  Formalism.L2.Pj GlobalTheory.Models

namespace GlobalTheory.LocalData.Towers

theorem isIntegral_rat_zeta_of_coeff (n : ℕ) : IsIntegral ℚ (zeta n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : zeta 0 = 1 := by simp [zeta]
    rw [this]; exact isIntegral_one
  · have h := Complex.isPrimitiveRoot_exp n hn.ne'
    exact (h.isIntegral hn).tower_top

theorem exists_coeff_containing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (s : Finset ℂ), (∀ z ∈ s, IsAlgebraic ℚ z) → ∃ c : Coeff l, ∀ z ∈ s, z ∈ c.F := by
  intro E _ _ _ H l s hs
  classical
  let b := Module.finBasis ℚ E
  let S : Set ℂ := (s : Set ℂ) ∪ Set.range (fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2)) ∪
    {zeta l.M', H.rt0, zeta l.A}
  have hfin : S.Finite := ((s.finite_toSet).union (Set.finite_range _)).union (Set.toFinite _)
  haveI : Finite S := hfin.to_subtype
  have hint : ∀ x ∈ S, IsIntegral ℚ x := by
    rintro x ((hx | ⟨p, rfl⟩) | hx)
    · exact (hs x hx).isIntegral
    · exact (Algebra.IsIntegral.isIntegral (R := ℚ) (b p.2)).map p.1.toRatAlgHom
    · rcases hx with rfl | rfl | rfl
      · exact isIntegral_rat_zeta_of_coeff _
      · refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
        rw [H.sqrt_neg_disc_sq]
        exact (isIntegral_natCast _).neg
      · exact isIntegral_rat_zeta_of_coeff _
  have hsub : S ⊆ IntermediateField.adjoin ℚ S := IntermediateField.subset_adjoin _ _
  refine ⟨⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hint, ?_, ?_, ?_⟩, ?_⟩
  · intro τ a

    rw [← b.sum_repr a, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _ (hsub (Or.inl (Or.inr ⟨(τ, i), rfl⟩)))
  · exact hsub (Or.inr (by simp))
  · refine IntermediateField.adjoin.mono _ _ _ ?_
    intro x hx
    exact Or.inr (Or.inr hx)
  · intro z hz
    exact hsub (Or.inl (Or.inl hz))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_valuationSubring {l : Level H} (c : Coeff l) (p : ℕ) (v : HeightOneSpectrum (𝓞 c.F))
    (hv : (p : 𝓞 c.F) ∈ v.asIdeal) :
    ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ c.V W = (v.valuation c.F).valuationSubring := by
  obtain ⟨W, hWe, hWn⟩ := GlobalTheory.Reg.exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom
    (v.valuation c.F).valuationSubring
  have hpU : (p : c.F) ∈ (v.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (v.valuation c.F)).lt_one_iff_lt_one]
    have := (v.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hv
    simpa using this
  exact ⟨W, by simpa using hWn _ hpU, hWe⟩

theorem baseAt_of_eq {l : Level H} {c : Coeff l} {v : HeightOneSpectrum (𝓞 c.F)} {V : ValuationSubring c.F}
    (h : V = (v.valuation c.F).valuationSubring) : PointsOfFlagModel.BaseAt v V.subtype := by
  subst h
  refine ⟨Subtype.val_injective, fun x => ⟨?_, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩⟩
  rintro ⟨y, rfl⟩
  exact y.2

theorem exists_coeff_ge {l : Level H} (c : Coeff l) (l₂ : Level H) : ∃ c₂ : Coeff l₂, c.F ≤ c₂.F := by
  classical
  haveI := c.fin
  let b := Module.finBasis ℚ c.F
  obtain ⟨c₂, h⟩ := exists_coeff_containing E H l₂ (Finset.univ.image fun i => ((b i : c.F) : ℂ)) (by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom c.F.val)
  refine ⟨c₂, fun x hx => ?_⟩
  have key : ∀ y : c.F, (y : ℂ) ∈ c₂.F := by
    intro y
    have hy : y ∈ Submodule.span ℚ (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      have e : ((a • y : c.F) : ℂ) = (a : ℂ) * (y : ℂ) := by simp [Rat.smul_def]
      rw [e]
      exact mul_mem (SubfieldClass.ratCast_mem _ a) hy
  exact key ⟨x, hx⟩

def deeper (l : Level H) (k : ℕ) (hk : 0 < k) : Level H :=
  { l with A := k * l.A, A_pos := Nat.mul_pos hk l.A_pos }

theorem dvd_deeper (l : Level H) (k : ℕ) (hk : 0 < k) : l.Dvd (deeper l k hk) :=
  ⟨dvd_rfl, le_rfl, Dvd.intro_left k rfl⟩

variable {D : Datum H}

theorem exists_transition {Xo : ∀ l : Level H, Moduli D l} (S : System Xo) (hN : ToroidalLevelCompatibility (H := H) (D := D)) {p : ℕ}
    (hp : p.Prime) {W W' : ValuationSubring ℂ} (hW : (p : ℂ) ∈ W.nonunits) (hW' : (p : ℂ) ∈ W'.nonunits)
    (i i' : Idx H p) (hl : i.l.Dvd i'.l) (hc : i.c.F ≤ i'.c.F) (he : i.c.V W = i.c.V W') :
    ∃ (b : i.c.V W →+* i'.c.V W') (π : (S.Y p W' hp hW' i').X ⟶ (S.Y p W hp hW i).X),
      IsTransition (S.Y p W hp hW i) (S.Y p W' hp hW' i') b π := by
  obtain ⟨L1, L2, L3, -⟩ := GlobalTheory.T.all_uniformization_laws_hold
  obtain ⟨l₀, h₀, r₀⟩ := S.raises p W hp hW i
  obtain ⟨l₀', h₀', r₀'⟩ := S.raises p W' hp hW' i'
  obtain ⟨-, hsp, hmono⟩ := GlobalTheory.Models.primeToPart_spec E H p hp
  let b : i.c.V W →+* i'.c.V W' :=
    ((IntermediateField.inclusion hc).toRingHom.comp (i.c.V W).subtype).codRestrict (i'.c.V W') fun x => by
      have hx : (x : i.c.F) ∈ i.c.V W' := he ▸ x.2
      exact hx
  obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_transition_map_raised_models GlobalTheory.T.semiAbelian_hom_extends_uniquely_over_dvr L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN l₀ l₀' _ _ i.l i.c _ _
    (S.Y p W hp hW i) i'.l i'.c _ _ (S.Y p W' hp hW' i') b (S.aux _).1.pos ⟨_, dvd_rfl⟩
    (hmono _ _ _ _ h₀ h₀' hl) (hsp _ _ h₀).1 (hsp _ _ h₀').1 hl hc
    ((GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW).1
    ((GlobalTheory.CoeffRings.coeff_isDedFrac E H i'.l i'.c).2.2.2 p W' hp hW').1 (fun _ => rfl) r₀ r₀'
  exact ⟨b, π, hπ⟩

theorem exists_towerAt {Xo : ∀ l : Level H, Moduli D l} (S : System Xo) (hD : 1 ≤ D.p + D.q) (l : Level H)
    (c : Coeff l) {p : ℕ} (hp : p.Prime) (hg : l.GoodAt p) : ∃ Tw : PointsOfFlagModel.Tower p (Xo l) c, PointsOfFlagModel.TowerAt Tw := by
  have hN := (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H D hD).1
  have hne : ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β),
      Nonempty Y.X := fun l c O _ β Y =>
    ((GlobalTheory.T.typeFn_period_exist_moduli_nonempty E H D).2.2 GlobalTheory.T.cmModuli_consequence_of_abelianSchemeLaws hD l (Xo l) c).map fun x => Y.j x
  let lv : ℕ → Level H := fun n => deeper l (p ^ n) (pow_pos hp.pos n)
  choose cN hcN using fun n => exists_coeff_ge c (lv n)
  choose W hW hWe using fun v : PointsOfFlagModel.abelian₂ p c => exists_valuationSubring c p v.1 v.2
  choose WN hWN hWNe using fun n (w : PointsOfFlagModel.abelian₂ p (cN n)) => exists_valuationSubring (cN n) p w.1 w.2
  refine ⟨{ O := fun v => c.V (W v)
            β := fun v => (c.V (W v)).subtype
            Y := fun v => S.Y p (W v) hp (hW v) ⟨l, c, hg⟩
            lvN := lv
            XoN := fun n => Xo (lv n)
            cN := cN
            ON := fun n w => (cN n).V (WN n w)
            βN := fun n w => ((cN n).V (WN n w)).subtype
            YN := fun n w => S.Y p (WN n w) hp (hWN n w) ⟨lv n, cN n, hg⟩ },
    fun v => ⟨baseAt_of_eq (hWe v), hne _ _ _ _ _⟩,
    fun n => ⟨dvd_deeper l _ (pow_pos hp.pos n), dvd_rfl, fun w => ⟨⟨baseAt_of_eq (hWNe n w), hne _ _ _ _ _⟩, ?_⟩⟩⟩
  obtain ⟨v, hv, hve⟩ := GlobalTheory.GlobalModelGuards.exists_prime_eq c (WN n w) p hp (hWN n w)
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hve
  exact ⟨⟨v, hv⟩, exists_transition S hN hp (hW ⟨v, hv⟩) (hWN n w) ⟨l, c, hg⟩ ⟨lv n, cN n, hg⟩ (dvd_deeper l _ (pow_pos hp.pos n))
    (hcN n) ((hWe ⟨v, hv⟩).trans hve)⟩

theorem nonempty_tower {Xo : ∀ l : Level H, Moduli D l} (S : System Xo) (l : Level H) (c : Coeff l)
    (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (p : ℕ) : Nonempty (PointsOfFlagModel.Tower p (Xo l) c) := by
  choose q hq hqv using fun v : PointsOfFlagModel.abelian₂ p c => GlobalTheory.Reg.exists_prime_natCast_mem v.1
  choose W hW _ using fun v : PointsOfFlagModel.abelian₂ p c => exists_valuationSubring c (q v) v.1 (hqv v)
  exact ⟨{ O := fun v => c.V (W v)
           β := fun v => (c.V (W v)).subtype
           Y := fun v => S.Y (q v) (W v) (hq v) (hW v) ⟨l, c, hg _ (hq v)⟩
           lvN := fun _ => l
           XoN := fun _ => Xo l
           cN := fun _ => c
           ON := fun _ v => c.V (W v)
           βN := fun _ v => (c.V (W v)).subtype
           YN := fun _ v => S.Y (q v) (W v) (hq v) (hW v) ⟨l, c, hg _ (hq v)⟩ }⟩

theorem exists_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ p : ℕ, ∃ Tw : PointsOfFlagModel.Tower p Xo c, p.Prime → PointsOfFlagModel.TowerAt Tw := by
  intro E _ _ _ H D l Xo c hD hg p
  classical
  obtain ⟨Xf, rfl⟩ : ∃ Xf : ∀ l : Level H, Moduli D l, Xf l = Xo :=
    ⟨Function.update (fun l => (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 E H D l hD).some) l Xo, Function.update_self ..⟩
  obtain ⟨L1, L2, L3, -⟩ := GlobalTheory.T.all_uniformization_laws_hold
  obtain ⟨S, -⟩ := GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing L1 L2 L3 (GlobalTheory.T.exists_fullLevelAmpleModel_of_semistableReduction GlobalTheory.T.semistableReduction_ppav_padicField) E H D Xf hD (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H D hD).1
  by_cases hp : p.Prime
  · obtain ⟨Tw, h⟩ := exists_towerAt S hD l c hp (hg p hp)
    exact ⟨Tw, fun _ => h⟩
  · obtain ⟨Tw⟩ := nonempty_tower S l c hg p
    exact ⟨Tw, fun h => absurd h hp⟩

end GlobalTheory.LocalData.Towers
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PeriodFormAdditiveBalancedPosDefBoundedRankStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.periodForm_additive_balanced_posDef_boundedRank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ) (C : SCF p) (P : PointsOfFlagModel.PtC Y C), p.Prime → ∀ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes → Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → spMap g ≫ ιT = P.yt → ∀ A : DatAt Y P, (∀ a a' b, A.beta (a + a') b = A.beta a b + A.beta a' b) ∧ (∀ (x : 𝓞 E) a b, A.beta (x • a) b = A.beta a (H.bar x • b)) ∧ (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ A.Ylat), ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * A.beta (b i) (b k)) ∧ ∃ ρ : ℕ, Module.finrank ℤ A.Ylat = 2 * (Module.finrank ℚ E / 2) * ρ ∧ ρ ≤ Dw.p ∧ ρ ≤ Dw.q := by
  first | exact @GlobalTheory.PeriodLaws.period_laws | exact GlobalTheory.PeriodLaws.period_laws | (intros; apply GlobalTheory.PeriodLaws.period_laws <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocalDataAtConcretePointsExist

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalData

def FactorsFin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) {p : ℕ} {C : SCF p} (P : PointsOfFlagModel.PtC Y C) : Prop :=
  ∃ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes ∧ Function.Injective g ∧
    (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) ∧ spMap g ≫ ιT = P.yt

theorem half_degree (D : D7) : Module.finrank ℚ D.host.E / 2 = D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  omega

theorem bar_eq_of_conj (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (x x' : 𝓞 D.host.E)
    (h : (x' : D.host.E) = D.host.conj (x : D.host.E)) : H.bar x = x' := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact (H.bar_eq x).trans ((barE_eq_conj D x).trans h.symm)

theorem laws_of_factorsFin (D : D7) (Q : Par D) (hQ : Q.Pins) {j : ℕ} (hj : 1 ≤ j) (hm : j < D.R.m) {p : ℕ}
    (hp : p.Prime) {O : Type} [CommRing O] {β : O →+* Q.c.F} {Y : Model (Q.Xo j) Q.c β} {C : SCF p}
    {P : PointsOfFlagModel.PtC Y C} (hf : FactorsFin Y P) (A : DatAt Y P) :
    (∀ a b, A.toLatB.beta a b = A.toLatB.beta b a) ∧
    (∀ a a' b, A.toLatB.beta (a + a') b = A.toLatB.beta a b + A.toLatB.beta a' b) ∧
    (∀ (x x' : 𝓞 D.host.E), (x' : D.host.E) = D.host.conj (x : D.host.E) →
      ∀ a b, A.toLatB.beta (x • a) b = A.toLatB.beta a (x' • b)) ∧
    (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ A.toLatB.Y), ∀ x : ι → ℝ, x ≠ 0 →
      0 < ∑ i, ∑ k, x i * x k * A.toLatB.beta (b i) (b k)) ∧
    ∃ ρ : ℕ, Module.finrank ℤ A.toLatB.Y = 2 * D.R.f * ρ ∧ ρ ≤ (D.R.sigW j).1 ∧ ρ + (D.R.sigW j).1 ≤ D.R.r := by
  obtain ⟨T, g, ιT, h1, h2, h3, h4⟩ := hf
  obtain ⟨ha, hb, hc, ρ, hr1, hr2, hr3⟩ := GlobalTheory.T.periodForm_additive_balanced_posDef_boundedRank D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c O β Y p C
    P hp T g ιT h1 h2 h3 h4 A
  obtain ⟨hp1, hq1, -⟩ := hQ.2.2.2 j ⟨hj, hm.le⟩
  rw [hp1] at hr2
  rw [hq1] at hr3
  rw [half_degree D] at hr1
  refine ⟨A.beta_symm, ha, fun x x' hx a b => ?_, hc, ρ, hr1, hr2, ?_⟩
  · rw [← bar_eq_of_conj D Q.H x x' hx]
    exact hb x a b
  · simp only [Ranks.sigW, Ranks.r] at hr3 ⊢
    omega

theorem uniq_of_factorsFin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Y : Model Xo c β} {p : ℕ} (hp : p.Prime) {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (hf : FactorsFin Y P)
    (A A' : DatAt Y P) : ∃ e : A.toLatB.Y ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (e a) (e b) = A.toLatB.beta a b := by
  obtain ⟨T, g, ιT, h1, h2, h3, h4⟩ := hf
  exact (GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic E H Dw l Xo c O β Y p C P hp T g ιT h1 h2 h3 h4 A A').2

theorem localData_exists :
    ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → Packet66Rest Q := by
  intro D Q hQ hpq
  have hgood := (GlobalTheory.T.level_good_and_half_eq_prime_product D Q.H Q.l hQ.1.2.1 hQ.2.1.1).1
  choose Tw hTw using fun j p => Towers.exists_tower D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c (hpq j) hgood p
  have hdat : ∀ j p (z : PointsOfFlagModel.Pt (Tw j p) .yy), p.Prime → FactorsFin ((Tw j p).Y z.1) z.2.2.1 →
      Nonempty (DatAt ((Tw j p).Y z.1) z.2.2.1) := by
    rintro j p z hp ⟨T, g, ιT, h1, h2, h3, h4⟩
    obtain ⟨A, -⟩ := GlobalTheory.T.exists_degeneration_data_algebraic_point_model D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c _ _ _ p _ z.2.2.1 hp T g ιT h1 h2 h3 h4
    exact ⟨A⟩
  let Pt : ℕ → ℕ → Type := fun j p => {z : PointsOfFlagModel.Pt (Tw j p) .yy //
    (1 ≤ j ∧ j < D.R.m) ∧ p.Prime ∧ FactorsFin ((Tw j p).Y z.1) z.2.2.1}
  have A0 : ∀ j p (y : Pt j p), DatAt ((Tw j p).Y y.1.1) y.1.2.2.1 := fun j p y =>
    Classical.choice (hdat j p y.1 y.2.2.1 y.2.2.2)
  obtain ⟨P, dat, hP⟩ := GlobalTheory.T.exists_localData_prescribed_points_flag D Pt (fun j p y => PointsOfFlagModel.fld y.1) (fun j p y => (A0 j p y).toLatB)
    (fun j p y => laws_of_factorsFin D Q hQ y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2 (A0 j p y))
  let G : In66 Q :=
    { P := P
      dat := dat
      Tw := Tw
      rel := fun j p η z => (P.loc (dat j) p).fld η = PointsOfFlagModel.fld z ∧
        ∀ A : DatAt ((Tw j p).Y z.1) z.2.2.1, ∃ e : (P.loc (dat j) p).Ylat η ≃ₗ[𝓞 D.host.E] A.Ylat,
          ∀ a b, A.beta (e a) (e b) = (P.loc (dat j) p).be η a b }
  have hfac : ∀ j la z, G.IsAlgPt j la z → FactorsFin ((Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1 := by
    rintro j la z ⟨T, io, e, y, ho, hy, hz⟩
    obtain ⟨g, ιT, h2, h3, h4⟩ := (GlobalTheory.T.exists_flag_model_baseChange_integral_framed_point D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c la (Tw j _)
      (hTw j _ (resCh_prime la)) T io e ho y hy).2 z hz
    exact ⟨T, g, ιT, hy, h2, h3, h4⟩
  refine ⟨G, fun j hj hm => (hP j hj hm).1, fun j _ _ p hp => hTw j p hp,
    fun j _ _ la z hz => hdat j _ z (resCh_prime la) (hfac j la z hz), fun j hj hm la z hz => ⟨?_, fun η h => h.1⟩,
    fun j _ _ la z _ η h => h.2, fun j _ _ la T io e ho y hy => ?_⟩
  · let y : Pt j (WeightAlgebra.resCh la) := ⟨z, ⟨hj, hm⟩, resCh_prime la, hfac j la z hz⟩
    obtain ⟨η, h1, e, he⟩ := (hP j hj hm).2 _ y
    refine ⟨η, h1, fun A => ?_⟩
    exact (uniq_of_factorsFin (resCh_prime la) y.2.2.2 (A0 j _ y) A).elim fun e' he' =>
      ⟨e.trans e', fun a b => (he' (e a) (e b)).trans (he a b)⟩
  · exact (GlobalTheory.T.exists_flag_model_baseChange_integral_framed_point D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c la (Tw j _)
      (hTw j _ (resCh_prime la)) T io e ho y hy).1

end GlobalTheory.LocalData
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocalDataAtConcretePointsExistStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localDataAtConcretePoints_exist : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → Packet66Rest Q := by
  first | exact @GlobalTheory.LocalData.localData_exists | exact GlobalTheory.LocalData.localData_exists | (intros; apply GlobalTheory.LocalData.localData_exists <;> assumption)
end
end
