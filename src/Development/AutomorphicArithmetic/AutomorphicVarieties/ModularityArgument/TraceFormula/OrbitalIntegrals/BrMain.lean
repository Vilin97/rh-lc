module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.AlongIndep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.GeoTransport
import GroundTheory.LocalFields.Integers
public import GroundTheory.LocalFields.Uniqueness
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceOfLocal
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwCentImg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.UnitMatch
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Mathlib.Topology.Separation.Connected

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.GeoOfMatch

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.geoOfMatch :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCentImg → UpperTheory.V.Z.Tf.Orb.QuotAlong → UpperTheory.V.Z.Tf.Orb.InclClosed → UpperTheory.V.Z.Tf.Orb.GeoOfMatch := by
  intro hT hC hCC hI hQ hCl k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n _ _ _ _ μE μk hE hk φ hφ f hf hM γ hγ ν hν
  obtain ⟨a1, a2, a3, -⟩ := hT E n
  obtain ⟨b1, b2, b3, -⟩ := hT k n
  have hσc : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) := ((hC k E).2.2 n).2 σ
  refine ⟨fun δ hδ => ?_, fun hn => ?_⟩
  · have hδ' : normGL σ δ = incl γ := hδ
    obtain ⟨hreg, hS⟩ := hI k E σ hσ n δ γ hγ hδ'
    have hcl : IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) := by
      have : ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x} := by
        ext x; simp [Subgroup.mem_centralizer_singleton_iff, Commute, SemiconjBy]
      rw [this]
      exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
    have hcm : ∀ a ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)), ∀ b ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)),
        Commute a b := fun a ha b hb => by
      rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
      exact Units.ext (hCC k n γ a b hγ (congrArg Units.val ha) (congrArg Units.val hb))
    obtain ⟨μ, hμ, hmap, hq⟩ := hQ _ _ incl (hCl k E n) μE hE _ _ hcl hcm hS ν hν
    have h1 := hM.1 δ γ 1 μ ν hreg (by simpa using hδ') hμ hν (by simpa using hmap)
    have hcont : Continuous fun g => φ (twConj (sigmaGL σ) g δ) :=
      hφ.1.continuous.comp ((continuous_inv.mul continuous_const).mul hσc)
    have h2 := hq _ hcont.measurable fun s hs g => by rw [twConj_mul_left _ _ hs]
    rw [one_mul]
    exact h2.trans h1
  · refine hM.2 γ ν hγ (fun ⟨δ, h, hh⟩ => hn ⟨twConj (sigmaGL σ) h δ, ?_⟩) hν
    have hl : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
      rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
    have := twNorm_twConj_of_pow_eq_one _ hl h δ
    have hh' : twNorm (sigmaGL σ) (Module.finrank k E) δ = h * incl γ * h⁻¹ := hh
    rw [hh'] at this
    refine this.trans ?_
    show h⁻¹ * (h * incl γ * h⁻¹) * h = incl γ
    group
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.InclClosed

section

@[expose] public section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.inclClosed :
    UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.InclClosed := by
  intro _ k E _ _ _ _ _ _ _ _ _ _ _ n
  let _ := GroundTheory.LocalField.nontriviallyNormedField k
  have := GroundTheory.LocalField.completeSpace_nontriviallyNormedField k
  have := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField E
  have h : Topology.IsClosedEmbedding (algebraMap k E) :=
    LinearMap.isClosedEmbedding_of_injective (f := Algebra.linearMap k E) (LinearMap.ker_eq_bot.mpr (algebraMap k E).injective)
  have hM : Topology.IsEmbedding
      ((algebraMap k E).mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) k →* Matrix (Fin n) (Fin n) E) :=
    Topology.IsEmbedding.piMap (f := fun _ : Fin n => Pi.map fun _ : Fin n => algebraMap k E)
      fun _ => Topology.IsEmbedding.piMap fun _ => h.isEmbedding
  refine ⟨hM.units_map, ?_⟩
  have e : Set.range (incl : GL (Fin n) k → GL (Fin n) E) =
      ⋂ i, ⋂ j, (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) ⁻¹' Set.range (algebraMap k E) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro ⟨y, rfl⟩ i j
      exact ⟨(y : Matrix (Fin n) (Fin n) k) i j, rfl⟩
    · intro h
      choose M hM using h
      have e : (algebraMap k E).mapMatrix (Matrix.of M) = (g : Matrix (Fin n) (Fin n) E) := by
        ext i j
        exact hM i j
      have hd : (Matrix.of M).det ≠ 0 := fun h0 => by
        have h1 := RingHom.map_det (algebraMap k E) (Matrix.of M)
        rw [h0, map_zero, e] at h1
        exact (Matrix.GeneralLinearGroup.det g).ne_zero h1.symm
      exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, Units.ext e⟩
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun j => h.isClosed_range.preimage (Units.continuous_val.matrix_elem i j)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceInt

section

@[expose] public section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.placeInt :
    UpperTheory.V.Z.Tf.Orb.PlaceInt := by
  refine ⟨fun F _ _ v n => rfl, fun F E _ _ _ _ _ v w hw n => ?_⟩
  ext g
  refine ⟨fun h => h w, fun h w' => ?_⟩
  obtain rfl := hw w'
  exact h
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceUniq

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel PositivityTheory.Rg.Tf.Loc GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo
open scoped TensorProduct

theorem UpperTheory.V.Z.Tf.Orb.placeUniq :
    UpperTheory.V.Z.Tf.Orb.PlaceUniq := by
  intro F E _ _ _ _ _ _ hp v hs
  obtain ⟨w, hw⟩ := not_forall.1 hs
  have hd : ∀ w' : PlacesOver E v, Module.finrank (v.adicCompletion F) (w'.1.adicCompletion E) =
      Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) := fun w' => by
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (E ≃ₐ[F] E) w w'
    exact (galEquiv v σ w.1 w'.1 (by rw [← hσ]; rfl)).toLinearEquiv.finrank_eq.symm
  have h := sum_finrank_eq E v
  rw [Finset.sum_congr rfl fun w' _ => hd w', Finset.sum_const, smul_eq_mul, Finset.card_univ] at h
  rcases (Nat.prime_mul_iff.1 (h ▸ hp)) with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact absurd (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1).2 hw
  · obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.1 h1
    exact ⟨u, hu⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceUnit

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.placeUnit :
    UpperTheory.V.Z.Tf.Orb.UnitMatch → UpperTheory.V.Z.Tf.Orb.UnitSB → UpperTheory.V.Z.Tf.Orb.PlaceData → UpperTheory.V.Z.Tf.Orb.PlaceOfLocal → UpperTheory.V.Z.Tf.Orb.PlaceInt → UpperTheory.V.Z.Tf.Orb.PlaceUnit := by
  intro hM hU hD hL hI hB F E _ _ _ _ _ _ σ hσ v w hw hur n _ _ _ _ mE mF hE hF vE vF
  obtain ⟨i1, i2, i3, i4, s, hs, hr, h1, h2, h3⟩ := hD F E σ hσ v w hw
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  obtain ⟨hH, hP⟩ := @hL F E _ _ _ _ _ _ σ hσ v w hw i1 i2 i3 i4 s hs hr h1 h2 n _ _ _ _ mE mF hE hF _ _
  have hc : Continuous (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  have hm := @hM hB _ _ _ _ _ _ _ _ _ _ _ i1 i2 i3 i4 (h3 hur) s hs n _ _ _ _ _ mF hH hF
    (by rw [Measure.map_apply hc.measurable (hU _ n).1.measurableSet, ← hI.2 F E v w hw n, vE])
    (by rw [hI.1 F v n, vF])
  have := hP _ (hU _ n).2.2 _ (hU _ n).2.2 hm
  rw [hI.2 F E v w hw n, ← hI.1 F v n]
  exact this
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotAlong

section

@[expose] public section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotAlong :
    UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotAlong := by
  intro _ _ G _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ j hj μG hμ T S hT hc hS ν hν
  subst hS
  let e₀ : T ≃* T.map j := T.equivMapOfInjective j hj.injective
  have c1 : Continuous e₀ := (hj.continuous.comp continuous_subtype_val).subtype_mk _
  have c2 : Continuous e₀.symm := by
    rw [(hj.isInducing.comp IsInducing.subtypeVal).continuous_iff]
    have : (j ∘ Subtype.val) ∘ e₀.symm = Subtype.val := funext fun x => congrArg Subtype.val (e₀.apply_symm_apply x)
    exact continuous_subtype_val.congr fun x => (congrFun this x).symm
  let e : T ≃ₜ* T.map j := ⟨e₀, c1, c2⟩
  have he : Measurable (e : T → T.map j) := c1.measurable
  refine ⟨ν.map e, e.isHaarMeasure_map ν, Measure.map_map (g := fun x : T.map j => (x : G)) measurable_subtype_coe he, fun F _ _ => ?_⟩
  have hp : PositivityTheory.Rg.Tf.Geo.IsNormAlong id (fun t : T => j t) ν = IsQuotNormaliser (T.map j) (ν.map e) := by
    funext ρ
    refine propext (and_congr_right fun hρ => forall_congr' fun g => ?_)
    rw [lintegral_map (f := fun h : T.map j => ρ (h * g)) (hρ.comp (measurable_subtype_coe.mul_const g)) he]
    rfl
  have gen : ∀ p q : (G → ℝ≥0∞) → Prop, p = q → ∀ [Decidable (∃ ρ, p ρ)] [Decidable (∃ ρ, q ρ)],
      (if h : ∃ ρ, p ρ then ∫ x, F x * ((h.choose x).toReal : ℂ) ∂μG else 0) =
      (if h : ∃ ρ, q ρ then ∫ x, F x * ((h.choose x).toReal : ℂ) ∂μG else 0) := by
    rintro p _ rfl _ _
    congr
  exact @gen _ _ hp (Classical.propDecidable _) (Classical.propDecidable _)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.UnitSB

section

@[expose] public section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.unitSB :
    UpperTheory.V.Z.Tf.Orb.UnitSB := by
  intro E _ _ _ _ n
  have := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField E
  have ho : IsOpen (unitGL (n := Fin n) E : Set (GL (Fin n) E)) := GroundTheory.Automorphic.GLnLocal.isOpen_integralGL E n
  have hc : IsCompact (unitGL (n := Fin n) E : Set (GL (Fin n) E)) := GroundTheory.Automorphic.GLnLocal.isCompact_integralGL E n
  refine ⟨ho, hc, ?_, ?_⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    by_cases hx : x ∈ (unitGL (n := Fin n) E : Set (GL (Fin n) E))
    · filter_upwards [ho.mem_nhds hx] with y hy
      simp only [unitFnC, Set.indicator_of_mem hx, Set.indicator_of_mem hy, Pi.one_apply]
    · filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp only [unitFnC, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain

section

@[expose] public section

namespace UpperTheory.V.Z.Tf.Orb

theorem twCentImg_holds : TwCentImg := twCentImg centComm_of

theorem quotAlong_holds : QuotAlong := quotAlong haarComm_of quotIndep_of

theorem inclClosed_holds : InclClosed := inclClosed extCont_of

theorem geoOfMatch_holds : GeoOfMatch := geoOfMatch gLTop_of extCont_of centComm_of twCentImg_holds quotAlong_holds inclClosed_holds

theorem quotReal_holds : QuotReal := quotReal

theorem unitSB_holds : UnitSB := unitSB

theorem unitMatch_holds : UnitMatch := unitMatch gLTop_of extCont_of centComm_of twCent_of haarComm_of quotReal_holds unitSB_holds

theorem geoTransport_holds : GeoTransport := geoTransport

theorem alongIndep_holds : AlongIndep := alongIndep

theorem placeData_holds : PlaceData := placeData

theorem placeOfLocal_holds : PlaceOfLocal := placeOfLocal gLTop_of extCont_of centComm_of haarComm_of twCentImg_holds geoOfMatch_holds geoTransport_holds alongIndep_holds

theorem placeUniq_holds : PlaceUniq := placeUniq

theorem placeInt_holds : PlaceInt := placeInt

theorem placeUnit_holds : PlaceUnit := placeUnit unitMatch_holds unitSB_holds placeData_holds placeOfLocal_holds placeInt_holds

end UpperTheory.V.Z.Tf.Orb
end
end
