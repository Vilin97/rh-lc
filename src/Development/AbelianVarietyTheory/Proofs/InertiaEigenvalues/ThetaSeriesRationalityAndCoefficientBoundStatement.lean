module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalThetaSeriesOfTwistSeriesSideDataStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterisationTransferMovedReadings
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalDatumSmallFieldFormHeckeScalarUnitStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiIntComb
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeoHalfMove

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsScalarMove

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct




namespace GlobalTheory.Unframe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ} (kap : ℝ) (lam : type_of% Rl.lam3)
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  (hw : ∀ i σ, w i σ ∈ Subgroup.center Γ) (hst : ∀ i, (Rl.FW i).MKStable)
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem pin_move {ρ : Setup D.ntw} (h : RealPin Rl cG ρ) : RealPin (fullHeckeRealDatMovedReadings Rl w kap lam) cG ρ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15, h.16, h.17, h.18⟩

theorem isNorm_move {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (ν : ℂ) :
    IsNorm (fullHeckeRealDatMovedReadings Rl w kap lam) v₀ B ν ↔ IsNorm Rl v₀ B ν := Iff.rfl

theorem vec_move {j : Fin D.R.m} (h : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) :
    FWT.IsChosenExtremalVector (fullHeckeRealDatMovedReadings Rl w kap lam).toRealDat j (sg0 D A3.A) (v₀ j _) := h

theorem isScalar_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {ν : ℂ}
    (h : IsScalar YS v₀ hρ i j b ν) : IsScalar (Rl := fullHeckeRealDatMovedReadings Rl w kap lam) (cG := cG) (S := moveS w YS) (moveYS kap lam YS hw hst) v₀ hρ i j b ν :=
  ⟨h.ne, fun h' => (isNorm_move kap lam _ _).2 (h.norm (h'.imp fun _ => (isNorm_move kap lam _ _).1)), fun h' =>
    (congrArg (Rat hρ) (realRd_move kap lam YS hw hst v₀ hρ i j b ν)).mpr
      (h.rat ((ratRow_move kap lam YS hw hst v₀ hρ i j b).1 h'))⟩

def moveZ (Z : ExportTie YS v₀) : ExportTie (Rl := fullHeckeRealDatMovedReadings Rl w kap lam) (cG := cG) (S := moveS w YS) (moveYS kap lam YS hw hst) v₀ where
  ρ := Z.ρ
  good := Z.good
  pin := pin_move kap lam Z.pin
  vec := fun j => vec_move kap lam (Z.vec j)
  ν := Z.ν
  scalar := fun i j b => isScalar_move kap lam hw hst Z.good i j b (Z.scalar i j b)
  tie := cast (congrArg (Comparison₂ Z.good (Y := D.nexp)) (rd_move kap lam hw hst Z).symm) Z.tie
  hecke := fun i j b => (congrArg HeckeTie (realRd_move kap lam YS hw hst v₀ Z.good i j b _)).mpr (Z.hecke i j b)
  univ := Z.univ

end GlobalTheory.Unframe

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSeriesCoeffBoundedInSupOfTwistSeriesSid

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section
namespace GlobalTheory.XiBound

theorem exists_pow_mul_mem {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {l : O} (hl : l ∈ IsLocalRing.maximalIdeal O) (z : K) :
    ∃ (n : ℕ) (o : O), algebraMap O K o = algebraMap O K (l ^ n) * z := by
  by_cases h0 : l = 0
  · exact ⟨1, 0, by simp [h0]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨⟨a, d⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors O) z
  have hd : (d : O) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hw
    exact (IsLocalRing.mem_maximalIdeal _).1 hl (hw ▸ w.isUnit)
  have hdvd : (d : O) ∣ l ^ k := by
    rw [hv, hw, mul_pow, ← pow_mul]
    exact mul_dvd_mul (Units.isUnit v).dvd (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero he)))
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨k, a * t, ?_⟩
  simp only at hz
  rw [ht, map_mul, map_mul, ← hz]
  ring

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → XiBdd Y.Z.rd := by
  intro hA hR hI D X E Y hF hP i hi j b s h P hd
  classical
  obtain ⟨u, c, hu, hK⟩ := GlobalTheory.XiIntComb.xi_int_comb hA hR hI D X E Y hF hP i hi j b s h P hd
  have hν : Y.Z.ν i j b ≠ 0 := (Y.Z.scalar i j b).ne
  have hFa : Faithful (Y.Z.rd i j b) :=
    realRd_faithful D X.Γ X.Pl0 X.I0 X.T X.A3 _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b (Y.Z.ν i j b)
      hν X.unif X.char.models.HW (Y.Z.vec j) ((GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)
  have hinj := hFa.injective
  set lam : ℂ := (Y.Z.ν i j b)⁻¹ * (((D.ntw.l i : ℕ) : ℂ) ^ c * u) with hlam

  have step : ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a x,
      Y.Z.rd i j b x = Y.Z.ρ.xi i j b D.nexp Q M h P a →
      ∃ x' ∈ D.nexp.Bsup i ((j : ℕ) + 1) b, Y.Z.rd i j b x' = lam • Y.Z.rd i j b x := by
    intro Q M hQ hs a x hx
    obtain ⟨n, o, m, hm, he⟩ := hK Q M hQ hs a
    let y : NX.Fm Y.S i ((j : ℕ) + 1) b :=
      ∑ k, ((show NX.KB Y.S i b from algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (o k)) • ((1 : NX.KB Y.S i b) ⊗ₜ[Y.S.Ks] m k) :
        NX.KB Y.S i b ⊗[Y.S.Ks] NX.FmK Y.S ((j : ℕ) + 1))
    have hy : y ∈ NX.Bsup Y.S i ((j : ℕ) + 1) b := by
      refine Submodule.sum_mem _ fun k _ => ?_
      exact (NX.Bsup Y.S i ((j : ℕ) + 1) b).smul_mem (o k) (Submodule.subset_span ⟨m k, hm k, rfl⟩)
    have hey : evK Y.YS X.geo.v₀ Y.Z.good i j b y = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
      refine (map_sum (evK Y.YS X.geo.v₀ Y.Z.good i j b) (fun k => ((show NX.KB Y.S i b from algebraMap (D.ntw.O i)
        (FractionRing (D.ntw.O i)) (o k)) • ((1 : NX.KB Y.S i b) ⊗ₜ[Y.S.Ks] m k) : NX.KB Y.S i b ⊗[Y.S.Ks] NX.FmK Y.S ((j : ℕ) + 1)))
        Finset.univ).trans (Finset.sum_congr rfl fun k _ => ?_)
      rw [TensorProduct.smul_tmul', evK_tmul, smul_eq_mul, mul_one]
      rfl
    let x' := (Y.YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y
    refine ⟨x', (Y.sup i _ b (Nat.le_add_left _ _) j.2 x').2 (by simp only [x', LinearEquiv.apply_symm_apply]; exact hy), ?_⟩
    change (Y.Z.ν i j b)⁻¹ • evK Y.YS X.geo.v₀ Y.Z.good i j b (Y.YS.eF i _ b (Nat.le_add_left _ _) j.2 x') = _
    rw [show Y.YS.eF i _ b (Nat.le_add_left _ _) j.2 x' = y from LinearEquiv.apply_symm_apply _ _, hey, ← he, hx, hlam,
      smul_smul]
  by_cases hex : ∃ μ : FractionRing (D.ntw.O i), Y.Z.ρ.e i b μ = lam
  · obtain ⟨μ, hμ⟩ := hex
    obtain ⟨N, o, ho⟩ := exists_pow_mul_mem (K := FractionRing (D.ntw.O i)) (D.ntw.O_l i) μ⁻¹
    refine ⟨N, fun Q M hQ hs a x hx => ?_⟩
    obtain ⟨x', hx'B, hx'⟩ := step Q M hQ hs a x hx
    have hμx : x' = μ • x := hinj (by rw [hx', map_smulₛₗ, hμ])
    by_cases hμ0 : μ = 0
    · exfalso
      rw [hμ0, map_zero, hlam] at hμ
      have hl : ((D.ntw.l i : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.ntw.lPrime i).out.ne_zero
      exact mul_ne_zero (inv_ne_zero hν) (mul_ne_zero (pow_ne_zero _ hl) hu) hμ.symm
    have : ((D.ntw.l i : D.ntw.O i) ^ N) • x = o • x' := by
      rw [hμx, ← algebraMap_smul (FractionRing (D.ntw.O i)) o, ← algebraMap_smul (FractionRing (D.ntw.O i)) ((D.ntw.l i : D.ntw.O i) ^ N),
        smul_smul, ho, mul_assoc, inv_mul_cancel₀ hμ0, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ hx'B
  · refine ⟨0, fun Q M hQ hs a x hx => ?_⟩
    obtain ⟨x', -, hx'⟩ := step Q M hQ hs a x hx
    by_cases h0 : Y.Z.rd i j b x = 0
    · rw [hinj (h0.trans (map_zero _).symm), smul_zero]
      exact Submodule.zero_mem _
    · exact absurd (hFa.mem_range_of_smul h0 ⟨x, rfl⟩ ⟨x', hx'⟩) hex

end GlobalTheory.XiBound
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSeriesCoeffBoundedInSupOfTwistSeriesSidStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.universalSeriesCoeff_boundedInSup_of_twistSeriesSideData : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → XiBdd Y.Z.rd := by
  first | exact @GlobalTheory.XiBound.main | exact GlobalTheory.XiBound.main | (intros; apply GlobalTheory.XiBound.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesRationalityAndCoefficientBound

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct




namespace GlobalTheory.Unframe

open GlobalTheory.TwInputs GlobalTheory.RealGeo Formalism.L2.Pj Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}



theorem exists_framed (hP : GlobalTheory.Published.CuspRapidDecay) (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (hF : FieldOk X) :
    ∃ (X' : RealSide D) (Y' : SerSide X' E), FieldOk X' ∧
      (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X'.core X'.R.toRealDat j X'.core.σ₀ hV) ∧
      (∀ i j b, RatRow Y'.YS X'.geo.v₀ Y'.Z.good i j b → RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧
      (XiBdd Y'.Z.rd → XiBdd Y.Z.rd) := by
  have hC : GlobalTheory.Core5 X.R.toRealDat X.F.lv2 := ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.thP⟩
  obtain ⟨c', w, hw, hfr, B, hB⟩ := exists_framed_half hP X.size hC X.geo X.unif X.inGeo
  obtain ⟨kap, lam, hs⟩ := scalars_exist (F := X.F) (realDatMovedReadingsKeepScalars X.R w)
  have hch : (fullHeckeRealDatMovedReadings X.R w kap lam).Char3 X.F := heckeCharacterisation_transfer_movedReadings X.char hs
  obtain ⟨B', -, hB', -⟩ := @geoHalf_upd D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (moveR X.R.toRealDat w) _ kap X.R.lam
    X.R.err0 B
  obtain ⟨κ, v₀, fw, bar, O, pins, rho, eqa, ct, phase⟩ := B'
  obtain rfl : v₀ = X.geo.v₀ := (eq_of_heq hB').trans hB
  let g : @GeoHalf D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat fun _ => 1 :=
    @GeoHalf.mk D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat _
      κ X.geo.v₀ fw bar O pins rho eqa ct phase
  have hpb : X.core.pb = X.R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs X.core.toCore X.R.toRealDat X.geo.fw.laws.toLawsM hC.lev
      ((X.geo.pins ⟨0, by have := D.R.two_le_m; omega⟩).2.tuple ()).half
  obtain ⟨hI, hU, hInt⟩ := @GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral hP D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg
    (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat _ g
    ⟨hch.lev, hch.grp.red_R, hch.grp.red_L, hch.grp.record, hch.fam, hch.models, hch.chain, hch.thP⟩ hch.grp.chiW hpb X.size
  have hst : ∀ i, (X.R.FW i).MKStable := fun i => (X.integral i).2.2
  let X' : RealSide D := @RealSide.mk D X.Γ X.grp X.fin X.Pl0 X.I0 X.T X.A3 (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam) X.F X.cG g
    hch X.phs X.guard X.valKs X.idem hU hInt hI X.finT X.host X.std X.size
  let Y' : SerSide X' E :=
    { S := moveS w Y.YS
      YS := moveYS kap lam Y.YS hw hst
      sup := Y.sup
      H := moveH kap lam Y.YS hw hst Y.H
      reads := reads_move kap lam Y.YS hw hst Y.reads
      del := Y.del
      Z := moveZ kap lam hw hst Y.Z
      U_eq := Y.U_eq
      psi_eq := Y.psi_eq
      low := Y.low
      Sb := Y.Sb
      B_range := Y.B_range
      hk_emb := Y.hk_emb
      hk_split := Y.hk_split
      off := Y.off
      all := Y.all }
  refine ⟨X', Y', ⟨hF.galois, hF.star, hF.vals, hF.ray, hF.roots, hF.split⟩, hfr,
    fun i j b => (ratRow_move kap lam Y.YS hw hst X.geo.v₀ Y.Z.good i j b).1, fun h => ?_⟩
  rw [← rd_move kap lam hw hst Y.Z]
  exact h

end GlobalTheory.Unframe

section

open GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf

theorem GlobalTheory.Unframe.rat_and_xiBdd : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧ XiBdd Y.Z.rd := by
  intro hP hA hR hS D X E Y hF
  obtain ⟨X', Y', hF', hfr, h1, h2⟩ := GlobalTheory.Unframe.exists_framed hP X Y hF
  exact ⟨fun i hi j b => h1 i j b (GlobalTheory.T.exists_rational_thetaSeries_of_twistSeriesSideData hA hR D X' E Y' hF' hfr i hi j b), h2 (GlobalTheory.T.universalSeriesCoeff_boundedInSup_of_twistSeriesSideData hA hR hS D X' E Y' hF' hfr)⟩

end
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesRationalityAndCoefficientBoundStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaSeries_rationality_and_coefficientBound : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧ XiBdd Y.Z.rd := by
  first | exact @GlobalTheory.Unframe.rat_and_xiBdd | exact GlobalTheory.Unframe.rat_and_xiBdd | (intros; apply GlobalTheory.Unframe.rat_and_xiBdd <;> assumption)
end
end
