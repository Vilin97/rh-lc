module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTransformCuspFormsReadsCosetSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOffOutsideS0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexPrincipalLevelEqRealisationPrincipalLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsHeckeDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtSplitPlaceDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.NotFamConstZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLaws
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Formalism.LocalToGlobal.IndefiniteReal.FWCentral

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeUnitOfExportTie

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct




namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀)

theorem exists_delta_root {ρ : GlobalTheory.SeriesTie.Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (z : (Formalism.L2.Theta.AE D)ˣ) : ∃ a : FractionRing (D.ntw.O i),
      ρ.e i b a = (((ρ.B i j b).de.chi z : Circle) : ℂ) ∧ ∃ n : ℕ, n ≠ 0 ∧ a ^ n = 1 := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_, _, hn, ?_⟩
  · rw [hρ.delta i j b]
    exact (GlobalTheory.SeriesTie.charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm
  · rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, map_one, map_one]

section Side

variable {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) (j : Fin D.R.m)

theorem valC_geoHecke {P : PlE D.host} {k : ℕ} (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T0.Q.l P.asIdeal (charAt P))
    (s : T0.Q.c.F) {f g : T0.R ((j : ℕ) + 1)} (hf : f ∈ sec (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (wtA (κ j)) (κ j).n)
    (hfg : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T0 ((j : ℕ) + 1) P.asIdeal (charAt P) k s f g)
    (z : FrC YS iC b ((j : ℕ) + 1)) (quot : HkKer P.asIdeal (charAt P) k z → FrC YS iC b ((j : ℕ) + 1))
    (hq : ∀ C, IsHkQuot P.asIdeal (charAt P) k z C (quot C)) :
    valC z g = embC YS iC b s * ∑ᶠ C, valC (quot C) f := by
  have hrel := hfg (PAt (embC YS iC b)) z
  have hL : GlobalTheory.Reg.EvLaws (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp _ _ _ _ _ _).1
  have hfun := GlobalTheory.HeckePointLaw.heckePointLaws.2.2.1 _ _ _ _ (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hP
  have hterm : ∀ C, hkTerm (fun S _ _ => FrPt (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := T0.Q.Xo ((j : ℕ) + 1)) P.asIdeal (charAt P) k Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P.asIdeal (charAt P) k (GlobalTheory.ThetaTrace.hkTr (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (charAt P)) Ω y C z)
      f z C = valC (quot C) f := by
    intro C
    have hex : ∃ w, hkRelFr P.asIdeal (charAt P) k (GlobalTheory.ThetaTrace.hkTr (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (charAt P))
        (PAt (embC YS iC b)) z C w := ⟨quot C, hq C⟩
    unfold hkTerm
    rw [dite_eq_left hex]
    have hm := hfun (PAt (embC YS iC b)) z C _ _ hex.choose_spec (hq C)
    exact (GlobalTheory.Reg.PChartModel.evR_map hL hf.1 (AlgHom.id _ _) hm).symm
  change toCp _ (evR (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c g z) = _
  unfold evR
  rw [hrel, map_mul, toCp_algebraMap]
  congr 1
  unfold hkVal
  exact finsum_congr hterm

end Side

end GlobalTheory.GeoTie
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeoOfLevels

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct




namespace GlobalTheory.GeoTie.CuspLev

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀)

variable {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) (j : Fin D.R.m)

theorem heckeIs_of_levels (Z : GlobalTheory.SeriesTie.ExportTie YS v₀) (hev : fw.Evaluates)
    (hLev : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hHW : Rl.toRealDat.models_HW) (hU : Rl.toRealDat.LUnif) (hK : (S.A ((j : ℕ) + 1)).IsKsForm)
    (hRd' : ∀ hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j,
      GlobalTheory.HeckeSup.ReadsCusp T0 Rl.toRealDat κ j (res T0 (sg0 D A3.A)) hV)
    (hS : ∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E)))
    (hHT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform) {k : ℕ} {P : PlE D.host} (hk : HkIdx i k P) :
    ∃ (c : FractionRing (D.ntw.O i)),
      Z.ρ.e i b c = (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) ^ k ∧ (∃ n : ℕ, n ≠ 0 ∧ c ^ n = 1) ∧
      ‖embC YS iC b (hkScal T0.Q.c (((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV)‖ = 1 ∧
      HeckeIs YS fw iC b j k P ((iC c)⁻¹ * embC YS iC b (hkScal T0.Q.c (((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV)) := by
  obtain ⟨hk1, hkr, hPs, hPS0⟩ := hk

  have hsg : sg0 D A3.A = D.what₂.embLL := RingHom.ext fun c => congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)
  have hres : res T0 (sg0 D A3.A) = T0.σ₀ := by
    rw [hsg]; exact res_embLL T0 fw.alg_eq fw.laws.pins.2.2.1
  have hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j :=
    fw.laws.spaceW _ (inR j) _ (base_embedding_good T0 Rl.toRealDat fw.alg_eq fw.laws.pins.2.2.1)
  have hRd := hRd' hV
  have hν : Z.ν i j b ≠ 0 := (Z.scalar i j b).ne
  have hinj : Function.Injective (Z.rd i j b) :=
    (GlobalTheory.SeriesTie.realRd_faithful D Γ Pl0 I0 T1 A3 T0.Q.c.F Rl cG S YS v₀ Z.ρ Z.good i j b (Z.ν i j b) hν hU
      hHW (Z.vec j) hK).injective

  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    rw [Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hPS0 (D.ntw.placesOver_subset_exceptional i 0 h)
    · exact hPS0 (D.ntw.placesOver_subset_exceptional i 1 h)
  have hoff : ¬ charAt P ∣ T0.Q.l.M' := GlobalTheory.HeckeSup.not_dvd_level fw.laws (charAt_mem P) hg
  have hso := hS P hPs hPS0
  have hsplit : P.asIdeal ⊔ P.asIdeal.map (T0.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ :=
    GlobalTheory.HeckeSup.split_of_ne hso.1
  have hSO : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.IsSplitOff T0.Q.l P.asIdeal (charAt P) :=
    ⟨P.isMaximal, hsplit, charAt_prime P, charAt_mem P, hoff⟩
  have hHP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T0.Q.l P.asIdeal (charAt P) :=
    GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, hsplit, charAt_prime P, charAt_mem P, hoff⟩

  have hn : (κ j).n = D.R.nV := (fw.kap j (D.eTau.symm 1)).2.2
  set cq : T0.Q.c.F := ((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2) with hcq
  set s : T0.Q.c.F := hkScal T0.Q.c cq P.asIdeal k D.R.nV with hs
  have htr : ∀ x : NX.FmK S ((j : ℕ) + 1), ∃ g ∈ T0.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T0 ((j : ℕ) + 1) P.asIdeal (charAt P) k s (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)) g := by
    intro x
    obtain ⟨g, hg, hfg⟩ := GlobalTheory.HeckeSup.exists_transform hHT GlobalTheory.HeckePointLaw.heckePointLaws fw.laws j hSO hkr cq
      (dom_wtA (κ j)) _ (cuspOf YS fw j x).2
    rw [show hkScal T0.Q.c cq P.asIdeal k (κ j).n = s by rw [hn]] at hfg
    exact ⟨g, hg, hfg⟩
  choose G hG hGt using htr
  let x' : NX.FmK S ((j : ℕ) + 1) → NX.FmK S ((j : ℕ) + 1) := fun x => (cuspOf YS fw j).symm ⟨G x, hG x⟩
  have hx' : ∀ x, (cuspOf YS fw j (x' x) : T0.R ((j : ℕ) + 1)) = G x := fun x => by
    simp only [x', AddEquiv.apply_symm_apply]

  obtain ⟨α₀, R₀, z₀, d₀⟩ := GlobalTheory.HeckeDatumExists.exists_isHeckeDatum D D.nd D.ntw Z.ρ Z.good i j b k P ⟨hk1, hkr, hPs, hPS0⟩
  obtain ⟨c, hc, N, hN, hcN⟩ := exists_delta_root Z.good i j b z₀
  have hPg : Bridge.SplitOff P (((Z.ρ.B i j b).G.Pg : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main Z.good i _ (fun P' hP' => by
      obtain ⟨k', hk'⟩ := Z.good.Pg i j b P' hP'
      exact D.ntw.placesOver_subset_exceptional i k' hk') P hPs hPS0
  have hdQ : Bridge.SplitOff P (((Z.ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main Z.good i _ (fun P' hP' => by
      rw [Z.good.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (GlobalTheory.SeriesTie.mem_half.1 hP').1) P hPs hPS0

  have hPgS : GlobalTheory.ExportSeries.SplitSet (Z.ρ.B i j b).G.Pg := by
    obtain ⟨Q', hPgQ, -, hQs⟩ := (Z.good.base i j b).places.split
    exact hQs.mono hPgQ
  have hde : ∀ α R z, Z.ρ.IsHeckeDatum i j b k P α R z → (((Z.ρ.B i j b).de.chi z : Circle) : ℂ) = Z.ρ.e i b c :=
    fun α R z d => by
      rw [hc, GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α z (Z.pin.delta i j b) (Z.good.base i j b).de.unram
          (Z.good.base i j b).de.split hdQ d.elt d.det,
        GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α₀ z₀ (Z.pin.delta i j b) (Z.good.base i j b).de.unram
          (Z.good.base i j b).de.split hdQ d₀.elt d₀.det]
  have hchr' : ChrEq (Z.ρ.B i j b).mu0 (Rl.C.mu0 j) := by rw [Z.pin.mu0 i j b]; exact hLev.mu0 j
  have hmu0 : ∀ α R z, Z.ρ.IsHeckeDatum i j b k P α R z →
      (((Z.ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k :=
    fun α R z d => GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α z hchr' (Z.good.base i j b).unram hPgS hPg d.elt d.det
  have hrank : (Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hdiv : k * D.R.nV / 2 = k * (D.R.nV / 2) := Nat.mul_div_assoc _ (even_iff_two_dvd.1 (kapDom D).2)

  have hkey : ∀ (a : NX.KB S i b) (x : NX.FmK S ((j : ℕ) + 1)),
      D.nexp.hkF i _ b k P ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x)) = c⁻¹ • (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x' x) := by
    intro a x
    refine GlobalTheory.SeriesTie.HeckeTie.eq (Z.hecke i j b) hinj ⟨hk1, hkr, hPs, hPS0⟩ d₀ ?_
    intro α R z d
    have hdc := d.reps
    rw [GlobalTheory.SeriesTie.levK_eq_levG_triv Rl Z.pin i j b] at hdc
    have hset : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T0 Rl.toRealDat j P (charAt P) k α R :=
      ⟨hso, charAt_prime P, charAt_mem P, hoff, hkr, d.elt, hdc⟩
    have hread := hRd P (charAt P) k α R ⟨hso, hg, hkr, d.elt, hdc⟩ hset _ (cuspOf YS fw j x).2 _ (hG x) (hGt x)
    simp only [← GlobalTheory.HeckeSup.hkC_eq (T := T0)] at hread
    funext h
    rw [GlobalTheory.SeriesTie.Setup.hecke_apply, map_smulₛₗ]
    simp only [GlobalTheory.SeriesTie.ExportTie.rd, Pi.smul_apply, smul_eq_mul]
    rw [realRd_eq_phiC YS fw Z.good i j b (Z.ν i j b) hV hev, realRd_eq_phiC YS fw Z.good i j b (Z.ν i j b) hV hev]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx', hread, GlobalTheory.ExportSeries.Base.mu, MonoidHom.mul_apply, Circle.coe_mul, hmu0 α R z d, hde α R z d,
      show Formalism.ConjugateSelfDual.normV P = Nat.card (kP P) from rfl, hrank, ← hdiv, map_inv₀, ← Finset.mul_sum]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt]
    ring
  have hsn : ‖embC YS iC b s‖ = 1 := by
    obtain ⟨p', f', hp', hp'P, hq'⟩ := GlobalTheory.HeckeSup.exists_prime_under P
    have hl : p' ≠ D.ntw.l i := by
      rintro rfl
      exact hPS0 (D.ntw.twistExcludedPlaces_contains_residueChar i hp'P)
    have e1 : Ideal.absNorm P.asIdeal = p' ^ f' := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq']
    have e2 : Nat.card (kP P) = p' ^ f' := hq'
    have hp1 : ‖((p' : ℕ) : ℂ_[D.ntw.l i])‖ = 1 := by
      rw [← map_natCast (algebraMap ℚ_[D.ntw.l i] ℂ_[D.ntw.l i]) p', norm_algebraMap', Padic.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes (Fact.out : (D.ntw.l i).Prime) hp').2 (Ne.symm hl)
    rw [hs, hkScal, hcq, e1, e2]
    simp only [map_mul, map_pow, map_inv₀, map_natCast, norm_mul, norm_pow, norm_inv, Nat.cast_pow, hp1, one_pow, inv_one,
      mul_one]
  refine ⟨c, hc.trans (GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α₀ z₀ (Z.pin.delta i j b) (Z.good.base i j b).de.unram
    (Z.good.base i j b).de.split hdQ d₀.elt d₀.det), ⟨N, hN, hcN⟩, hsn, ?_⟩
  intro z quot hq f
  have hfin : Finite (HkKer P.asIdeal (charAt P) k z.1) :=
    GlobalTheory.HeckePointLaw.heckePointLaws.1 _ _ _ _ (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hHP _ z.1
  obtain ⟨y, rfl⟩ := (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm.surjective f
  rw [LinearEquiv.apply_symm_apply]
  have key : ∀ y : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      valAt YS fw j z.1 (YS.eF i _ b (Nat.le_add_left _ _) j.2
        (D.nexp.hkF i _ b k P ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y))) =
        (iC c)⁻¹ * embC YS iC b s * ∑ᶠ C, valAt YS fw j (quot C) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      have e0 : (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (0 : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) = 0 :=
        map_zero _
      have e1 : ∀ C, valAt YS fw j (quot C) (0 : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) = 0 := fun C => map_zero _
      rw [e0, map_zero, map_zero, map_zero, finsum_congr e1, finsum_zero, mul_zero]
    | add y y' hy hy' =>
      have ea : (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (y + y') =
          (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y + (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y' := map_add _ _ _
      have eb : ∀ C, valAt YS fw j (quot C) (y + y') = valAt YS fw j (quot C) y + valAt YS fw j (quot C) y' :=
        fun C => map_add _ _ _
      rw [ea, map_add (f := _), map_add (f := _), map_add (f := _), hy, hy', finsum_congr eb, finsum_add_distrib (Set.toFinite _) (Set.toFinite _),
        mul_add]
    | tmul a x =>
      have ea : (YS.eF i _ b (Nat.le_add_left _ _) j.2) ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x' x)) =
          a ⊗ₜ[S.Ks] x' x := LinearEquiv.apply_symm_apply _ _
      rw [hkey, map_smul, ea]
      refine (valAt_smul YS fw j z.1 c⁻¹ _).trans ?_
      rw [valAt_tmul, hx',
        valC_geoHecke YS iC b j hHP s (cuspOf_mem_sec YS fw j x) (hGt x) z.1 quot hq]
      simp only [valAt_tmul]
      rw [← mul_finsum, map_inv₀]
      ring
  exact key y

theorem heckeGeo_of_levels (Z : GlobalTheory.SeriesTie.ExportTie YS v₀) (hev : fw.Evaluates)
    (hLev : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hHW : Rl.toRealDat.models_HW) (hU : Rl.toRealDat.LUnif) (hK : (S.A ((j : ℕ) + 1)).IsKsForm)
    (hRd : ∀ hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j,
      GlobalTheory.HeckeSup.ReadsCusp T0 Rl.toRealDat κ j (res T0 (sg0 D A3.A)) hV)
    (hS : ∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E)))
    (hHT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform)
    (hδ : ∀ P, P ∉ D.ntw.S0 i → ∃ s : T0.Q.c.F,
      D.what₂.embLL (algebraMap T0.Q.c.F D.what₂.LL s) = (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ)) :
    HeckeGeo YS fw iC b j := by
  intro k P hk
  obtain ⟨c, hc, ⟨N, hN, hcN⟩, hsn, h⟩ := heckeIs_of_levels YS fw iC b j Z hev hLev hHW hU hK hRd hS hHT hk
  obtain ⟨s₁, hs₁⟩ := hδ P hk.2.2.2
  have hs : Z.ρ.e i b (sideK YS i b (s₁ ^ k)) = Z.ρ.e i b c := by
    obtain ⟨a, rfl⟩ := (eKs YS).surjective s₁
    rw [hc, ← hs₁, map_pow, map_pow, sideK_eKs, eKs_LL, ← S.kKs_spec]
    exact congrArg (· ^ k) (Z.good.e_LL0 i b (S.kKs a))
  have hcs : embC YS iC b (s₁ ^ k) = iC c := congrArg iC ((Z.ρ.e i b).injective hs)
  have h1 : ‖iC c‖ ^ N = 1 := by rw [← norm_pow, ← map_pow, hcN, map_one, norm_one]
  have hc1 : ‖iC c‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN).1 h1
  refine ⟨(s₁ ^ k)⁻¹ * hkScal T0.Q.c (((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV, ?_, ?_⟩
  · rw [map_mul, map_inv₀, norm_mul, norm_inv, hcs, hc1, hsn, inv_one, one_mul]
  · rw [map_mul, map_inv₀, hcs]
    exact h

end GlobalTheory.GeoTie.CuspLev

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeometricAllStates

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.HeightCounting.HeckeLaw

theorem delAt_unr {D : D7} (C : CharFrame D) (i : D.ntw.Tw) {P : PlE D.host} (hP : P ∉ D.ntw.S0 i) :
    (C.delAt (D.ntw.l i)).UnrAt P := by
  have h : ¬ OverP D.host (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) P := fun hk =>
    hP (D.ntw.primes_subset_exceptional i (by rw [← Finset.mem_coe, D.ntw.pD_eq]; exact hk))
  unfold CharFrame.delAt
  split_ifs at h ⊢
  · exact C.isDel'.unr P h
  · exact C.isDel.unr P h

theorem del_values {B : Base} {δ : Fld.FieldDat B.toPre} {f : Fr B.toPre} (h : B.KsExact δ f) :
    f.del.ValuesIn 0 B.KstoC ∧ f.del'.ValuesIn 0 B.KstoC := by
  have h1 : Fld.charField f ≤ B.KsC := ((Fld.listField_le_iff δ f).1 (le_of_eq (Eq.symm h))).2.2.2.2.1
  rw [Fld.valuesIn_iff, Fld.valuesIn_iff, B.imField_KstoC]
  exact ⟨((le_sup_right.trans le_sup_left).trans le_sup_left).trans h1, (le_sup_right.trans le_sup_left).trans h1⟩

theorem delAt_mem {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (i : (w.st Z).toD7.ntw.Tw) (P : PlE (w.st Z).toD7.host) (hP : P ∉ (w.st Z).toD7.ntw.S0 i) :
    ∃ s : z.core.Q.c.F, (w.st Z).toD7.what₂.embLL (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL s) =
      (((z.R.C.delAt ((w.st Z).toD7.ntw.l i)).val P : ℂˣ) : ℂ) := by
  have hC : z.R.C = Fr.at (w.st Z) f := z.lev.C.trans (congrArg _ w.C_eq)
  have hu := delAt_unr z.R.C i hP
  have hv : (z.R.C.delAt ((w.st Z).toD7.ntw.l i)).ValuesIn 0 B.KstoC := by
    rw [hC]
    unfold CharFrame.delAt
    split_ifs
    · exact (del_values w.exact).2
    · exact (del_values w.exact).1
  obtain ⟨y, hy⟩ := hv P hu
  obtain ⟨s, hs⟩ := z.Ks_le y.1 y.2
  refine ⟨s, ?_⟩
  rw [hs]
  refine Eq.trans (show _ = B.KstoC y from rfl) (hy.trans ?_)
  simp [HChar.valTw]

end GlobalTheory.HeightCounting.HeckeLaw
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeGeometricOfMultiplicityLowerBound

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.HeightCounting.HeckeLaw
theorem hecke_geometric_of_multiplicity_lower_bound_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (i : (Dof x).ntw.Tw) (b : Bool) (j : Fin (Dof x).R.m), GlobalTheory.GeoTie.HeckeGeo l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j := by
  intro hP hS hL
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  refine ((ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x l i b j
  obtain ⟨hHo, -⟩ := H.1 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := H.2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := by
    have hs : ({τ | τ = (Formalism.L2.DIV.mu0F (X := B.fields) (tuOf w.I (usedOf w.I T P.Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T P.Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T P.Wt)).finite_toSet
    exact hs.to_subtype
  let X := GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize
  have hC := X.char
  have hSb : ∀ Q ∈ x.m.z.R.Sb, Q ∈ (Dof x).ntw.S0 i := by
    intro Q hQ
    have hA : x.m.z.R.Sb = x.m.z.R.Pg := x.m.z.pins.char.allPl
    obtain ⟨k, hk⟩ := l.b.ser.ex.good.Pg i j b Q (by rw [l.b.ser.ex.pin.Pg]; exact hA ▸ hQ)
    exact (Dof x).ntw.placesOver_subset_exceptional i k hk
  exact GlobalTheory.GeoTie.CuspLev.heckeGeo_of_levels l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j l.b.ser.ex
    (x.m.z.geo.fw.evaluates_of_lUnif x.m.intersectionNumber_baseChange.prim.unif) hC.lev hC.models.HW x.m.intersectionNumber_baseChange.prim.unif
    (l.rat.In.ks _ (Nat.le_add_left _ _) j.2) (fun hV => GlobalTheory.HeckeSupReal.readsCusp_realSide hP.decay hS.hkRead (Dof x) X j hV)
    (fun Q hQs hQ => GlobalTheory.SplitOffS0.main l.b.ser.ex.good i _ hSb Q hQs hQ) hS.hkTr
    (fun Q hQ => delAt_mem w x.o.Z x.m.z i Q hQ)
end GlobalTheory.HeightCounting.HeckeLaw
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeGeo_at_levelB1_states : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (i : (Dof x).ntw.Tw) (b : Bool) (j : Fin (Dof x).R.m), GlobalTheory.GeoTie.HeckeGeo l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j := by
  first | exact @_root_.GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_multiplicity_lower_bound_alt | exact _root_.GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_multiplicity_lower_bound_alt | (intros; apply _root_.GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_multiplicity_lower_bound_alt <;> assumption)
end
end
end
end
