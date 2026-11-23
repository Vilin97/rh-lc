module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ArithmeticGroupCongruenceSubgroupProperty
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BaseExtensionHolds
public import Development.AutomorphicArithmetic.CommutativeAlgebra.CongruenceCRTOfLatticeGen
public import Development.AutomorphicArithmetic.CommutativeAlgebra.CongruenceSubgroupIsLatticeStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsGenericModuliPoint
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsNumberFieldPointOfGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
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
public import Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeCorrespondenceIsogenyOfTraceCrt
public import Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeCorrespondenceLiesInTowerOfLiftCount
public import Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeLiftExistsOfQuotientLevel
public import Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeLiftSeparatedOfLatticeCongruence
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsogenyClassExistsOfQuotient
public import Development.AutomorphicArithmetic.CommutativeAlgebra.LatticeGeneration
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplierIsUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
public import Development.AutomorphicArithmetic.CommutativeAlgebra.PowerProjectorExists
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientInvariantOfTraceUnitCrt
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientLevelOfLatticeGeneration
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientMapComp
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliIso
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliObjectExists
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientSeparatedOfTraceUnitCrt
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientUniqueOfComp
public import Development.AutomorphicArithmetic.CommutativeAlgebra.RationalSplittingExists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFiniteStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerCoveringOfInvariantFiniteEtaleSeparated
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerFiniteEtaleOfTrivialPowerCartesian
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerInvariantOfBaseInvariantPowerCartesian
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerPointCountStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerSeparatedOfTrivialPowerCartesian
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerTrivialOfQuotientTracePowerCartesian
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceEtaIdentity
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceIdentityOfTjElement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TracePullbackIdentity
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceUnitOfPullbackMultiplier

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.GroupSchemePullbackExists

section

@[expose] public section

open UpperTheory.Gal.Int.Geo

theorem UpperTheory.group_scheme_pullback_exists :
    GPull := by
  intro G R _ _ gb N X X' s e o
  exact GlobalTheory.UPel.HT.Gen.BaseChange.exists_gObjMap_pull e o
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.IntegralGeometricGaloisSplitting

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.integralGeometricGalois_splitting : UpperTheory.Gal.Int.Geo.SplitOf := by
  intro W X c _ _ Δ _ a ha h
  refine UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts c c Δ a ha ?_
  intro Ω _ _ x y hy
  obtain ⟨δ, hδ, hu⟩ := h Ω x y hy.symm
  exact ⟨δ, hδ.symm, fun δ' hδ' => hu δ' hδ'.symm⟩
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.PowerMapCartesian

section

@[expose] public section

open UpperTheory.Gal.Int.Geo
open CategoryTheory

theorem UpperTheory.power_map_cartesian :
    PowCart := by
  intro X Y Z A B C f g φ χ u v k
  refine ⟨fun H => GlobalTheory.KS.PowPB.powMap_isPullback _ _ _ _ f φ u H k,
    GlobalTheory.KS.PowPB.powMap_w f φ u k, fun w => ?_⟩
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_w, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w,
      Category.assoc, GlobalTheory.KS.PowPB.powMap_w]
  · intro i
    rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_pr, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_pr,
      Category.assoc, GlobalTheory.KS.PowPB.powMap_pr]
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.SiteExistsOfSplittingAndPowerProjector

section

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.site_exists_of_splitting_and_power_projector :
    MIn → SplitQ → BaseEx → PowProj → SiteEx := by
  intro hM hS hB hP
  intro p _ D G hSc E _ _ e gb hstd w q _ r 𝔴 𝔫 hpl hat hlev
  have sp := hS p D hSc.m1 q
  obtain ⟨N₀, 𝔞, h3, hcq, hcp, hsup, hupow, hlv⟩ := hlev
  obtain ⟨f, b, hmat, hstdb, hqmem, hnorm⟩ :=
    hB q (datAt hat sp) hSc.a1 hSc.m1 E e gb hstd w 𝔴 r hpl hat.le N₀ h3 hcq
  obtain ⟨M⟩ := hM.ex q (datAt hat sp) (Ow w) b N₀ h3 hcq
  have hEt : UpperTheory.Gal.FiniteEtaleModels.IsEtIdeal b 𝔞 :=
    (hM.placeOf q (datAt hat sp) (Ow w) b r 𝔴 hat.max hstdb.pmem hSc.a1 hstdb.ule hstdb.tw 𝔞 hsup).2 hupow
  obtain ⟨Y, π, ρ, hov, ⟨hmπ⟩, hgal⟩ := hM.finModel q (datAt hat sp) (Ow w) b N₀ h3 hcq 𝔞 1 hEt M
  have hfin : IsFinite π := hgal.fin
  have het : Etale π := hgal.etale
  have hMproj : IsProjOver M.s := hM.proj q (datAt hat sp) (Ow w) b N₀ h3 hcq hSc.cpt M
  have hYproj : IsProjOver Y.s := by
    rw [← hov]
    exact GlobalTheory.T.isProjOver_comp_finite (Ow w) M.X Y.X π M.s hfin hMproj
  have hYsm : SmoothOfRelativeDimension (0 + (datAt hat sp).a * ((datAt hat sp).n - 1)) Y.s := by
    rw [← hov]
    haveI : SmoothOfRelativeDimension 0 π := by
      rw [← AlgebraicGeometry.Etale.eq_smoothOfRelativeDimension_zero]
      exact het
    haveI := M.smooth
    infer_instance
  have hPw := fun k => hP q (datAt hat sp) (Ow w) b N₀ h3 hcq Y.X Y.s Y.univ k
  exact ⟨⟨hat, sp, f, b, hmat, N₀, 𝔞, hstdb, hqmem, hnorm, hcp, hsup, hupow, hlv, M, Y, π, hov, hmπ,
    hfin, het, fun k => (hPw k).1 hYproj, fun k => (hPw k).2 _ hYsm⟩⟩
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.StandardDatumExists

section

@[expose] public section

open UpperTheory.Gal.Int.Geo

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen in
theorem UpperTheory.standard_datum_exists :
    StdEx := by
  intro p _ D ha E _ _ e
  let φ : 𝓞 D.F →+* E := (e : D.F →+* E).comp (algebraMap (𝓞 D.F) D.F)
  have key : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]
    ring
  have hroot : φ D.ω ^ 2 - (D.tr : E) * φ D.ω + (D.nm : E) = 0 := by
    simpa using congrArg φ key
  have hsub : Subsingleton (Fin D.toG.a) := by
    have h : D.toG.a = 1 := ha
    rw [h]
    infer_instance
  exact ⟨{ ρ := φ D.ω
           ρ_root := hroot
           t := fun _ => φ
           t_ω := fun _ => rfl
           comax := fun i j hij => (hij (Subsingleton.elim i j)).elim }, rfl, fun _ _ => rfl⟩
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.TowerCoveringCongruenceOfHeckeLies

section

@[expose] public section

open UpperTheory.Gal.Int.Geo

theorem UpperTheory.tower_covering_congruence_of_hecke_lies :
    MIn → SiteEx → NumEx → ClsEx → KSCover → TjLies → KSCong := by
  intro hM hS hN hC hV hL p _ D G L hsc E _ _ e gb hstd k T N J A _ g θ w 𝔴 hpl ϑ hG
  obtain ⟨q, r, 𝔫, K₀, hat, hok, hlev, hKN, hNn, hdeck, hall⟩ := hG
  haveI : Fact q.Prime := ⟨hat.prime⟩
  haveI : 𝔴.IsMaximal := hat.max
  obtain ⟨S⟩ := hS p D G hsc E e gb hstd w q r 𝔴 𝔫 hpl hat hok
  have hNpos : 0 < N.1 := lt_of_lt_of_le (by norm_num) N.2.1
  obtain ⟨c, a, hnum⟩ := (hN p D E gb w q r 𝔴 𝔫 S N.1 hNpos).1 hNn
  obtain ⟨⟨C⟩, -⟩ := hC q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat N.1 S.N₀ c a S.𝔞
    hnum.1 hNpos S.std.three S.std.cop hnum.2 S.Y (T.M N).X (T.M N).s (T.M N).univ
  obtain ⟨Cv⟩ := hV p D G L E gb w q r 𝔴 𝔫 S k T K₀ hlev N c a hnum C hKN J A g θ hdeck
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow w)
  haveI := S.et
  obtain ⟨Tc, Lc, d, h, hov, hpt⟩ := hM.cong q (datAt S.atq S.sp) (Ow w) S.f S.b S.N₀ r 𝔴 S.std S.M ϖ hϖ S.𝔞 1
    S.sup S.upow S.Y S.π S.ov inferInstance S.mπ k
  choose γ hγK hγT hγd hγr hγθ using hall
  refine ⟨Cv.toCover, q, S.f, hat.prime, S.qmem, S.norm, ϖ, fun j => (h j).corr,
    fun j => γ j (Nat.lt_succ_iff.1 j.2), fun j => (L.KN (g (γ j (Nat.lt_succ_iff.1 j.2))).M.1).relIndex
      (K₀ ⊓ K₀.comap (MulAut.conj (g (γ j (Nat.lt_succ_iff.1 j.2))).h).toMonoidHom), hϖ, hpt, fun j => ⟨hov j, ?_, ?_⟩⟩
  · obtain ⟨h0, κ, e1, e2, e3⟩ := hL p D G L E gb w q r 𝔴 𝔫 S k T K₀ hlev N c a hnum C hKN J g _ j
      (Nat.lt_succ_iff.1 j.2) (hγK _ _) (hγT _ _) (hγd _ _) (hγr _ _) (Tc j) (Lc j)
    exact ⟨h0, κ, e1, e2, e3⟩
  · exact hγθ _ _
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.TraceEtaPointwise

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.trace_eta_pointwise : TrEtaPt := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT Ω _ _ z x
  obtain ⟨-, -, -, -, hgeo⟩ := hT
  have hz : z ≫ s = spMap (Spec.preimage (z ≫ s)).hom := by
    simp [spMap, Spec.map_preimage]
  obtain ⟨I', I'', h1, h2, h3⟩ := hgeo Ω z _ hz
  have hpos : ∀ M : Lv p, 0 < (M : ℕ) := fun M => by
    have := M.2.1
    omega
  have hzero : ∀ n : ℕ, I''.ev n 0 = 1 := fun n => by
    have h := I''.add n 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hin0 : inAf D 0 = 0 := by
    simp [inAf]
  have e1 := congrArg (· ≫ ψ) (h1 x)
  simp only [Category.assoc] at e1
  refine ⟨?_, ?_⟩
  · refine Iff.trans ?_ ((h3 _ (hpos N') N'.2.2 x 0).trans ?_)
    · rw [e1]
      first
        | simp only [hzero]
        | erw [hzero]
    · simp only [hin0, zero_add]
  · rintro rfl y hxy
    refine (h3 _ (hpos N') N'.2.2 x y).mp ?_
    rw [← e1, hxy]
    exact h2 y
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CovMain

section

@[expose] public section

namespace UpperTheory.Gal.Int.Geo.CovMain

set_option linter.unusedVariables false

theorem splitQ_of (I : MIn) : SplitQ := UpperTheory.rational_splitting_exists

theorem baseEx_of (I : MIn) : BaseEx := UpperTheory.baseExtension_holds

theorem powProj_of (I : MIn) : PowProj := UpperTheory.power_projector_exists

theorem siteEx_of (I : MIn) : SiteEx := UpperTheory.site_exists_of_splitting_and_power_projector I (splitQ_of I) (baseEx_of I) (powProj_of I)

theorem genEx_of (I : MIn) : GenEx := UpperTheory.exists_generic_moduli_point

theorem numEx_of (I : MIn) : NumEx := UpperTheory.exists_number_field_point_of_generic (genEx_of I)

theorem latGen_of (I : MIn) : LatGen := UpperTheory.lattice_generation

theorem gPull_of (I : MIn) : GPull := UpperTheory.group_scheme_pullback_exists

theorem powCart_of (I : MIn) : PowCart := UpperTheory.power_map_cartesian

theorem qObj_of (I : MIn) : QObj := UpperTheory.quotient_moduli_object_exists

theorem qComp_of (I : MIn) : QComp := UpperTheory.quotient_map_comp

theorem qUniq_of (I : MIn) : QUniq := UpperTheory.quotient_unique_of_comp (qComp_of I)

theorem qIso_of (I : MIn) : QIso := UpperTheory.quotient_moduli_iso

theorem qLev_of (I : MIn) : QLev := UpperTheory.quotient_level_of_lattice_generation (latGen_of I)

theorem clsEx_of (I : MIn) : ClsEx := UpperTheory.isogeny_class_exists_of_quotient (qObj_of I) (qComp_of I) (qUniq_of I) (qLev_of I)

theorem trEta_of (I : MIn) : TrEta := UpperTheory.trace_eta_identity

theorem trEtaPt_of (I : MIn) : TrEtaPt := UpperTheory.trace_eta_pointwise

theorem multUnit_of (I : MIn) : MultUnit := UpperTheory.multiplier_is_unit

theorem trBack_of (I : MIn) : TrBack := UpperTheory.trace_pullback_identity

theorem trUnit_of (I : MIn) : TrUnit := UpperTheory.trace_unit_of_pullback_multiplier (trBack_of I) (multUnit_of I)

theorem trTj_of (I : MIn) : TrTj := UpperTheory.trace_identity_of_tjElement

theorem congCRT_of (I : MIn) : CongCRT := UpperTheory.congruenceCRT_of_latticeGen (latGen_of I)

theorem grpLat_of (I : MIn) : GrpLat := UpperTheory.congruenceSubgroup_isLattice_statement

theorem grpCong_of (I : MIn) : GrpCong := UpperTheory.arithmeticGroup_congruenceSubgroupProperty

theorem baseInv_of (I : MIn) : BaseInv := UpperTheory.quotient_invariant_of_trace_unit_crt (numEx_of I) (qComp_of I) (qIso_of I) (clsEx_of I) (trEta_of I) (trUnit_of I) (congCRT_of I)

theorem piInv_of (I : MIn) : PiInv := UpperTheory.tower_invariant_of_base_invariant_powerCartesian (baseInv_of I) (powCart_of I)

theorem baseSep_of (I : MIn) : BaseSep := UpperTheory.quotient_separated_of_trace_unit_crt (gPull_of I) (qComp_of I) (qIso_of I) (qUniq_of I) (trEta_of I) (trEtaPt_of I) (trUnit_of I) (congCRT_of I)

theorem piZero_of (I : MIn) : PiZero := UpperTheory.tower_trivial_of_quotient_trace_powerCartesian I (qObj_of I) (qComp_of I) (qIso_of I) (qUniq_of I) (trEta_of I) (trUnit_of I) (powCart_of I)

theorem piFet_of (I : MIn) : PiFet := UpperTheory.tower_finiteEtale_of_trivial_powerCartesian (piZero_of I) (powCart_of I)

theorem piSep_of (I : MIn) : PiSep := UpperTheory.tower_separated_of_trivial_powerCartesian (piZero_of I) (baseSep_of I) (powCart_of I)

theorem splitOf_of (I : MIn) : SplitOf := UpperTheory.integralGeometricGalois_splitting

theorem kSCover_of (I : MIn) : KSCover := UpperTheory.tower_covering_of_invariant_finiteEtale_separated (piInv_of I) (piFet_of I) (piSep_of I) (splitOf_of I)

theorem tjIsog_of (I : MIn) : TjIsog := UpperTheory.heckeCorrespondence_isogeny_of_trace_crt (trEta_of I) (trBack_of I) (trTj_of I) (multUnit_of I) (congCRT_of I)

theorem liftEx_of (I : MIn) : LiftEx := UpperTheory.hecke_lift_exists_of_quotient_level (numEx_of I) (qObj_of I) (qComp_of I) (qUniq_of I) (qLev_of I) (tjIsog_of I) (trEta_of I) (congCRT_of I)

theorem liftSep_of (I : MIn) : LiftSep := UpperTheory.hecke_lift_separated_of_lattice_congruence (numEx_of I) (baseInv_of I) (trEta_of I) (trEtaPt_of I) (congCRT_of I) (grpLat_of I) (grpCong_of I)

theorem count_of (I : MIn) : Count := UpperTheory.tower_point_count_statement

theorem tjLies_of (I : MIn) : TjLies := UpperTheory.heckeCorrespondence_lies_in_tower_of_lift_count I (numEx_of I) (clsEx_of I) (powCart_of I) (piInv_of I) (piFet_of I) (liftEx_of I) (liftSep_of I) (count_of I)

theorem stdEx_of (I : MIn) : StdEx := UpperTheory.standard_datum_exists

theorem kSCong_of (I : MIn) : KSCong := UpperTheory.tower_covering_congruence_of_hecke_lies I (siteEx_of I) (numEx_of I) (clsEx_of I) (kSCover_of I) (tjLies_of I)

end UpperTheory.Gal.Int.Geo.CovMain
end
end
