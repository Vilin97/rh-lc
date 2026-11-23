module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
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
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdelicCoreWithoutVolumeNormalisationStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetOfKer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFOAssembledIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdelStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_galoisConjugates_heckeChar_trivialOnRealIdeles : ∀ (D : D7) (Q : Par D) (χ₀ : (AE D)ˣ →* Circle), IsHeckeChar D χ₀ → (∀ a, χ₀ (idF D a) = 1) → (∀ x, FinUnit x → ∃ y : Q.c.F, ((χ₀ x : Circle) : ℂ) = Q.c.F.val.toRingHom y) → ∃ χ : (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle, χ Q.c.F.val.toRingHom = χ₀ ∧ ∀ σ, IsHeckeChar D (χ σ) ∧ (∀ a, χ σ (idF D a) = 1) ∧ MuConj Q.c.F.val.toRingHom σ χ₀ (χ σ) := by
  first | exact @GlobalTheory.HeckeConj.exists_conjugates | exact GlobalTheory.HeckeConj.exists_conjugates | (intros; apply GlobalTheory.HeckeConj.exists_conjugates <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsParPinsCanon

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

noncomputable section

namespace GlobalTheory.Member.ParExist

theorem datLaws_all (D : D7) : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI :=
  fun j hj => ⟨datInt_holds D j,
    { unimod := efW_unimod_holds D j _, rank := latW_rank D j hj, dom := datDom_holds D j hj _ }⟩

def parAtLevel (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
    (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) : Par D where
  H := hostOfRecord D
  l := l
  c :=
    { F := FO D
      fin := inferInstance
      conj := fun τ a => conj_mem_FO D τ a
      zeta_mem := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).zeta_mem
        have h1 : (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))).M' = l.M' := by
          simp [Level.M', levelG, levelOfPs, hl.1, hl.2]
        rw [h1] at h
        exact h
      le := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).le
        have h1 : KA l = KA (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))) := by
          unfold KA
          rw [hl.2]
          rfl
        rw [h1]
        exact h }
  Dw := datumAtLift D _ (datLaws_all D)
  Xo := fun j => Classical.choice (hN D.host.E _ (datumAtLift D _ (datLaws_all D) j) l (datumAtLift_pq_pos D _ (datLaws_all D) j))
  eO := eOf D hF

theorem exists_par_pins_canon (D : D7) (hF : OFull D) (hz : OZeta D)
    (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K))
    (hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) :
    ∃ Q : Par D, Q.Pins ∧ Q.Canon ∧ (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) ∧
      Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  obtain ⟨l, hl, hb⟩ := levelPb_exists D pb hg
  refine ⟨parAtLevel D hF hz GlobalTheory.Moduli.moduli_scheme_exists l hl, ?_, ⟨rfl, fun j hj => ?_⟩, fun j => datumAtLift_pq_pos D _ (datLaws_all D) j, hb⟩
  · refine ⟨⟨rfl, rfl, rfl, tauEmb_sqrt D⟩, hl, eOf_spec D hF, fun j hj => ?_⟩
    show IsDatW D j (datumAtLift D _ (datLaws_all D) j)
    unfold datumAtLift
    rw [dite_eq_left hj]
    exact isDatW_datumOf D _ j _ _
  · show ∃ hP hd, HEq (datumAtLift D _ (datLaws_all D) j) (datumOfRecord D j hj hP hd)
    unfold datumAtLift
    rw [dite_eq_left hj]
    exact ⟨Formalism.IndefR.Fin.factPrincipalDatum, datDom_holds D j hj _, HEq.rfl⟩

end GlobalTheory.Member.ParExist
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCoreJOfChiOKNoVol

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2

theorem exists_coreJ_of_chiOK_noVol : ∀ (D : D7), OFull D → OZeta D → ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) → ∀ chi₀, ChiOK D chi₀ → ∃ J : CoreJ D, LawsJ J ∧ LawsCore J.toCore ∧ J.Q.Canon ∧ J.pb = pb ∧ (∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) ∧ (∀ j, J.chiW j J.σ₀ = chi₀ j) := by
  intro D hO hZ pb hg chi₀ hchi
  classical
  obtain ⟨Q, hP, hCan, hpq, hM⟩ := GlobalTheory.Member.ParExist.exists_par_pins_canon D hO hZ pb hg
  have hle : FO D ≤ Q.c.F := by
    rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := Q.eO.surjective y
    have h : D.what₂.phiO (Q.eO x) = ((x : Q.c.F) : ℂ) := hP.2.2.1 x
    rw [h]
    exact (x : Q.c.F).2
  have key : ∀ j, ∃ χ : (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle,
      χ Q.c.F.val.toRingHom = chi₀ j ∧ (InR D j → ∀ σ,
        IsHeckeChar D (χ σ) ∧ (∀ a, χ σ (idF D a) = 1) ∧
          MuConj Q.c.F.val.toRingHom σ (chi₀ j) (χ σ)) := by
    intro j
    by_cases hj : InR D j
    · obtain ⟨h1, h2, h3⟩ := hchi j hj
      obtain ⟨χ, hχ, hσ⟩ := GlobalTheory.T.exists_galoisConjugates_heckeChar_trivialOnRealIdeles D Q (chi₀ j) h1 h2
        (fun x hx => ⟨⟨_, hle (h3 x hx)⟩, rfl⟩)
      exact ⟨χ, hχ, fun _ => hσ⟩
    · exact ⟨fun _ => chi₀ j, rfl, fun h => absurd h hj⟩
  choose chiW h0 hW using key
  obtain ⟨T, hJ, hC, hp, hQ, hH⟩ := GlobalTheory.T.exists_adelicCore_without_volumeNormalisation D Q hP hpq pb hg hM chiW
    (fun j hj σ _ => by rw [h0 j]; exact hW j hj σ)
  subst hQ
  refine ⟨T, hJ, hC, hCan, hp, hpq, fun j => ?_⟩
  rw [eq_of_heq hH]
  exact h0 j

end GlobalTheory.FinalJoin2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallField

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreExact

theorem locK_mem_of_values : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (M : IntermediateField ℚ ℂ), GlobalTheory.Mem.Fld.valueField χ 0 ≤ M → (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ), ((χ.locK P k : ℂˣ) : ℂ) ∈ M :=
  fun _ _ _ χ _ hv hi P _ => GlobalTheory.HeckeValField.mem_unitsIn.1 (GlobalTheory.HeckeValField.loc_mem χ hv hi P _)

theorem char_mem_of_values : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → ∀ M : IntermediateField ℚ ℂ, GlobalTheory.Mem.Fld.valueField χ 0 ≤ M → (∀ k : D.host.Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((c x : Circle) : ℂ) ∈ M := by
  intro D c χ hc M hv hi x hx
  obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom x)
  rw [hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact prod_mem fun P _ => locK_mem_of_values D.host.E χ M hv hi P (k P)

theorem KsC_eq (X : Stages) : X.B.KsC = FO X.toD7 := by
  ext z
  rw [Base.mem_KsC, mem_FO_assembled_iff]

theorem exists_core_exact : ∀ (X : Stages) (f : Fr X.B.toPre), Fld.charField f ≤ X.B.KsC → Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) → VolTieG X.toD7 → ∃ (C : CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL), CorePin C.toCore (Fr.at X f).P.pb ∧ (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧ (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧ (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧ (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧ LawsJ C ∧ Formalism.IndefR.FWT.AlgTie C ∧ Formalism.L2.Host.ValLL X.toD7 (Fr.at X f) ∧ ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Fr.at X f → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 → ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) := by
  intro X f hch hv _
  obtain ⟨J, hJ, hC, hCan, hp, hpq, -⟩ := GlobalTheory.FinalJoin2.exists_coreJ_of_chiOK_noVol X.toD7 (hermitianCodeWordStages_ringOfIntegers_full X)
    (hermitianCodeWordStages_has_rootOfUnity X) f.P.pb f.P.pb_over _ (GlobalTheory.FinalJoin.chiOK_one X.toD7)
  have hP : J.Q.PinField := hJ.pins.2.2.1
  letI := Formalism.IndefR.FWT.algTop J hP
  have ha : Formalism.IndefR.FWT.AlgTie J := Formalism.IndefR.FWT.algTie_algTop J hP

  have hemb : ∀ y : J.Q.c.F, X.toD7.what₂.embLL (algebraMap J.Q.c.F X.toD7.what₂.LL y) = (y : ℂ) := by
    have h : X.toD7.what₂.embLL.comp (algebraMap J.Q.c.F X.toD7.what₂.LL) = J.Q.c.F.val.toRingHom :=
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 J.Q.c.F)) (RingHom.ext fun x =>
        (congrArg X.toD7.what₂.embLL (ha x)).trans (hP x))
    exact fun y => RingHom.congr_fun h y

  have hle : ∀ y : J.Q.c.F, (y : ℂ) ∈ FO X.toD7 := by
    intro y
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 J.Q.c.F) y
    have hi : ∀ a : 𝓞 J.Q.c.F, ((a : J.Q.c.F) : ℂ) ∈ FO X.toD7 := fun a => by
      rw [← hP a]
      exact phiO_mem_FO _ _
    rw [IntermediateField.coe_div]
    exact div_mem (hi a) (hi b)
  have hge : ∀ z ∈ FO X.toD7, ∃ y : J.Q.c.F, (y : ℂ) = z := by
    intro z hz
    have hle' : FO X.toD7 ≤ J.Q.c.F := by
      rw [FO, IntermediateField.adjoin_le_iff]
      rintro _ ⟨w, rfl⟩
      obtain ⟨x, rfl⟩ := J.Q.eO.surjective w
      have h : X.toD7.what₂.phiO (J.Q.eO x) = ((x : J.Q.c.F) : ℂ) := hP x
      rw [h]
      exact (x : J.Q.c.F).2
    exact ⟨⟨z, hle' hz⟩, rfl⟩

  have hback : ∀ z : X.toD7.what₂.LL, X.toD7.what₂.embLL z ∈ FO X.toD7 →
      ∃ y : J.Q.c.F, algebraMap J.Q.c.F X.toD7.what₂.LL y = z := by
    intro z hz
    obtain ⟨y, hy⟩ := hge _ hz
    exact ⟨y, X.toD7.what₂.embLL.injective ((hemb y).trans hy)⟩
  refine ⟨J, inferInstance, ⟨hC, hCan, hpq, hp⟩, hemb, fun y => ?_, fun x hx => hback x ?_, fun x => hback _ ?_,
    hJ, ha, hv.toLL, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := (mem_FO_assembled_iff X _).1 (hle y)
    have : algebraMap J.Q.c.F X.toD7.what₂.LL y = x := X.toD7.what₂.embLL.injective (((hemb y).trans hx'.symm))
    rw [this]
    exact X.B.Ks_le hx
  · exact (mem_FO_assembled_iff X _).2 ⟨x, hx, rfl⟩
  · rw [show X.toD7.what₂.embLL (X.toD7.embE x) = X.toD7.host.φ₀ x from RingHom.congr_fun X.toD7.embE_φ₀ x]
    exact phi0_mem_coeff_field _ x
  · intro T' L μ hL hLC i x hx
    have hmem : ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ FO X.toD7 := by
      refine char_mem_of_values X.toD7 _ _ (hL.mu0 i) (FO X.toD7) ?_ ?_ x hx
      · rw [hLC, ← KsC_eq]
        exact (le_iSup (fun j => Fld.valueField (f.mu0 j) 0) i).trans
          (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans hch))))
      · intro k
        obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
        choose z hz using fun g => (X.toD7.hc (X.toD7.eTau.symm g)).e_int i
        have hnz : n = fun g => 2 * -z g := funext fun g => by
          have h1 := hn g
          simp only [Formalism.L2.Host.eExp, hz] at h1
          exact_mod_cast h1
        rw [hnz] at hi
        rw [hi k]
        refine prod_mem fun g _ => ?_
        rw [GlobalTheory.RefCharValues.sign_zpow_even _ ((map_ne_zero _).2 k.ne_zero)]
        exact zpow_mem (div_mem (conj_mem_FO _ _ _) (conj_mem_FO _ ((starRingEnd ℂ).comp _) _)) _
    obtain ⟨y, hy⟩ := hge _ hmem
    exact ⟨y, by rw [hemb, hy]⟩

end GlobalTheory.CoreExact
end
end
