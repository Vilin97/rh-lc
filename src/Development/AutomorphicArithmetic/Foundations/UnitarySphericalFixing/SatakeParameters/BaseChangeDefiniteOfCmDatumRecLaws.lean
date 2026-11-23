module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.UnitaryReadS
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseChangeDistinctness
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DivisibleGroupTowerCompatibility
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSpeh
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfNodupSumMultisetOfEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TwoAtCharZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameInert
public import GroundTheory.GlobalFields.KummerTheory.Splitting
public import GroundTheory.GlobalFields.TateThesis.DegreeOnePrimes
public import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRSplit
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
import Mathlib.NumberTheory.RamificationInertia.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC

namespace GlobalTheory.DefiniteBCFrozen

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

theorem isBC_of_isBaseChange {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    {B : NBC A} {j : ℕ} {π : B.AU j} {Pa : List (Part A.CG)}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness.IsBaseChange B j π Pa) : SphericalInertData.IsBC N A B j π Pa := by
  refine ⟨fun p hp => ⟨(h.discrete p hp).1, (h.discrete p hp).2, h.conjSelfDual p hp⟩, ?_, h.rank, h.split,
    h.inert, h.inf⟩
  refine h.distinct.map ?_
  rintro ⟨a, π, d⟩ ⟨a', π', d'⟩ hh
  simp only [Prod.mk.injEq, Sigma.mk.injEq] at hh
  obtain ⟨⟨rfl, h2⟩, rfl⟩ := hh
  cases h2
  rfl

end GlobalTheory.DefiniteBCFrozen

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDegreeOnePrimeNotSplitsCompletely

section

@[expose] public section

open NumberField IsDedekindDomain GroundTheory.Global

namespace GlobalTheory.CompanionTheory.Density


open Filter Topology Set in
theorem exists_degreeOnePrime_not_splitsCompletely :
    ∀ (L F M : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], 1 < Module.finrank F M →
      ∀ B : Set (HeightOneSpectrum (𝓞 F)), B.Finite →
        ∃ v ∈ degreeOnePrimes L F, v ∉ B ∧ ¬ SplitsCompletely M v := by
  intro L F M _ _ _ _ _ _ _ _ _ hdeg B hB
  by_contra hcon
  push Not at hcon
  have hfin : (degreeOnePrimes L F \ ({v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} ∩ degreeOnePrimes L F)).Finite := by
    apply hB.subset
    intro v hv
    by_contra hvB
    exact hv.2 ⟨hcon v hv.1 hvB, hv.1⟩
  have hinter : ({v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} ∩
      degreeOnePrimes L F).HasDirichletDensity 1 :=
    (GroundTheory.Global.hasDirichletDensity_iff_of_subset_of_isBoundedUnder
      Set.inter_subset_right
      (GroundTheory.Global.isBoundedUnder_primeIdealZetaSum_of_finite hfin) 1).mpr
      (GroundTheory.Global.hasDirichletDensity_degreeOnePrimes (K := L) (L := F))
  have hsplit : {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}.HasDirichletDensity 1 :=
    (GroundTheory.Global.hasDirichletDensity_inter_degreeOnePrimes_iff
      (K := L) _ 1).mp hinter
  have hSd := GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely (K := F) (L := M)
  have heq : (1 : ℝ) = 1 / Module.finrank F M :=
    hsplit.dirichletDensity_eq.symm.trans hSd.dirichletDensity_eq
  have h2 : 2 ≤ Module.finrank F M := hdeg
  have hfr : (2 : ℝ) ≤ Module.finrank F M := by exact_mod_cast h2
  have hq : (1 : ℝ) / Module.finrank F M ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfr
  linarith

end GlobalTheory.CompanionTheory.Density
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.InertB

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Inert

namespace ExistsNonSplitPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_of_not_isSplitAt {Sec : Set (Pl E)} (hS : IsSection Sec) {w : Pl E} (hw : ¬ IsSplitAt w) :
    w ∈ Sec := by
  obtain ⟨u, ⟨hu, hue⟩, -⟩ := hS w
  by_cases h : u = w
  · exact h ▸ hu
  · exact absurd ⟨u, h, hue⟩ hw

theorem exists_not_isSplitAt (B : Set (Pl E)) (hB : B.Finite) : ∃ w : Pl E, w ∉ B ∧ ¬ IsSplitAt w := by
  set F := maximalRealSubfield E
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  obtain ⟨v, -, hvB, hv⟩ := GlobalTheory.CompanionTheory.Density.exists_degreeOnePrime_not_splitsCompletely F F E
    (by omega) ((fun w : Pl E => w.under (𝓞 F)) '' B) (hB.image _)
  haveI := v.isMaximal
  obtain ⟨⟨P, hP⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 E)
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot hP
  let w : Pl E := ⟨P, hP.1, hP0⟩
  have hwv : w.under (𝓞 F) = v := HeightOneSpectrum.ext (hP.2.over).symm
  refine ⟨w, fun hw => hvB ⟨w, hw, hwv⟩, ?_⟩
  rintro ⟨u, hu, hue⟩
  apply hv
  rw [GroundTheory.Global.splitsCompletely_iff_ncard_primesOver, h2]
  haveI : NoZeroSMulDivisors (𝓞 F) (𝓞 E) := ⟨fun {c x} e => by
    rw [Algebra.smul_def, mul_eq_zero, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))] at e
    exact e⟩
  have hle : (v.asIdeal.primesOver (𝓞 E)).ncard ≤ 2 := by
    have h := Ideal.card_primesOverFinset_le_finrank (𝓞 E) F E v.ne_bot
    rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset v.ne_bot, h2] at h
    exact h
  have hmem : ∀ x : Pl E, x.under (𝓞 F) = v → x.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := fun x hx =>
    ⟨x.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hx).symm⟩⟩
  have hge : 2 ≤ (v.asIdeal.primesOver (𝓞 E)).ncard := by
    have hne : u.asIdeal ≠ w.asIdeal := fun e => hu (HeightOneSpectrum.ext e)
    rw [← Set.ncard_pair hne]
    refine Set.ncard_le_ncard ?_ (IsDedekindDomain.primesOver_finite _ _)
    rintro x (rfl | rfl)
    · exact hmem u (hue.trans hwv)
    · exact hmem w hwv
  omega

end ExistsNonSplitPlace

theorem inertPlaceEx : InertPlaceEx := by
  intro E _ _ _ _ n π hπ Sec hS X
  have hfin : {w : Pl E | ¬ IsUnramU π w}.Finite :=
    Filter.eventually_cofinite.1 (PositivityTheory.Rg.BcB.F.Rig.eventually_isUnramU hπ)
  obtain ⟨w, hwB, hw⟩ := ExistsNonSplitPlace.exists_not_isSplitAt ((X : Set (Pl E)) ∪ {w | ¬ IsUnramU π w})
    (X.finite_toSet.union hfin)
  refine ⟨w, ExistsNonSplitPlace.mem_of_not_isSplitAt hS hw, fun h => hwB (Or.inl h), hw, ?_⟩
  by_contra h
  exact hwB (Or.inr h)

end PositivityTheory.Rg.BcB.F.Inert

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.BaseChangeDefiniteOfCmDatumRecLaws

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN UpperTheory.BaseChangeIdentities UpperTheory.Zero.LLC

namespace UpperTheory.One.M.Ud

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

attribute [local instance] host_isCMField
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem part {rc : RecMap A} (hMW : DiscCsd H.E) (hS : RecSpeh rc) (hC : CuspReadG rc) {n : ℕ}
    (hn : 0 < n) {V : Submodule ℂ (Sm H.E n)} (hV : IsDiscrete V) (hc : CsdAsc V)
    (hG : ∀ w : PlE H, ∃ σ', IsLocCompGL V w σ' ∧ Good (GlobalTheory.BCSupport.clsOf σ')) :
    ∃ p : Part A.CG, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π ∧ p.a * p.d = n ∧
      (∀ w σ, IsLocCompGL V w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ ∧ rc w n σ = spehLoc N A p w) ∧
      ∀ τ m, HasInfCharGL V τ m → m = spehInf p.d (A.infG p.π τ) := by
  obtain ⟨a, d, h, P, h1, h2, h3⟩ := hMW n hn V hV hc
  have had : a * d = n := by simpa [mul_comm] using h
  have ha : 1 ≤ a := Nat.pos_of_mul_pos_right (had ▸ hn)
  have hPG : ∀ w σ, P.IsLocComp w σ → Good (GlobalTheory.BCSupport.clsOf σ) := fun w σ hσ => by
    obtain ⟨σ', hσ', hg⟩ := hG w
    obtain ⟨-, σ₀, l, -, q⟩ := h2 w σ' hσ'
    have e : GlobalTheory.BCSupport.clsOf σ = GlobalTheory.BCSupport.clsOf σ₀ :=
      GlobalTheory.LocGL.IrrGL.of_eq_of.2 (GlobalTheory.CuspRep.LocUniq.isLocComp_unique P w σ σ₀ hσ l)
    rw [e]
    exact GlobalTheory.DefiniteBCGood.good_of_isSpehQuot h σ₀ σ' (Nat.pos_of_mul_pos_left (had ▸ hn)) q hg
  obtain ⟨π, c1, c2, c3⟩ := hC a P ha h1 hPG
  refine ⟨⟨a, π, d⟩, ha, Nat.pos_of_mul_pos_left (had ▸ hn), c1, had, fun w σ' hσ' => ?_, fun τ m' hm' => ?_⟩
  · obtain ⟨u, σ, l, u', q⟩ := h2 w σ' hσ'
    refine ⟨u, ?_⟩
    rw [hS w a d n h P σ σ' l u' q, ← c2 w σ l, spehLoc_eq]
  · obtain ⟨m, hm, rfl⟩ := h3 τ m' hm'
    rw [c3 τ m hm]


attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem parts {rc : RecMap A} (hNT : DefiniteN)
    (hMW : DiscCsd H.E)
    (hP : RecProd rc) (hS : RecSpeh rc) (hSat : RecSatake rc) (hC : CuspReadG rc)
    {n : ℕ} (hn : 1 ≤ n) {U : Submodule ℂ (UA H.E n → ℂ)} (hU : IsAutRepU U) (hGs : GlobalTheory.DefiniteBCGood.GoodSplitU U)
    (hSat' : ∀ w, ¬ IsSplitPl H w → ∃ α, IsSatAt U w α) :
    ∃ Pa : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧ rankIso N A Pa = n ∧
      (∀ w, IsSplitPl H w → ∃ σ : LocIrr w n,
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ isoLoc N A Pa w = rc w n σ) ∧
      (∀ w α, IsSatAt U w α → A.unr (isoLoc N A Pa w) ∧
        A.frobEig (isoLoc N A Pa w) = ubc n (Finset.univ.val.map fun i => (α i : ℂ))) ∧
      ∀ τ lam, HasWeightAt U τ lam → Pa.Nodup ∧ isoInf N A Pa τ = infOfWeight lam ∧
        isoInf N A Pa (ComplexEmbedding.conjugate τ) = (infOfWeight lam).map (fun z => -z) := by
  obtain ⟨c, d, h, V, σ, m, bc⟩ := hNT H.E (host_unramified H) n hn U hU
  have hgood : ∀ i w, Good (GlobalTheory.BCSupport.clsOf (σ i w)) := fun i w => by
    by_cases hw : IsSplitPl H w
    · have hc := bc.split w (isSplitAt_of_isSplitPl hw)
      exact GlobalTheory.BCSupport.good_of_good_locProd h w (σ · w) hc.1
        (hGs w hw ⟨_, locProd h w (σ · w), GlobalTheory.SmGL.isSmooth_parInd _ _, hc.1⟩ hc) i
    · obtain ⟨α, s, ϖ, q, e1, e2, e3⟩ := hSat' w hw
      exact good_of_sph h w (σ · w) (bc.unram w (GlobalTheory.BcSpehCompare.isUnramU_of_hasSatAt e1 e2.2.1 e3)) i
  choose p p1 p2 p3 p4 p5 p6 using fun i =>
    Ud.part hMW hS hC (bc.pos i) (bc.discrete i) (bc.csd i) (fun w => ⟨σ i w, bc.loc i w, hgood i w⟩)
  let Q : ∀ w, LocIrr w n := fun w =>
    { V := _
      ρ := locProd h w (σ · w)
      smooth := GlobalTheory.SmGL.isSmooth_parInd _ _
      irred := UpperTheory.Lit.Mix.multiProd_at (@UpperTheory.Lit.Mix.twoAt_charZero _ _ _ _ _ (charZero_of_injective_algebraMap (algebraMap H.E _).injective)) _ (fun i => (σ i w).smooth) (fun i => (σ i w).irred)
        fun i => (p5 i w _ (bc.loc i w)).1 }
  have hloc : ∀ w, isoLoc N A (List.ofFn p) w = rc w n (Q w) := fun w => by
    rw [hP w c n d h (σ · w) (Q w) ⟨.refl _⟩]
    simp only [fun i => (p5 i w _ (bc.loc i w)).2]
    rw [lpSumList, ← Function.comp_def (fun q => spehLoc N A q w) p, ← List.map_ofFn, List.foldr_map]
    rfl
  have hinf : ∀ τ, isoInf N A (List.ofFn p) τ = ∑ i, m i τ := fun τ => by
    rw [isoInf_eq, List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun i _ => (p6 i τ _ (bc.inf i τ)).symm
  refine ⟨List.ofFn p, fun q hq => ?_, ?_, fun w hw => ⟨Q w, bc.split w (isSplitAt_of_isSplitPl hw), hloc w⟩,
    fun w α ⟨s, ϖ, q, e1, e2, e3⟩ => ?_, fun τ lam hl => ⟨List.nodup_ofFn.2 fun i j e => ?_, ?_, ?_⟩⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hq
    exact ⟨p1 i, p2 i, p3 i⟩
  · rw [rankIso, List.map_ofFn, List.sum_ofFn, ← h]
    exact Finset.sum_congr rfl fun i _ => p4 i
  · rw [hloc, ← ubc_eq_map_inv]
    exact hSat w n (Q w) _ (bc.inert w s ϖ q e1 e2 α e3)
  · refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (fun h0 => (bc.pos i).ne' ?_) ?_
    · rw [← (bc.inf i τ).1]
      exact Multiset.card_eq_zero.2 h0
    · rw [p6 i τ _ (bc.inf i τ), p6 j τ _ (bc.inf j τ), e]
  · rw [hinf, bc.weight τ lam hl]
  · rw [hinf, bc.weight _ _ (hasWeightAt_conjugate hn hl), infOfWeight_dual]

theorem bcAt (B : NBC A) (rc : RecMap A) (hNT : DefiniteN)
    (hMW : DiscCsd H.E)
    (hP : RecProd rc) (hS : RecSpeh rc) (hSat : RecSatake rc) (hC : CuspReadG rc) (hU : UnitaryReadS B rc) :
    GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness.BaseChangeDefinite_at B := by
  intro j h1 h2 π hπ
  obtain ⟨U, u1, u2, u3, u4⟩ := hU j h1 h2 π
  obtain ⟨w₀, -, hw₀'⟩ := PositivityTheory.Rg.BcB.F.Inert.ExistsNonSplitPlace.exists_not_isSplitAt (E := H.E) ∅ Set.finite_empty
  have hw₀ : ¬ IsSplitPl H w₀ := fun h => hw₀' (isSplitAt_of_isSplitPl h)
  have hn : 1 ≤ R.nV := by
    have := R.rank_add_five_le
    simp only [Ranks.nV]
    omega
  obtain ⟨Pa, a1, a2, a3, a4, a5⟩ := Ud.parts hNT hMW hP hS hSat hC hn u1 (u3 w₀ hw₀ (hπ w₀ hw₀)).1
    fun w hw => (u3 w hw (hπ w hw)).2.imp fun _ h => h.1
  refine ⟨Pa, fun p hp => ⟨(a1 p hp).1, (a1 p hp).2.1⟩, fun p hp => (a1 p hp).2.2, ?_, a2, fun w hw => ?_,
    fun w hw => ?_, fun τ => ?_, fun τ _ => ?_⟩
  · obtain ⟨lam, hl, -⟩ := u4 H.φ₀
    exact (a5 _ lam hl).1
  · obtain ⟨σ, s1, s2⟩ := a3 w hw
    rw [s2, u2 w hw σ s1]
  · obtain ⟨α, s1, s2⟩ := (u3 w hw (hπ w hw)).2
    rw [s2]
    exact a4 w α s1
  · obtain ⟨lam, hl, e⟩ := u4 τ
    rw [e, (a5 τ lam hl).2.1]
  · obtain ⟨lam, hl, e⟩ := u4 τ
    rw [e, (a5 τ lam hl).2.2]

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions

theorem baseChangeDefinite_of_cmDatum_recLaws : ∀ (D : D7) (rc : RecMap D.naut), DefiniteN →
    DiscCsd D.host.E → RecProd rc → RecSpeh rc →
    RecSatake rc → CuspReadG rc → UnitaryReadS D.nbc rc → SphericalInertData.Conclusion1 D := by
  intro D rc hNT hMW hP hS hSat hC hU _ _ j h1 h2 _ _ π hπ
  obtain ⟨Pa, hPa⟩ := Ud.bcAt D.nbc rc hNT hMW hP hS hSat hC hU j h1 h2 π hπ
  exact ⟨Pa, GlobalTheory.DefiniteBCFrozen.isBC_of_isBaseChange hPa⟩

end UpperTheory.One.M.Ud

end
end
end
