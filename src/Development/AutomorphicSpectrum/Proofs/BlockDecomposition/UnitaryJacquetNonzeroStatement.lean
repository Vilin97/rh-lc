module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasselmanFirstPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContractionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUniqueStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsDomMonoid
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatumStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedVectorZeroOfDualStatement
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakePowerNonvanishingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabFiniteIndexOfSmooth

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormHeckeVecDosetInd

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.SphComp

theorem form_heckeVec_dosetInd {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}
    (hK : IsCommensurated K) (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ K)
    (l : Module.Dual ℂ V) (hl : ∀ k ∈ K, l ∘ₗ ρ k = l) (g : G) :
    l (heckeVec ρ K (dosetInd ℂ K g) x) =
      (Nat.card {c : G ⧸ K // (c.out : G) ∈ DoubleCoset.doubleCoset g (K : Set G) K} : ℂ) * l (ρ g x) := by
  classical
  set D := DoubleCoset.doubleCoset g (K : Set G) K with hD
  have hm := Formalism.UG.Final.DosetIndMem G K ℂ g
  have hfin : {c : G ⧸ K | c.out ∈ D}.Finite := by
    refine (Formalism.UG.P.finite_support_cosets hK hm.2).subset ?_
    intro c hc
    have h' : c.out ∈ D := hc
    simp only [Set.mem_setOf_eq, dosetInd]
    rw [Set.indicator_of_mem h']
    simp
  have hterm : ∀ γ ∈ D, l (ρ γ x) = l (ρ g x) := by
    intro γ hγ
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hγ
    have e := LinearMap.congr_fun (hl a ha) (ρ g (ρ b x))
    simp only [LinearMap.comp_apply] at e
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, GlobalTheory.LGrp.mem_fixed.1 hx _ hb]
  have e1 : l (heckeVec ρ K (dosetInd ℂ K g) x) =
      ∑ᶠ c : G ⧸ K, l (dosetInd ℂ K g c.out • ρ c.out x) :=
    l.toAddMonoidHom.map_finsum (finite_heckeVec hK hm ρ x)
  have e2 : (fun c : G ⧸ K => l (dosetInd ℂ K g c.out • ρ c.out x)) =
      Set.indicator {c : G ⧸ K | c.out ∈ D} (fun _ => l (ρ g x)) := by
    funext c
    by_cases h : c.out ∈ D
    · have h1 : dosetInd ℂ K g c.out = 1 := by
        simp only [dosetInd]
        rw [Set.indicator_of_mem h]
        simp
      rw [Set.indicator_of_mem (show c ∈ {c : G ⧸ K | c.out ∈ D} from h), h1, one_smul, hterm _ h]
    · have h1 : dosetInd ℂ K g c.out = 0 := by
        simp only [dosetInd]
        exact Set.indicator_of_notMem h _
      rw [Set.indicator_of_notMem (show c ∉ {c : G ⧸ K | c.out ∈ D} from h), h1, zero_smul, map_zero]
  have hc : Nat.card {c : G ⧸ K // c.out ∈ D} = hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.card_coe_set_eq {c : G ⧸ K | c.out ∈ D}
  rw [e1, e2, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hfin, hc]
  simp

theorem sphCompare : PositivityTheory.SphericalProduct.SphCompare := by
  intro L _ _ ϖ σ q n hU V _ _ ρ α v₀ hv l hl g
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n
  have e := congrArg l (hv.2.2 _ (Formalism.UG.Final.DosetIndMem _ (KU σ n) ℂ g))
  rw [map_smul, smul_eq_mul, form_heckeVec_dosetInd hK ρ hv.2.1 l hl g] at e
  exact e

end GlobalTheory.CompanionTheory.SphComp

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentOfProjectionZero

section

@[expose] public section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem hecke_pow_kills_of_proj_eq_zero : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
    IsSmooth π → ∀ t : D.T, D.IsStrDom t → ∀ U : Module.End ℂ (fixed π D.J),
    PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → ∀ v : fixed π D.J, D.proj π (v : V) = 0 →
    ∃ j : ℕ, (U ^ j) v = 0 := by
  intro G _ _ _ D V _ _ π hπ t ht U hU v hv

  have hdom : ∀ r : ℕ, D.IsDom (t ^ r) := by
    intro r
    induction r with
    | zero => simpa using (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).1
    | succ r ih =>
      rw [pow_succ]
      exact (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).2 _ _ ih ht.1

  have hecke : ∀ r : ℕ, PositivityTheory.Lbc.IsHeckeOpG π D.J ((t ^ r : D.T) : G) (U ^ r) := by
    intro r
    induction r with
    | zero =>
      intro w l _
      simp
    | succ r ih =>
      rw [pow_succ, pow_succ U]
      exact GlobalTheory.T.casselman_first_property G D V π hπ (t ^ r) t (hdom r) ht.1 _ _ ih hU

  have key : ∀ u ∈ twKer π D.N 1, ∃ R : ℕ, ∀ r ≥ R,
      ∀ l : Module.Dual ℂ V, (∀ x ∈ D.J, l ∘ₗ π x = l) → l (π ((t : G) ^ r) u) = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨n, w, rfl⟩ := hu
      obtain ⟨R, hR⟩ := ht.2.1 (n : G) n.2
      refine ⟨R, fun r hr l hl => ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
      have hmem : (t : G) ^ (R + j) * (n : G) * ((t : G) ^ (R + j))⁻¹ ∈ D.J ⊓ D.N := by
        have := (hdom j).1 _ hR
        convert this using 1
        simp only [Subgroup.coe_pow]
        rw [add_comm R j, pow_add]
        group
      have hx := hl _ hmem.1
      have hy := LinearMap.congr_fun hx (π ((t : G) ^ (R + j)) w)
      simp only [LinearMap.comp_apply] at hy
      have hz : π ((t : G) ^ (R + j) * (n : G) * ((t : G) ^ (R + j))⁻¹) (π ((t : G) ^ (R + j)) w)
          = π ((t : G) ^ (R + j)) (π (n : G) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [hz] at hy
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hy, sub_self]
    | zero => exact ⟨0, fun r _ l _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA⟩ := ha
      obtain ⟨B, hB⟩ := hb
      refine ⟨max A B, fun r hr l hl => ?_⟩
      rw [map_add (f := _), map_add (f := _), hA r (le_trans (le_max_left _ _) hr) l hl,
        hB r (le_trans (le_max_right _ _) hr) l hl, add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA⟩ := ha
      refine ⟨A, fun r hr l hl => ?_⟩
      rw [map_smul, map_smul, hA r hr l hl, smul_zero]
  obtain ⟨R, hR⟩ := key _ ((Submodule.Quotient.mk_eq_zero _).1 hv)
  refine ⟨R, ?_⟩
  have h0 : (((U ^ R) v : fixed π D.J) : V) = 0 := by
    refine GlobalTheory.T.fixed_vector_zero_of_dual G D.J D.isCompact_J V π hπ _ ((U ^ R) v).2 fun l hl => ?_
    rw [← hecke R v l hl, Subgroup.coe_pow]
    exact hR R le_rfl l hl
  exact Subtype.ext h0

end GlobalTheory.CompanionTheory.Cass
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetNonzero

section

@[expose] public section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.JacSph

theorem hecke_pow {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : CassData G) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hπ : IsSmooth π) (t : D.T) (ht : D.IsDom t)
    (U : Module.End ℂ (fixed π D.J)) (hU : PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U) (r : ℕ) :
    D.IsDom (t ^ r) ∧ PositivityTheory.Lbc.IsHeckeOpG π D.J ((t ^ r : D.T) : G) (U ^ r) := by
  induction r with
  | zero =>
    refine ⟨by simpa using (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).1, ?_⟩
    intro w l _
    simp
  | succ r ih =>
    rw [pow_succ, pow_succ U]
    exact ⟨(GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).2 _ _ ih.1 ht,
      GlobalTheory.T.casselman_first_property G D V π hπ (t ^ r) t ih.1 ht _ _ ih.2 hU⟩

theorem jacNeU : JacNeU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hu hadm _ hsat
  obtain ⟨v₀, hv₀⟩ := hsat.exists_vec
  have hfixK : v₀ ∈ fixed ρ (KU σ n) := hv₀.2.1
  refine ⟨v₀, fun hjac => ?_, fun k hk _ => ?_⟩
  · obtain ⟨D, hJ, hN, hNm, hT⟩ := GlobalTheory.T.iwahori_unipotent_datum L ϖ σ q hu n
    obtain ⟨hKo, hKc, hIK, t₀, ht₀d, ht₀s⟩ := GlobalTheory.CompanionTheory.KUFactsU.kuFacts L ϖ σ q n hu
    have hstr : D.IsStrDom ⟨t₀, (hT _).2 ht₀d⟩ :=
      (GlobalTheory.T.dominant_unipotent_contraction L ϖ σ q hu n D hJ hN hNm hT ⟨t₀, (hT _).2 ht₀d⟩).2 ht₀s
    have hker : twKer ρ D.N 1 = jacU ρ := twKer_eq_jacSub D _ hN ρ
    have hproj0 : D.proj ρ v₀ = 0 := by
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      rw [hker]
      exact hjac
    have hJK : ∀ x ∈ D.J, x ∈ KU σ n := fun x hx => hIK (hJ ▸ hx)
    have hfixJ : v₀ ∈ fixed ρ D.J :=
      GlobalTheory.LGrp.mem_fixed.2 fun x hx => GlobalTheory.LGrp.mem_fixed.1 hfixK x (hJK x hx)
    obtain ⟨U, hU, -⟩ := GlobalTheory.T.hecke_character_exists_unique (GU σ n) D.J D.isOpen_J D.isCompact_J V ρ hadm.1 t₀
    obtain ⟨j₀, hj₀⟩ := GlobalTheory.CompanionTheory.Cass.hecke_pow_kills_of_proj_eq_zero (GU σ n) D V ρ hadm.1 _ hstr U hU
      ⟨v₀, hfixJ⟩ hproj0
    obtain ⟨l, hlK, hl1⟩ := GlobalTheory.CompanionTheory.KAvg.kInvForm (GU σ n) (KU σ n) hKo hKc V ρ hadm.1 v₀ hfixK hv₀.1
    obtain ⟨j, hj, hS⟩ := GlobalTheory.T.satake_power_nonvanishing L ϖ σ q n hu α t₀ ht₀d ht₀s j₀
    have hUj : (U ^ j) ⟨v₀, hfixJ⟩ = 0 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [add_comm, pow_add, Module.End.mul_apply, hj₀, map_zero]
    have hl0 : l (ρ (t₀ ^ j) v₀) = 0 := by
      have h := (hecke_pow D ρ hadm.1 _ hstr.1 U hU j).2 ⟨v₀, hfixJ⟩ l fun x hx => hlK x (hJK x hx)
      rw [hUj] at h
      simpa using h
    have hc := GlobalTheory.CompanionTheory.SphComp.sphCompare L ϖ σ q n hu V ρ α v₀ hv₀ l hlK (t₀ ^ j)
    rw [hl0, mul_zero, hl1, mul_one] at hc
    exact hS hc.symm
  · rw [GlobalTheory.LGrp.mem_fixed.1 hfixK k hk, sub_self]
    exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.JacSph
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetNonzeroStatement

section

@[expose] public section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.unitary_jacquet_nonzero : PositivityTheory.SphericalProduct.JacNeU := by
  first | exact @GlobalTheory.CompanionTheory.JacSph.jacNeU | exact GlobalTheory.CompanionTheory.JacSph.jacNeU | (intros; apply GlobalTheory.CompanionTheory.JacSph.jacNeU <;> assumption)
end
end
