module

public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.PrimaryComponentCohomologyEqBotOfScdpLt
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.COnePropertyFiniteExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjectiveStatement
public import GroundTheory.TateCohomology.CohTrivial
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsenAlgebraicExtensionRatFunc
public import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Scalars
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.DimensionSylow
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.HaveILetI
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Brauer
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.KummerOpen

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.COnePropertyFiniteExtensionStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.c_one_property_finite_extension : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], (∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0) → (∀ (n d : ℕ) (f : MvPolynomial (Fin n) L), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → L, x ≠ 0 ∧ MvPolynomial.eval x f = 0) := by
  first | exact @GlobalTheory.c_one_of_finite_extension | exact GlobalTheory.c_one_of_finite_extension | (intros; apply GlobalTheory.c_one_of_finite_extension <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.COneH2UnitsSubsingleton

section

@[expose] public section

open IsLocalRing

open CategoryTheory Limits groupCohomology GroundTheory.GroupCoh IntermediateField

namespace GlobalTheory

theorem c_one_h2_units_subsingleton : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L], (∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0) → Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) := by
  intro K L _ _ _ _ _ hC
  classical
  let A := Rep.ofAlgebraAutOnUnits K L
  have h0 : ∀ (S : Subgroup (L ≃ₐ[K] L)) [Fintype S],
      IsZero (tateCohomology (Rep.res S.subtype A) 0) := by
    intro S _
    refine isZero_tateCohomology_zero_of_forall _ fun m hm => ?_
    let u : Lˣ := Additive.toMul m
    have hu : (u : L) ∈ fixedField S := fun s => congrArg Units.val (hm s)
    have hCF := GlobalTheory.T.c_one_property_finite_extension K (fixedField S) hC
    have hne : (⟨(u : L), hu⟩ : fixedField S) ≠ 0 := fun h => u.ne_zero (congrArg Subtype.val h)
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass (fixedField S) L hCF _ hne
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hx
      exact hne hx.symm
    let y : Rep.res S.subtype A := Additive.ofMul (Units.mk0 x hx0)
    refine ⟨y, ?_⟩
    have e1 : (Rep.res S.subtype A).ρ.norm y = ∑ s : S, (Rep.res S.subtype A).ρ s y := by
      first
        | rw [Representation.norm, LinearMap.coeFn_sum, Finset.sum_apply]
        | simp [Representation.norm]
    have e2 : (Additive.ofMul (∏ s : S, (s : L ≃ₐ[K] L) • Units.mk0 x hx0) : Additive Lˣ) =
        ∑ s : S, (Rep.res S.subtype A).ρ s y := ofMul_prod _ _
    rw [e1, ← e2]
    change Additive.ofMul _ = Additive.ofMul u
    congr 1
    apply Units.ext
    rw [Units.coe_prod]
    have h := Algebra.norm_eq_prod_automorphisms (fixedField S) x
    rw [hx] at h
    refine Eq.trans ?_ h.symm
    exact Fintype.prod_equiv (subgroupEquivAlgEquiv S).toEquiv _ _ (fun s => rfl)
  have h1 : ∀ (S : Subgroup (L ≃ₐ[K] L)) [Fintype S],
      IsZero (tateCohomology (Rep.res S.subtype A) (0 + 1)) := by
    intro S _
    have hz : ∀ z : groupCohomology (Rep.res S.subtype A) 1, z = 0 := fun z =>
      H1_induction_on z fun f => by
        rw [H1π_eq_zero_iff]
        have hf := (mem_cocycles₁_iff (A := Rep.res S.subtype A) f).1 f.2
        let e := subgroupEquivAlgEquiv S
        let g : Gal(L/fixedField S) → Lˣ := fun σ => Additive.toMul (f (e.symm σ))
        have hg : IsMulCocycle₁ g := by
          intro σ τ
          obtain ⟨s, rfl⟩ := e.surjective σ
          obtain ⟨t, rfl⟩ := e.surjective τ
          have h := congrArg (Additive.toMul (α := Lˣ)) (hf s t)
          simp only [g, ← map_mul, MulEquiv.symm_apply_apply]
          exact h
        obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units g hg
        refine ⟨Additive.ofMul β, funext fun s => ?_⟩
        have h := congrArg (Additive.ofMul (α := Lˣ)) (hβ (e s))
        rw [show g (e s) = Additive.toMul (f s) by simp only [g, MulEquiv.symm_apply_apply]; rfl] at h
        exact h
    have hs : Subsingleton (groupCohomology (Rep.res S.subtype A) 1) :=
      ⟨fun a b => by rw [hz a, hz b]⟩
    have e : (0 + 1 : ℤ) = ((1 : ℕ) : ℤ) := by norm_num
    rw [e]
    exact (ModuleCat.isZero_of_subsingleton (groupCohomology (Rep.res S.subtype A) 1)).of_iso ((TateCohomology.isoGroupCohomology 1).app _)
  have hCT : CohTrivial A := cohTrivial_of_forall_subgroup A 0 fun S _ => ⟨h0 S, h1 S⟩
  have h2 : IsZero (tateCohomology A ((2 : ℕ) : ℤ)) :=
    isZero_tateCohomology_of_index A _ fun p hp _ =>
      ⟨⊤, by simpa [Subgroup.index_top] using hp.one_lt.ne', fun {_} => hCT ⊤ _⟩
  have h2' : IsZero (groupCohomology A 2) :=
    h2.of_iso ((TateCohomology.isoGroupCohomology 2).app A).symm
  exact (ModuleCat.isZero_iff_subsingleton).1 h2'

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CdpGaloisLeOneOfAlgebraicRatFunc

section

@[expose] public section

set_option maxSynthPendingDepth 1

open CategoryTheory IntermediateField GroundTheory.ProfCoh

namespace GlobalTheory.TsenCD

theorem subsingleton_brauer (k E Ω : Type) [Field k] [IsAlgClosed k] [Field E] [Algebra (RatFunc k) E]
    [Algebra.IsAlgebraic (RatFunc k) E] [Field Ω] [Algebra E Ω] [IsGalois E Ω] :
    Subsingleton (cohomology (galUnits.{0} E Ω) 2) := by
  suffices h : ∀ x : cohomology (galUnits.{0} E Ω) 2, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨F, z, rfl⟩ := exists_unitsInflation_eq 2 x
  have hC := GlobalTheory.tsen_algebraic_extension_ratFunc k E
  have h1 : Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits E F.toIntermediateField) 2) :=
    GlobalTheory.c_one_h2_units_subsingleton E F.toIntermediateField hC
  have h2 : Subsingleton (groupCohomology (galUnitsZ E F.toIntermediateField) 2) := h1
  have h3 : Subsingleton (groupCohomology (galUnits.{0} E F.toIntermediateField) 2) :=
    (h2GalUnitsAddEquiv E F.toIntermediateField).injective.subsingleton
  rw [Subsingleton.elim z 0, map_zero]

theorem cdp_le_one_of_ne_char (k K Ω : Type) [Field k] [IsAlgClosed k] [Field K]
    [Algebra (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (p : ℕ) (hp : p.Prime) (hpK : (p : K) ≠ 0) :
    cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity K Ω hp hpK
  have h := cdp_le_of_forall_openSubgroup hp (galRootsOfUnity.{0} K Ω p) e 1 (fun U => by
    let E := fixedField (U : Subgroup (Ω ≃ₐ[K] Ω))
    letI : Algebra (RatFunc k) E := ((algebraMap K E).comp (algebraMap (RatFunc k) K)).toAlgebra
    haveI : IsScalarTower (RatFunc k) K E := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.IsAlgebraic K E := inferInstance
    haveI : Algebra.IsAlgebraic (RatFunc k) E := Algebra.IsAlgebraic.trans (RatFunc k) K E
    haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    have hB : Subsingleton (cohomology (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype
        (galUnits.{0} K Ω)) 2) := by
      have := subsingleton_brauer k E Ω
      exact (openCohomologyIso U 2).toLinearEquiv.toEquiv.subsingleton
    have h1 : Subsingleton (cohomology (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype
        (galUnits.{0} K Ω)) 1) := ModuleCat.subsingleton_of_isZero (isZero_H1_open K Ω U)
    have hS := kummerSequenceRes_shortExact (Ksep := Ω) p (U : Subgroup (Ω ≃ₐ[K] Ω)) hpK
    haveI : Subsingleton (cohomology (kummerSequenceRes (K := K) (Ksep := Ω) p
        (U : Subgroup (Ω ≃ₐ[K] Ω))).X₂ (1 + 1)) := hB
    exact (cohomologyMap_f_injective_of_subsingleton hS 1 h1).subsingleton)
  exact_mod_cast h

section ArtinSchreier

attribute [local instance 2000] Rep.hV2

open Polynomial

theorem exists_zmod_cast_eq_of_pow_sub_self {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [CharP Ω p]
    (y : Ω) (hy : y ^ p - y = 0) : ∃ a : ZMod p, ZMod.castHom (dvd_refl p) Ω a = y := by
  classical
  by_contra hne
  push_neg at hne
  set f := ZMod.castHom (dvd_refl p) Ω
  set P : Polynomial Ω := X ^ p - X
  have hP : P ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hp.out.one_lt
  have hroot : ∀ z : Ω, z ^ p - z = 0 → z ∈ P.roots.toFinset := fun z hz => by
    rw [Multiset.mem_toFinset, mem_roots hP]
    simp [P, hz]
  have hT : insert y (Finset.univ.image f) ⊆ P.roots.toFinset := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hroot _ hy
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hz
      apply hroot
      rw [← map_pow, ZMod.pow_card, sub_self]
  have hy' : y ∉ Finset.univ.image f := fun h => by
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
    exact hne a ha
  have hcard : (insert y (Finset.univ.image f)).card = p + 1 := by
    rw [Finset.card_insert_of_notMem hy', Finset.card_image_of_injective _ f.injective,
      Finset.card_univ, ZMod.card]
  have h1 := Finset.card_le_card hT
  have h2 : P.roots.toFinset.card ≤ p :=
    (Multiset.toFinset_card_le _).trans ((card_roots' P).trans
      (Polynomial.natDegree_X_pow_sub_X (R := Ω) hp.out.one_lt).le)
  omega

theorem exists_pow_sub_self_eq {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [CharP Ω p]
    [IsSepClosed Ω] (a : Ω) : ∃ x : Ω, x ^ p - x = a := by
  have hd : derivative (X ^ p - X - C a : Polynomial Ω) = -1 := by
    simp [derivative_X_pow, CharP.cast_eq_zero]
  have hsep : (X ^ p - X - C a : Polynomial Ω).Separable := by
    rw [separable_def, hd]
    exact isCoprime_one_right.neg_right
  have hdeg : (X ^ p - X - C a : Polynomial Ω).degree ≠ 0 := fun h => by
    have h' := congrArg derivative (eq_C_of_degree_eq_zero h)
    rw [hd, derivative_C] at h'
    exact one_ne_zero (neg_eq_zero.1 h')
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root _ hdeg hsep
  refine ⟨x, ?_⟩
  have := hx.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at this
  exact sub_eq_zero.1 this

end ArtinSchreier

section Sequence

attribute [local instance 2000] Rep.hV2

variable (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] [IsGalois E Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p]

noncomputable def primeFieldToGalAdd :
    Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p)) ⟶ galAddInt.{0} E Ω :=
  Rep.ofHom ⟨uliftIntLinearMap ((ZMod.castHom (dvd_refl p) Ω).toAddMonoidHom.comp
      (AddEquiv.ulift : ULift.{0} (ZMod p) ≃+ ZMod p).toAddMonoidHom), fun σ =>
    LinearMap.ext fun x => by
      change ZMod.castHom (dvd_refl p) Ω x.down = σ (ZMod.castHom (dvd_refl p) Ω x.down)
      exact (congrArg (fun φ : ZMod p →+* Ω => φ x.down)
        (RingHom.ext_zmod ((σ : Ω →+* Ω).comp (ZMod.castHom (dvd_refl p) Ω))
          (ZMod.castHom (dvd_refl p) Ω))).symm⟩

noncomputable def artinSchreierMap : galAddInt.{0} E Ω ⟶ galAddInt.{0} E Ω :=
  Rep.ofHom ⟨uliftIntLinearMap ((frobenius Ω p).toAddMonoidHom - AddMonoidHom.id Ω), fun σ =>
    LinearMap.ext fun x => by
      change σ x ^ p - σ x = σ (x ^ p - x)
      rw [map_sub, map_pow]⟩

noncomputable def artinSchreierSequence : ShortComplex (Rep (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω)) :=
  ShortComplex.mk (primeFieldToGalAdd E Ω p) (artinSchreierMap E Ω p) (by
    ext x
    change (ZMod.castHom (dvd_refl p) Ω x.down) ^ p - ZMod.castHom (dvd_refl p) Ω x.down = 0
    rw [← map_pow, ZMod.pow_card, sub_self])

theorem artinSchreierSequence_shortExact [IsSepClosed Ω] :
    (artinSchreierSequence E Ω p).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine shortComplex_exact_of_forall_exists _ fun y hy => ?_
    obtain ⟨a, ha⟩ := exists_zmod_cast_eq_of_pow_sub_self (p := p) (Ω := Ω) y hy
    exact ⟨ULift.up a, ha⟩
  · exact (Rep.mono_iff_injective _).2 fun x y h =>
      ULift.ext ((ZMod.castHom (dvd_refl p) Ω).injective h)
  · refine (Rep.epi_iff_surjective _).2 fun a => ?_
    obtain ⟨x, hx⟩ := exists_pow_sub_self_eq (p := p) (Ω := Ω) a
    exact ⟨x, hx⟩

instance isDiscreteRep_artinSchreierSequence_X₁ :
    IsDiscreteRep (artinSchreierSequence E Ω p).X₁ :=
  inferInstanceAs (IsDiscreteRep (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p))))

instance isDiscreteRep_artinSchreierSequence_X₂ :
    IsDiscreteRep (artinSchreierSequence E Ω p).X₂ :=
  inferInstanceAs (IsDiscreteRep (galAddInt.{0} E Ω))

instance isDiscreteRep_artinSchreierSequence_X₃ :
    IsDiscreteRep (artinSchreierSequence E Ω p).X₃ :=
  inferInstanceAs (IsDiscreteRep (galAddInt.{0} E Ω))


omit [Fact p.Prime] [CharP Ω p] in
theorem subsingleton_cohomology_galAddInt {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (cohomology (galAddInt.{0} E Ω) n) := by
  have := subsingleton_cohomology_galAdd (K := E) (L := Ω) hn
  exact (cohomologyAddEquivOfEquiv (A := galAddInt.{0} E Ω) (A' := galAdd E Ω) (AddEquiv.refl Ω)
    (fun _ _ => rfl) n).injective.subsingleton

theorem subsingleton_cohomology_two_trivial_zmod [IsSepClosed Ω] :
    Subsingleton (cohomology (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p))) 2) := by
  have hS := artinSchreierSequence_shortExact E Ω p
  have h1 : Subsingleton (cohomology (artinSchreierSequence E Ω p).X₃ 1) :=
    subsingleton_cohomology_galAddInt E Ω one_ne_zero
  haveI : Subsingleton (cohomology (artinSchreierSequence E Ω p).X₂ (1 + 1)) :=
    subsingleton_cohomology_galAddInt E Ω (n := 2) two_ne_zero
  exact (cohomologyMap_f_injective_of_subsingleton hS 1 h1).subsingleton

end Sequence

theorem cdp_le_one_of_char_eq (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (p : ℕ) (hp : p.Prime) (hpK : (p : K) = 0) : cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp).2 hpK
  haveI : CharP Ω p := charP_of_injective_algebraMap (algebraMap K Ω).injective p
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  have h := cdp_le_of_forall_openSubgroup hp
    (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[K] Ω) (ULift.{0} (ZMod p))) AddEquiv.ulift.symm 1 (fun U => by
      let E := fixedField (U : Subgroup (Ω ≃ₐ[K] Ω))
      haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
      have h2 := subsingleton_cohomology_two_trivial_zmod E Ω p
      haveI : IsDiscreteRep (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype
          (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[K] Ω) (ULift.{0} (ZMod p)))) :=
        isDiscreteRep_res_subtype _ _
      let f : Rep.res (galFixedFieldEquivOpen U).toMonoidHom
          (Rep.res (U : Subgroup (Ω ≃ₐ[K] Ω)).subtype
            (Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[K] Ω) (ULift.{0} (ZMod p)))) ⟶
          Rep.trivial (ULift.{0} ℤ) (Ω ≃ₐ[E] Ω) (ULift.{0} (ZMod p)) :=
        Rep.ofHom ⟨LinearMap.id, fun σ => LinearMap.ext fun x => rfl⟩
      haveI := isIso_cohomologyMapAlong_of_mulEquiv (galFixedFieldEquivOpen U)
        (continuous_galFixedFieldEquivOpen U) (continuous_galFixedFieldEquivOpen_symm U) f
        Function.bijective_id 2
      exact (asIso (cohomologyMapAlong (galFixedFieldEquivOpen U).toMonoidHom
        (continuous_galFixedFieldEquivOpen U) f 2)).toLinearEquiv.toEquiv.subsingleton)
  exact_mod_cast h

theorem cdp_galois_le_one_of_algebraic_ratFunc : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [Field K]
    [Algebra (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (p : ℕ), p.Prime → GroundTheory.ProfCoh.cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  intro k K Ω _ _ _ _ _ _ _ _ p hp
  by_cases hpK : (p : K) = 0
  · exact cdp_le_one_of_char_eq K Ω p hp hpK
  · exact cdp_le_one_of_ne_char k K Ω p hp hpK

end GlobalTheory.TsenCD
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CdpGaloisLeOneOfAlgebraicRatFuncStatement

section

@[expose] public section

open GroundTheory.ProfCoh

theorem _root_.GlobalTheory.T.cdp_galois_le_one_of_isAlgebraic_ratFunc : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (p : ℕ), p.Prime → GroundTheory.ProfCoh.cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  first | (exact @GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc) | (exact GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc) | (intros; apply GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc  <;> assumption)
end
end
