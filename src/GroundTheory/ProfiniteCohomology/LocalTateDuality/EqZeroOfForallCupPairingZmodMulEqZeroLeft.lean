module

public import GroundTheory.ProfiniteCohomology.LocalTateDuality.KummerCup
import GroundTheory.LocalFields.LocalAxiomDictionary
import GroundTheory.LocalFields.UnitsPowers
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import Mathlib.FieldTheory.KrullTopology
public import GroundTheory.LocalFields.LocalReciprocityUniversal
public import GroundTheory.LocalFields.NormCorrespondence
public import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
import Mathlib.Algebra.Lie.OfAssociative
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

-- Source module: GroundTheory.ProfiniteCohomology.LocalTateDuality.NormCharacters

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IntermediateField GroundTheory.LocalField

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {Ω : Type*} [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsSepClosure F Ω] in
theorem exists_norm_iff_mem_range_normUnits (E : IntermediateField F Ω) [FiniteDimensional F E]
    (a : Fˣ) : (∃ y : E, Algebra.norm F y = (a : F)) ↔ a ∈ (normUnits F E).range := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hy
      exact a.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext (by simp [hy])⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, rfl⟩


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsSepClosure F Ω] in
theorem exists_norm_of_eq {E₁ E₂ : IntermediateField F Ω} (h : E₁ = E₂) {a : F}
    (hy : ∃ y : E₁, Algebra.norm F y = a) : ∃ y : E₂, Algebra.norm F y = a := by
  subst h
  exact hy

theorem eq_top_of_forall_exists_norm (H : Subgroup Gal(Ω/F)) [H.Normal]
    (hH : IsOpen (H : Set Gal(Ω/F))) (hcomm : ∀ σ τ : Gal(Ω/F), σ * τ * σ⁻¹ * τ⁻¹ ∈ H)
    (h : ∀ a : Fˣ, ∃ y : fixedField H, Algebra.norm F y = (a : F)) : H = ⊤ := by
  set E := fixedField H with hE
  have hfix : E.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
  have hfin : FiniteDimensional F E :=
    (InfiniteGalois.isOpen_iff_finite E).1 (by rw [hfix]; exact hH)
  have hgal : IsGalois F E :=
    (InfiniteGalois.normal_iff_isGalois E).1 (by rw [hfix]; infer_instance)
  have hc : ∀ σ' τ' : Gal(E/F), σ' * τ' = τ' * σ' := by
    intro σ' τ'
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := Ω) σ'
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := Ω) τ'
    have hk : σ * τ * σ⁻¹ * τ⁻¹ ∈ (AlgEquiv.restrictNormalHom E).ker := by
      rw [E.restrictNormalHom_ker, hfix]
      exact hcomm σ τ
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hk
    have key : ∀ {M : Type _} [Group M] (x y : M), x * y * x⁻¹ * y⁻¹ = 1 → x * y = y * x := by
      intro M _ x y hxy
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [hxy, one_mul]
    exact key _ _ hk
  have : IsAbelianGalois F E := { toIsGalois := hgal, toIsMulCommutative := ⟨⟨hc⟩⟩ }
  have hidx := index_range_normUnits_of_isAbelianGalois (Ω := Ω) E
  have htop : (normUnits F E).range = ⊤ :=
    eq_top_iff.2 fun a _ => (exists_norm_iff_mem_range_normUnits E a).1 (h a)
  rw [htop, Subgroup.index_top] at hidx
  have hbot : E = ⊥ := IntermediateField.finrank_eq_one_iff.1 hidx.symm
  rw [← hfix, hbot, IntermediateField.fixingSubgroup_bot]

theorem exists_zmod_char_not_norm {n : ℕ} (hn : (n : F) ≠ 0) (a : Fˣ) (ha : ∀ b : Fˣ, b ^ n ≠ a) :
    ∃ ψ : Gal(Ω/F) →* Multiplicative (ZMod n), IsOpen (ψ.ker : Set Gal(Ω/F)) ∧
      ¬ ∃ y : fixedField ψ.ker, Algebra.norm F y = (a : F) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  have : NeZero n := ⟨hn0⟩
  set P := (powMonoidHom n : Fˣ →* Fˣ).range with hP
  have hPopen : IsOpen (P : Set Fˣ) := isOpen_range_pow hn
  have hPfin : Finite (Fˣ ⧸ P) := finite_quotient_range_pow hn
  have : P.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hkill : ∀ q : Additive (Fˣ ⧸ P), n • q = 0 := by
    intro q
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    have hq : q = Additive.ofMul (x : Fˣ ⧸ P) := by rw [hx]; rfl
    rw [hq, ← ofMul_pow, ← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff (x ^ n)).2 (MonoidHom.mem_range.2 ⟨x, rfl⟩),
      ofMul_one]
  have hane : Additive.ofMul (a : Fˣ ⧸ P) ≠ 0 := by
    intro h0
    have h1 : (a : Fˣ ⧸ P) = 1 := congrArg Additive.toMul h0
    obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff _).1 h1
    exact ha b hb
  obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero (A := Additive (Fˣ ⧸ P)) hkill hane
  let φ : Fˣ →* Multiplicative (ZMod n) :=
    (AddMonoidHom.toMultiplicativeRight χ).comp (QuotientGroup.mk' P)
  have hφ : ∀ x : Fˣ, φ x = Multiplicative.ofAdd (χ (Additive.ofMul (x : Fˣ ⧸ P))) := fun _ => rfl
  have hPle : P ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hφ, (QuotientGroup.eq_one_iff _).2 hx, ofMul_one, map_zero, ofAdd_zero]
  have hH'open : IsOpen (φ.ker : Set Fˣ) := Subgroup.isOpen_mono hPle hPopen
  have : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hPle
  have haH' : a ∉ φ.ker := by
    rw [MonoidHom.mem_ker, hφ]
    intro h1
    exact hχ (Multiplicative.ofAdd.injective h1)
  obtain ⟨E, hEfin, hEab, hEH⟩ := exists_isAbelianGalois_range_normUnits_eq (Ω := Ω) φ.ker hH'open
  have := hEfin
  have := hEab
  let φbar : Fˣ ⧸ (normUnits F E).range →* Multiplicative (ZMod n) :=
    QuotientGroup.lift _ φ (le_of_eq hEH)
  have hφbar : Function.Injective φbar := by
    refine (injective_iff_map_eq_one φbar).2 fun q hq => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hx : x ∈ φ.ker := hq
      rw [← hEH] at hx
      exact (QuotientGroup.eq_one_iff _).2 hx
  let ψ : Gal(Ω/F) →* Multiplicative (ZMod n) :=
    (φbar.comp (localReciprocityAbelian E).toMonoidHom).comp (AlgEquiv.restrictNormalHom E)
  have hker : ψ.ker = E.fixingSubgroup := by
    rw [← E.restrictNormalHom_ker]
    ext σ
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : (localReciprocityAbelian E) (AlgEquiv.restrictNormalHom E σ) = 1 :=
        hφbar (h1.trans (map_one φbar).symm)
      exact (MulEquiv.map_eq_one_iff _).1 h2
    · intro h1
      change φbar ((localReciprocityAbelian E) (AlgEquiv.restrictNormalHom E σ)) = 1
      rw [h1, map_one, map_one]
  refine ⟨ψ, ?_, ?_⟩
  · rw [hker]
    exact IntermediateField.fixingSubgroup_isOpen E
  · have hfE : fixedField ψ.ker = E := by
      rw [hker]
      exact InfiniteGalois.fixedField_fixingSubgroup E
    intro hy
    have := (exists_norm_iff_mem_range_normUnits E a).1 (exists_norm_of_eq hfE hy)
    rw [hEH] at this
    exact haH' this

end GroundTheory.ProfCoh
end
end
end

-- Source module: GroundTheory.ProfiniteCohomology.LocalTateDuality.EqZeroOfForallCupPairingZmodMulEqZeroLeft

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField

attribute [local instance 2000] Rep.hV2

attribute [local irreducible] localClassFormationOfIsSepClosure

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
theorem unitsInvariantOpen_mul (W : Subgroup Gal(Ksep/K)) (a b : (fixedField W)ˣ) :
    unitsInvariantOpen W (a * b) = unitsInvariantOpen W a + unitsInvariantOpen W b := by
  apply Subtype.ext
  change Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) (a * b)) =
    Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) a) +
      Additive.ofMul (Units.map (algebraMap (fixedField W) Ksep : fixedField W →* Ksep) b)
  rw [map_mul, ofMul_mul]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
theorem natCast_fixedField_ne_zero (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K)) :
    (n : fixedField W) ≠ 0 := by
  rw [← map_natCast (algebraMap K (fixedField W))]
  exact (map_ne_zero_iff _ (algebraMap K (fixedField W)).injective).2 hn

theorem finite_cohomology_one_res_galRootsOfUnity (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    Finite (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1) := by
  let := GroundTheory.LocalField.algebraicValuativeRel K Ksep
  let := GroundTheory.LocalField.algebraicTopology K Ksep
  have := GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep
  have := GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep
  have hfinE : Finite ((fixedField (U : Subgroup Gal(Ksep/K)))ˣ ⧸
      (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* _).range) :=
    GroundTheory.LocalField.finite_quotient_range_pow (natCast_fixedField_ne_zero hn _)
  let κ : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →*
      Multiplicative (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep n)) 1) :=
    { toFun := fun a => Multiplicative.ofAdd ((δ (kummerSeqOpen_shortExact hn (U : Subgroup Gal(Ksep/K)))
        0 1 rfl).hom ((H0Iso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) a)))
      map_one' := by
        have h := unitsInvariantOpen_pow (U : Subgroup Gal(Ksep/K)) 1 0
        rw [pow_zero, zero_smul] at h
        rw [h, map_zero, map_zero, ofAdd_zero]
      map_mul' := fun a b => by
        rw [unitsInvariantOpen_mul, map_add (f := _), map_add (f := _), ofAdd_add] }
  have hle : (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* _).range ≤ κ.ker := by
    rintro _ ⟨b, rfl⟩
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd ((δ (kummerSeqOpen_shortExact hn (U : Subgroup Gal(Ksep/K))) 0 1 rfl).hom
      ((H0Iso _).inv.hom (unitsInvariantOpen (U : Subgroup Gal(Ksep/K)) (b ^ n)))) = 1
    rw [δ_unitsInvariantOpen_pow_eq_zero hn, ofAdd_zero]
  refine Finite.of_surjective (fun q => Multiplicative.toAdd (QuotientGroup.lift _ κ hle q)) fun y => ?_
  obtain ⟨a, rfl⟩ := exists_δ_unitsInvariantOpen_eq hn U y
  exact ⟨(a : _ ⧸ (powMonoidHom n : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ →* _).range), rfl⟩

theorem eq_zero_of_forall_cupPairing_zmodMul_eq_zero_left (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K)) (x : cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1)
    (h : ∀ y : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1,
      cupPairing (zmodMulPairing n (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
        (nsmul_res_galRootsOfUnity_eq_zero hn _)) (show 1 + 1 = 2 from rfl) x y = 0) :
    x = 0 := by
  let := GroundTheory.LocalField.algebraicValuativeRel K Ksep
  let := GroundTheory.LocalField.algebraicTopology K Ksep
  have := GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep
  have := GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 x
  have hnorm := fun a => (cupPairing_δ_unitsInvariantOpen_eq_zero_iff hn U z a).1 (h _)
  have hopen : IsOpen (charKer (charAdd (openChar n U z)) : Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) := by
    have e : (charKer (charAdd (openChar n U z)) : Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) =
        (fun g => openChar n U z (Additive.ofMul g)) ⁻¹' {0} := by
      ext g
      exact mem_charKer
    rw [e]
    exact (isOpen_discrete _).preimage ((openChar n U z).continuous_toFun.comp continuous_ofMul)
  have hcomm : ∀ σ τ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))),
      σ * τ * σ⁻¹ * τ⁻¹ ∈ charKer (charAdd (openChar n U z)) := fun σ τ => by
    rw [mem_charKer, ofMul_mul, ofMul_mul, ofMul_mul, ofMul_inv, ofMul_inv, map_add (f := _), map_add (f := _), map_add (f := _),
      map_neg, map_neg]
    abel
  have htop := eq_top_of_forall_exists_norm _ hopen hcomm hnorm
  rw [cohomologyπ_one_eq_zero_iff_of_trivial _ (fun _ _ => rfl)]
  exact fun g => ULift.ext (zmodCocycleHom_eq_zero_of_charKer_eq_top hn U z htop g)

theorem eq_zero_of_forall_cupPairing_zmodMul_eq_zero_right (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K))
    (y : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1)
    (h : ∀ x : cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1,
      cupPairing (zmodMulPairing n (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
        (nsmul_res_galRootsOfUnity_eq_zero hn _)) (show 1 + 1 = 2 from rfl) x y = 0) :
    y = 0 := by
  let := GroundTheory.LocalField.algebraicValuativeRel K Ksep
  let := GroundTheory.LocalField.algebraicTopology K Ksep
  have := GroundTheory.LocalField.algebraicTopology_isValuativeTopology K Ksep
  have := GroundTheory.LocalField.algebraicValuativeRel_valuativeExtension K Ksep
  obtain ⟨a, rfl⟩ := exists_δ_unitsInvariantOpen_eq hn U y
  by_cases ha : ∃ b : (fixedField (U : Subgroup Gal(Ksep/K)))ˣ, b ^ n = a
  · obtain ⟨b, rfl⟩ := ha
    exact δ_unitsInvariantOpen_pow_eq_zero hn _ b
  · simp only [not_exists] at ha
    obtain ⟨ψ, hψo, hψ⟩ := exists_zmod_char_not_norm (Ω := Ksep) (natCast_fixedField_ne_zero hn _) a ha
    obtain ⟨z, hz⟩ := exists_cocycle_charKer_eq hn U ψ hψo
    exact (hψ (exists_norm_of_eq (congrArg fixedField hz)
      ((cupPairing_δ_unitsInvariantOpen_eq_zero_iff hn U z a).1 (h _)))).elim

theorem isPerfectPairing_localInvRootsOfUnity (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    IsPerfectPairing
      (bilinAddHom (cupPairing (zmodMulPairing n
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
        (nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_galRootsOfUnity hn)))
        (show 1 + 1 = 2 from rfl)))
      (localInvRootsOfUnity hn U).toAddMonoidHom := by
  have : NeZero n := ⟨ne_zero_of_natCast_ne_zero' hn⟩
  set β := bilinAddHom (cupPairing (zmodMulPairing n
    (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n))
    (nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_galRootsOfUnity hn)))
    (show 1 + 1 = 2 from rfl)) with hβ
  set t := (localInvRootsOfUnity hn U).toAddMonoidHom with ht
  have ht0 : ∀ c, t c = 0 → c = 0 := fun c hc =>
    (localInvRootsOfUnity hn U).injective (hc.trans (map_zero _).symm)
  have h1 : Function.Injective ((AddMonoidHom.compHom t).comp β) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    refine eq_zero_of_forall_cupPairing_zmodMul_eq_zero_left hn U x fun y => ht0 _ ?_
    exact DFunLike.congr_fun hx y
  have h2 : Function.Injective ((AddMonoidHom.compHom t).comp β.flip) := by
    refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    refine eq_zero_of_forall_cupPairing_zmodMul_eq_zero_right hn U y fun x => ht0 _ ?_
    exact DFunLike.congr_fun hy x
  have hYfin := finite_cohomology_one_res_galRootsOfUnity hn U
  have hXfin : Finite (cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1) :=
    Finite.of_injective _ h1
  have c1 := Nat.card_le_card_of_injective _ h1
  have c2 := Nat.card_le_card_of_injective _ h2
  have c3 := card_addMonoidHom_zmod_le (n := n)
    (A := cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep n)) 1)
  have c4 := card_addMonoidHom_zmod_le (n := n)
    (A := cohomology (zmodRep.{0} (U : Subgroup Gal(Ksep/K)) n) 1)
  exact ⟨h1.bijective_of_nat_card_le (by omega), h2.bijective_of_nat_card_le (by omega)⟩

end GroundTheory.ProfCoh
end
end
end
