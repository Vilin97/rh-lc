module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardFilterLeLogClassNumber
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscFieldEqTorsionField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdDiscrTorsionField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionParamLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayFieldInRestrictScalars
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMemDifferentIdeal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRoot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeDvdOfMemDifferent

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.Mem.FieldsEx
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KPsiRam

theorem prime_dvd_of_mem_different (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (N : ℕ) (hmem : (N : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L)) {p : ℕ} (hp : p.Prime) (h : p ∣ (discr L).natAbs) :
    p ∣ N ∨ p ∣ (discr K).natAbs := by
  have h1 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have h2 : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ∣ Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  rw [Ideal.absNorm_span_natCast] at h2
  rw [h1] at h
  exact ((Nat.Prime.dvd_mul hp).1 h).imp (fun h => hp.dvd_of_dvd_pow (h.trans h2)) hp.dvd_of_dvd_pow

theorem sup_adjoin_root (F : IntermediateField ℚ ℂ) [NumberField F] {k : ℕ} (hk : 0 < k) {y : F}
    (hy : y ∈ powIdealElts F k) {z : ℂ} (hz : z ^ k = (y : ℂ)) :
    ∃ _ : NumberField ↥(F ⊔ ℚ⟮z⟯), ∀ p : ℕ, p.Prime → p ∣ (discr ↥(F ⊔ ℚ⟮z⟯)).natAbs →
      p ∣ k ∨ p ∣ (discr F).natAbs := by
  obtain ⟨hy, I, hI⟩ := hy
  have hI' : (I : Submodule (𝓞 F) F) ^ k = Submodule.span (𝓞 F) {y} := by
    rw [← FractionalIdeal.coe_pow, ← hI, FractionalIdeal.coe_spanSingleton]
  set L : IntermediateField ℚ ℂ := F ⊔ ℚ⟮z⟯ with hLdef
  have hzL : z ∈ L := (le_sup_right : ℚ⟮z⟯ ≤ L) (IntermediateField.mem_adjoin_simple_self ℚ z)
  have hzF : IsIntegral F z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_algebraMap (x := y))
  have hzQ : IsIntegral ℚ z := isIntegral_trans z hzF
  haveI : FiniteDimensional ℚ ℚ⟮z⟯ := IntermediateField.adjoin.finiteDimensional hzQ
  have hLfin : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_sup F ℚ⟮z⟯
  letI : NumberField L := NumberField.mk
  letI : Algebra F L := (IntermediateField.inclusion (le_sup_left : F ≤ L)).toRingHom.toAlgebra
  haveI : IsScalarTower F L ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hz' : (⟨z, hzL⟩ : L) ^ k = algebraMap F L y := Subtype.ext hz
  have hzi : IsIntegral F (⟨z, hzL⟩ : L) := Algebra.IsIntegral.isIntegral _
  have htop : F⟮(⟨z, hzL⟩ : L)⟯ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨w, hw⟩ -
    let M : IntermediateField ℚ ℂ :=
      ((F⟮(⟨z, hzL⟩ : L)⟯).map (IsScalarTower.toAlgHom F L ℂ)).restrictScalars ℚ
    have hM : L ≤ M := by
      refine sup_le (fun v hv => ?_) (IntermediateField.adjoin_simple_le_iff.mpr ?_)
      · exact ((F⟮(⟨z, hzL⟩ : L)⟯).map (IsScalarTower.toAlgHom F L ℂ)).algebraMap_mem ⟨v, hv⟩
      · exact ⟨_, IntermediateField.mem_adjoin_simple_self F _, rfl⟩
    obtain ⟨w', hw', hww⟩ := hM hw
    have : w' = ⟨w, hw⟩ := Subtype.ext hww
    rwa [this] at hw'
  have htop' : Algebra.adjoin F {(⟨z, hzL⟩ : L)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hzi.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]
  have hD := GlobalTheory.FieldSize.natCast_mem_differentIdeal_of_root k hk y hy _ hI' _ hz' htop'
  exact ⟨inferInstance, fun p hp h => prime_dvd_of_mem_different F L k hD hp h⟩

theorem sup_adjoin_roots {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) {h : ℕ} (hh : 0 < h) (S : Set ℂ)
    (hS : S.Finite) (hS' : ∀ z ∈ S, ∃ y ∈ powIdealElts E h, z ^ h = φ y) :
    ∃ _ : NumberField ↥(imField φ ⊔ IntermediateField.adjoin ℚ S), ∀ p : ℕ, p.Prime →
      p ∣ (discr ↥(imField φ ⊔ IntermediateField.adjoin ℚ S)).natAbs → p ∣ h ∨ p ∣ (discr E).natAbs := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    rw [IntermediateField.adjoin_empty, sup_bot_eq]
    let e₀ : E ≃ₐ[ℚ] imField φ := AlgEquiv.ofInjectiveField φ.toRatAlgHom
    have : FiniteDimensional ℚ (imField φ) := e₀.toLinearEquiv.finiteDimensional
    have hN : NumberField (imField φ) := NumberField.of_module_finite ℚ _
    exact ⟨hN, fun p _ hp => Or.inr (by rwa [discr_eq_discr_of_algEquiv _ e₀])⟩
  | @insert z S _ _ ih =>
    obtain ⟨_, ih⟩ := ih fun w hw => hS' w (Set.mem_insert_of_mem _ hw)
    obtain ⟨y, hy, hz⟩ := hS' z (Set.mem_insert _ _)
    have hE : ∀ x, φ x ∈ imField φ ⊔ IntermediateField.adjoin ℚ S := (imField_le_iff φ).1 le_sup_left
    obtain ⟨hN, H⟩ := sup_adjoin_root _ hh (map_mem_pow (φ.codRestrict _ hE) hy) hz
    rw [Set.insert_eq, Set.union_comm, IntermediateField.adjoin_union, ← sup_assoc]
    exact ⟨hN, fun p hp hd => (H p hp hd).elim Or.inl (ih p hp)⟩

theorem typeNorm_mem {R : Ranks} (H : Host R) (p q : ℕ) {h : ℕ} {γ : H.E} (hγ : γ ∈ powIdealElts H.E h) :
    typeNorm H p q γ ∈ powIdealElts H.E h := by
  have hσ : ∀ (σ : H.E ≃ₐ[ℚ] H.E) {x}, x ∈ powIdealElts H.E h → σ x ∈ powIdealElts H.E h :=
    fun σ _ hx => map_mem_pow (σ : H.E →+* H.E) hx
  exact prod_mem_pow _ _ fun g _ => mul_mem_pow (npow_mem_pow (hσ _ hγ) _) (npow_mem_pow (hσ _ (hσ _ hγ)) _)

theorem prime_dvd_discr_iSup_kPsi : ∀ (P : Pre) (δ : FieldDat P),
    ∃ _ : NumberField ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j), ∀ p : ℕ, p.Prime →
      p ∣ (discr ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j)).natAbs → p ∣ classNumber P.host.E * (discr P.host.E).natAbs := by
  intro P δ
  let S : Set ℂ := {rootOne (classNumber P.host.E)} ∪ ⋃ j ∈ Set.Icc 1 P.R.m, ⋃ i,
    {z | z ^ δ.basis.h i = P.host.φ₀ (typeNorm P.host (P.R.sigW j).1 (P.R.sigW j).2 (δ.basis.γ i : P.host.E))}
  have hS : S.Finite := by
    refine (Set.finite_singleton _).union ((Set.finite_Icc _ _).biUnion fun j _ => Set.finite_iUnion fun i => ?_)
    refine Set.Finite.subset (Polynomial.nthRoots (δ.basis.h i) (P.host.φ₀
      (typeNorm P.host (P.R.sigW j).1 (P.R.sigW j).2 (δ.basis.γ i : P.host.E)))).toFinset.finite_toSet fun z hz => ?_
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (δ.basis.h_pos i)]
    exact hz
  have hS' : ∀ z ∈ S, ∃ y ∈ powIdealElts P.host.E (classNumber P.host.E), z ^ classNumber P.host.E = P.host.φ₀ y := by
    rintro z (rfl | hz)
    · exact ⟨1, one_mem_pow, by
        rw [map_one]; exact (Complex.isPrimitiveRoot_exp _ (classNumber_ne_zero _)).pow_eq_one⟩
    · simp only [Set.mem_iUnion] at hz
      obtain ⟨j, -, i, hz⟩ := hz
      have hγ : (δ.basis.γ i : P.host.E) ∈ powIdealElts P.host.E (δ.basis.h i) :=
        ⟨(δ.basis.γ i).ne_zero, δ.basis.c i, by
          rw [← coe_toPrincipalIdeal, ← δ.basis.pow_eq i, Units.val_pow_eq_pow_val]; rfl⟩
      obtain ⟨k, hk⟩ : δ.basis.h i ∣ classNumber P.host.E := orderOf_dvd_card
      refine ⟨_, hk ▸ pow_mem_powIdealElts (typeNorm_mem P.host (P.R.sigW j).1 (P.R.sigW j).2 hγ) k, ?_⟩
      rw [hk, pow_mul, map_pow]
      exact congrArg (· ^ k) hz
  obtain ⟨_, H⟩ := sup_adjoin_roots P.host.φ₀ (classNumber_pos P.host.E) S hS hS'
  have hle : (⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) ≤ imField P.host.φ₀ ⊔ IntermediateField.adjoin ℚ S := by
    refine iSup₂_le fun j hj => sup_le (sup_le le_sup_left (le_sup_of_le_right ?_)) (le_sup_of_le_right ?_)
    · exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_left
    · refine IntermediateField.adjoin.mono _ _ _ ?_
      rintro z ⟨i, hz⟩
      exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hj, Set.mem_iUnion.2 ⟨i, hz⟩⟩)
  have : FiniteDimensional ℚ ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective
  have hN : NumberField ↥(⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) := NumberField.mk
  letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  refine ⟨hN, fun p hp hd => (Nat.Prime.dvd_mul hp).2 (H p hp (hd.trans ?_))⟩
  exact Int.natAbs_dvd_natAbs.2 (discr_dvd_discr _ _)

end GlobalTheory.Mem.KPsiRam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmallFieldClassFieldPieces

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host Formalism.L2.Rows GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open GlobalTheory.HilbertInClosure
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.SmallFieldPieces

section Copy

variable (ι : Qb →+* ℂ)

theorem qb_eq_of_map {L : Fld} {M : IntermediateField ℚ ℂ} (h : L.map ι.toRatAlgHom = M) : qb ι M = L := by
  rw [← h, qb, IntermediateField.comap_map]

theorem map_qb (M : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ M] : (qb ι M).map ι.toRatAlgHom = M := by
  refine IntermediateField.map_comap_eq_self fun z hz => ?_
  exact exists_eq_of_isAlgebraic ι
    (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨z, hz⟩ : M)))

theorem qb_mono {M N : IntermediateField ℚ ℂ} (h : M ≤ N) : qb ι M ≤ qb ι N := fun _ hx => h hx

theorem finrank_qb (M : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ M] :
    Module.finrank ℚ (qb ι M) = Module.finrank ℚ M :=
  (AlgEquiv.ofRingEquiv (R := ℚ) (f := qbEquiv ι M) fun q => by simp).toLinearEquiv.finrank_eq

theorem discr_qb (M : IntermediateField ℚ ℂ) [NumberField M] [NumberField (qb ι M)] : discr (qb ι M) = discr M :=
  discr_eq_discr_of_ringEquiv _ (qbEquiv ι M)

theorem qb_imField {E : Type} [Field E] [NumberField E] (j : E →ₐ[ℚ] Qb) (φ : E →+* ℂ) (h : ∀ x, ι (j x) = φ x) :
    qb ι (imField φ) = j.fieldRange := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, ι.injective ((h y).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, (h y).symm⟩

theorem qb_cycField {n : ℕ} (hn : n ≠ 0) : qb ι (cycField n) = muFld n := by
  refine qb_eq_of_map ι ?_
  rw [muFld, IntermediateField.adjoin_map]
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (cycField_le_iff.2 ?_)
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_cycField hn (by rw [← map_pow, show x ^ n = 1 from hx, map_one])
  · have h1 : rootOne n ^ n = 1 := (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
    obtain ⟨x, hx⟩ := exists_eq_of_isAlgebraic ι (z := rootOne n)
      (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn) (h1 ▸ isAlgebraic_one))
    exact IntermediateField.subset_adjoin ℚ _ ⟨x, ι.injective (by rw [map_pow, hx, h1, map_one]), hx⟩

theorem qb_KC (d : ℕ) : qb ι (KC d) = KQ d := by
  refine qb_eq_of_map ι ?_
  rw [KQ, sqQ, IntermediateField.adjoin_map]
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_simple_le_iff.2 ?_)
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : ι x ^ 2 = sqrtNegNat d ^ 2 := by
      rw [← map_pow, show x ^ 2 = _ from hx, sqrtNegNat_sq]
      simp
    have h2 := IntermediateField.mem_adjoin_simple_self ℚ (sqrtNegNat d)
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact (show ι x ∈ KC d from h ▸ h2)
    · exact (show ι x ∈ KC d from h ▸ neg_mem h2)
  · obtain ⟨x, hx⟩ := exists_eq_of_isAlgebraic ι (z := sqrtNegNat d)
      (IsAlgebraic.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isAlgebraic_nat d).neg))
    refine IntermediateField.subset_adjoin ℚ _ ⟨x, ι.injective ?_, hx⟩
    rw [map_pow, hx, sqrtNegNat_sq]
    simp

end Copy

theorem abelOver_of_isAbelianGalois {E : Type} [Field E] [NumberField E] (j : E →ₐ[ℚ] Qb) (L : Fld)
    (h : j.fieldRange ≤ L) (hab : letI := algThrough j L h; IsAbelianGalois E L) : AbelOver j.fieldRange L := by
  have hm : ∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → σ ∈ GalOf j.fieldRange := fun σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2
  refine ⟨h, fun σ hσ => map_mem_of_normal j L h ?_ σ (hm σ hσ),
    fun σ τ hσ hτ => (isAbelianGalois_iff j L h).1 hab σ (hm σ hσ) τ (hm τ hτ)⟩
  let := algThrough j L h
  infer_instance

theorem isHilbertCF_qb (hA : GlobalArtinReciprocity) (hW : WeberRayFieldSt) (ι : Qb →+* ℂ) {d : ℕ}
    {F : IntermediateField ℚ ℂ} {A : WeierstrassCurve F} (hd : d.Prime) (h4 : d % 4 = 3) (h3 : 3 < d)
    (hF : IsGoodCMCurve d F A) :
    ∃ (_ : NumberField (hilbertField d F)) (_ : FiniteDimensional ℚ (qb ι (hilbertField d F))),
      IsHilbertCF d (qb ι (hilbertField d F)) := by
  obtain ⟨hN, hdisc, h2, hR⟩ := isRayFieldIn_hilbertField hW d F A hd h4 h3 hF
  have hx : (IntermediateField.AdjoinSimple.gen ℚ (sqrtNegNat d)) ^ 2 =
      -(d : ℚ⟮sqrtNegNat d⟯) := Subtype.ext (by simpa using sqrtNegNat_sq d)
  have hTC := isTotallyComplex_of_sq_eq_neg hd.pos hx
  let j : ℚ⟮sqrtNegNat d⟯ →ₐ[ℚ] Qb :=
    ((qb ι ℚ⟮sqrtNegNat d⟯).val.toRingHom.comp (qbEquiv ι ℚ⟮sqrtNegNat d⟯).symm.toRingHom).toRatAlgHom
  have hj : ∀ x, ι (j x) = x := fun x =>
    congrArg Subtype.val ((qbEquiv ι ℚ⟮sqrtNegNat d⟯).apply_symm_apply x)
  have hr : j.fieldRange = KQ d := by
    rw [← qb_KC ι d, ← qb_imField ι j (ℚ⟮sqrtNegNat d⟯.val : ℚ⟮sqrtNegNat d⟯ →+* ℂ) hj]
    exact congrArg _ (le_antisymm (fun _ ⟨x, hx⟩ => hx ▸ x.2) fun z hz => ⟨⟨z, hz⟩, rfl⟩)
  have he : (ℚ⟮sqrtNegNat d⟯.val : ℚ⟮sqrtNegNat d⟯ →+* ℂ) = ι.comp j.toRingHom := RingHom.ext fun x => (hj x).symm
  obtain ⟨hN', h, hab, hd', hmax⟩ := hilbert_qb hA _ j ι _ (he ▸ hR)
  rw [hdisc, h2, Int.natAbs_neg, Int.natAbs_natCast] at hd' hmax
  refine ⟨hR.numberField, inferInstance, hr ▸ abelOver_of_isAbelianGalois j _ h hab, hd', fun L _ hL hU => ?_⟩
  have : NumberField L := {}
  rw [← hr] at hL
  refine hmax L hL.1 ((isAbelianGalois_iff j L hL.1).2 fun σ hσ τ hτ => hL.2.2 σ τ ?_ ?_) hU
  exacts [(IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ]

theorem squarefree_modulus (P : Pre) : Squarefree (modulus P) := by
  have g0 := P.host.g_prime 0
  have g1 := P.host.g_prime 1
  have p0 := P.host.pde_prime
  have p1 := P.host.pde'_prime
  simp only [modulus, Nat.squarefree_mul_iff, Nat.coprime_mul_iff_left, Nat.coprime_primes, g0, g1, p0, p1,
    g0.squarefree, g1.squarefree, p0.squarefree, p1.squarefree, and_true]
  exact ⟨⟨⟨(P.host.pde_ne_g 0).2.symm, (P.host.pde_ne_g 1).2.symm⟩, P.host.pde_ne⟩,
    ⟨(P.host.pde_ne_g 0).1.symm, (P.host.pde_ne_g 1).1.symm⟩, P.host.g_ne⟩

theorem coprime_discr {R : Ranks} (H : Host R) {p : ℕ} (hp : p % (H.QS * H.q * H.d) = 1) :
    Nat.Coprime p (discr H.E).natAbs := by
  have hc : Nat.Coprime p (H.QS * H.q * H.d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hp, Nat.gcd_one_left]
  refine Nat.Coprime.symm (Nat.coprime_of_dvd fun k hk h1 h2 => ?_)
  exact hk.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc h2 (H.der.discr_primes.1 k hk (Int.natCast_dvd.2 h1)))

theorem ray_qb (hA : GlobalArtinReciprocity) {P : Pre} (δ : FieldDat P) (T : Frame P.host) :
    ∃ _ : NumberField (qb T.ι δ.ray), AbelOver T.j.fieldRange (qb T.ι δ.ray) ∧
      (discr (qb T.ι δ.ray)).natAbs ∣
        (discr P.host.E).natAbs ^ (Module.finrank ℚ (qb T.ι δ.ray) / Module.finrank ℚ P.host.E) *
          modulus P ^ Module.finrank ℚ (qb T.ι δ.ray) := by
  have he : P.host.φ₀ = T.ι.comp T.j.toRingHom := RingHom.ext fun x => (T.phi0 x).symm
  obtain ⟨hN, h, hR⟩ := isRayField_qb T.j T.ι (he ▸ δ.isRay)
  refine ⟨hN, abelOver_of_isAbelianGalois _ _ h hR.1, ?_⟩
  let := algThrough T.j _ h
  rw [finrank_div]
  refine RayDiscr.natAbs_discr_dvd hA.rayClassFieldSt _ _ _ (squarefree_modulus P) ?_ hR
  exact (((coprime_discr _ (P.g_cond 0)).mul_left (coprime_discr _ (P.g_cond 1))).mul_left
    (coprime_discr _ P.pde_cond.1)).mul_left (coprime_discr _ P.pde_cond.2)

theorem kPsi_qb {P : Pre} (δ : FieldDat P) (T : Frame P.host) :
    ∃ S : Fin P.R.m → Finset Qb, (∀ j, (S j).card ≤ Nat.log 2 (classNumber P.host.E)) ∧
      (∀ j, ∀ y ∈ S j, ∃ n : ℕ, 0 < n ∧ n ∣ classNumber P.host.E ∧ y ^ n ∈ T.j.fieldRange) ∧
      qb T.ι (⨆ j ∈ Set.Icc 1 P.R.m, δ.KPsi j) =
        T.j.fieldRange ⊔ muFld (classNumber P.host.E) ⊔ IntermediateField.adjoin ℚ (⋃ j, (S j : Set Qb)) := by
  choose S hc hy hK using fun j : ℕ =>
    exists_kPsiField_generators P.R P.host δ.basis (P.R.sigW j).1 (P.R.sigW j).2
  have hE := qb_imField T.ι T.j P.host.φ₀ T.phi0
  have hal : ∀ j, ∀ y ∈ S j, IsAlgebraic ℚ y := fun j y h => by
    obtain ⟨n, hn, -, x, hx⟩ := hy j y h
    exact IsAlgebraic.of_pow hn (hx ▸ (Algebra.IsAlgebraic.isAlgebraic x).algHom P.host.φ₀.toRatAlgHom)
  refine ⟨fun j => (S (j + 1)).preimage T.ι T.ι.injective.injOn, fun j => le_trans ?_ (hc (j + 1)), fun j y h => ?_, ?_⟩
  · exact Finset.card_le_card_of_injOn T.ι (fun y h => Finset.mem_preimage.1 h) T.ι.injective.injOn
  · obtain ⟨n, hn, hd, h⟩ := hy _ _ (Finset.mem_preimage.1 h)
    exact ⟨n, hn, hd, hE ▸ mem_qb.2 (by rwa [map_pow])⟩
  · have hm := P.R.two_le_m
    have : Algebra.IsAlgebraic ℚ (imField P.host.φ₀) :=
      (AlgEquiv.ofInjectiveField P.host.φ₀.toRatAlgHom).isAlgebraic
    have h0 := classNumber_ne_zero P.host.E
    have : Algebra.IsAlgebraic ℚ (cycField (classNumber P.host.E)) :=
      IntermediateField.isAlgebraic_adjoin_simple (IsIntegral.of_pow (Nat.pos_of_ne_zero h0) (by
        rw [(Complex.isPrimitiveRoot_exp _ h0).pow_eq_one]; exact isIntegral_one))
    refine qb_eq_of_map _ ?_
    rw [← hE, ← qb_cycField T.ι h0, IntermediateField.map_sup, IntermediateField.map_sup, map_qb, map_qb,
      IntermediateField.adjoin_map, Set.image_iUnion]
    have hi : ∀ j, T.ι.toRatAlgHom '' ((S j).preimage T.ι T.ι.injective.injOn : Set Qb) = S j := fun j => by
      rw [Finset.coe_preimage]
      exact Set.image_preimage_eq_of_subset fun z hz => exists_eq_of_isAlgebraic _ (hal j z hz)
    simp only [hi, FieldDat.KPsi, hK]
    refine le_antisymm (sup_le ?_ (IntermediateField.adjoin_le_iff.2 (Set.iUnion_subset fun j => ?_)))
      (iSup₂_le fun j hj => sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _)
    · exact le_iSup₂_of_le 1 ⟨le_rfl, by omega⟩ le_sup_left
    · exact IntermediateField.adjoin_le_iff.1 (le_iSup₂_of_le (j + 1) ⟨by omega, j.2⟩ le_sup_right)
    · refine Set.subset_iUnion_of_subset ⟨j - 1, by have := hj.1; have := hj.2; omega⟩ ?_
      rw [Nat.sub_add_cancel hj.1]

theorem exists_twelfth_root (M : Fld) [NumberField M] {y : Qb} (hy : y ∈ M) :
    ∃ h : y ^ 12 ∈ M, (∃ I : FractionalIdeal (𝓞 M)⁰ M,
      FractionalIdeal.spanSingleton (𝓞 M)⁰ (⟨y ^ 12, h⟩ : M) = I ^ 12) ∧ M = M ⊔ IntermediateField.adjoin ℚ {y} :=
  ⟨pow_mem hy 12, ⟨FractionalIdeal.spanSingleton _ ⟨y, hy⟩, by rw [FractionalIdeal.spanSingleton_pow]; rfl⟩,
    (sup_eq_left.2 (IntermediateField.adjoin_simple_le_iff.2 hy)).symm⟩

theorem exists_pieces : GlobalArtinReciprocity → WeberRayFieldSt → ∀ (X : Stages) (f : Fr X.B.toPre)
    (δ : FieldDat X.B.toPre) (T : HostTied X.toD7), ∃ P : KsPieces X.toD7 T,
      P.HK = qb T.fr.ι (hilbertField X.B.host.d δ.jField) ∧ P.rcf = qb T.fr.ι δ.ray ∧ P.M = qb T.fr.ι δ.M ∧
        P.MDel = qb T.fr.ι δ.M' ∧ P.KPs = qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) := by
  intro hA hW X _ δ T
  have h16 : X.B.host.d % 16 = 7 := X.B.host.hyp.2.2.2.1
  obtain ⟨hH, hH', hilb⟩ := isHilbertCF_qb hA hW T.fr.ι X.B.host.hyp.2.1 (by omega) (by omega) δ.good
  obtain ⟨hR, hab, hcond⟩ := ray_qb hA δ T.fr
  obtain ⟨hF, hEll, -, -, -, -, hred⟩ := δ.good
  obtain ⟨hMf, hdeg⟩ := TorsionDegree.finrank_torsionField_le X.B.host.d δ.jField δ.curve
  have hM : NumberField δ.M := @NumberField.of_module_finite ℚ _ _ _ _ _ hMf
  have hMq := numberField_qb T.fr.ι δ.M
  have hMM : δ.M' = δ.M := DiscRoot.discField_eq_torsionField _ _ _
  obtain ⟨hK, hKram⟩ := KPsiRam.prime_dvd_discr_iSup_kPsi _ δ
  have hKq := numberField_qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j :)
  have hHq := numberField_qb T.fr.ι (hilbertField X.B.host.d δ.jField)
  have hram : ∀ p : ℕ, p.Prime → p ∣ (discr (qb T.fr.ι δ.M)).natAbs → p ∣ 6 * X.B.host.d := fun p hp h => by
    rw [discr_qb] at h
    have : NumberField (torsionField X.B.host.d δ.curve) := hM
    refine (TorsionRam.dvd_discr_torsionField _ _ δ.curve hred p hp h).elim id fun h => ?_
    rw [← discr_qb T.fr.ι, show (discr (qb T.fr.ι (hilbertField X.B.host.d δ.jField))).natAbs = _ from hilb.2.1] at h
    exact (hp.dvd_of_dvd_pow h).mul_left 6
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (δ.curve.Δ : ℂ) (show 0 < 12 by norm_num)
  have hzM : z ∈ δ.M := hMM ▸ ((discField_le_iff _ δ.curve).1 le_rfl).2.2.2 z hz
  have hz0 : z ≠ 0 := fun h => δ.curve.isUnit_Δ.ne_zero (Subtype.ext (by rw [← hz, h]; norm_num))
  let y := (qbEquiv T.fr.ι δ.M).symm ⟨z, hzM⟩
  have hy0 : (y : Qb) ≠ 0 := fun h => hz0 (congrArg Subtype.val
    ((map_eq_zero (qbEquiv T.fr.ι δ.M).symm).1 (Subtype.ext h)))
  obtain ⟨hy, hI, hgen⟩ := exists_twelfth_root _ y.2
  obtain ⟨S, hS1, hS2, hS3⟩ := kPsi_qb δ T.fr
  exact ⟨{
    HK := qb T.fr.ι (hilbertField X.B.host.d δ.jField)
    rcf := qb T.fr.ι δ.ray
    M := qb T.fr.ι δ.M
    MDel := qb T.fr.ι δ.M
    KPs := qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j)
    HK_hilb := hilb
    E_le_rcf := hab.1
    rcf_abel := hab
    rcf_cond := hcond
    HK_le_M := qb_mono _ (hilbertField_le_torsionField _ _)
    M_deg := by rw [finrank_qb, finrank_qb]; exact hdeg
    M_ram := hram
    MDel_gen := ⟨y, hy, hy0, hI, hgen⟩
    MDel_ram := hram
    KPs_gen := ⟨S, hS1, hS2, hS3⟩
    KPs_ram := fun p hp h => hKram p hp (by rwa [discr_qb] at h)
    M_le_MDel := le_rfl
    E_le_KPs := hS3 ▸ le_sup_left.trans le_sup_left }, rfl, rfl, rfl, by rw [hMM], rfl⟩

end GlobalTheory.SmallFieldPieces

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmallFieldClassFieldPiecesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host Formalism.L2.Rows GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_smallField_classFieldPieces : GlobalArtinReciprocity → WeberRayFieldSt → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : FieldDat X.B.toPre) (T : HostTied X.toD7), ∃ P : KsPieces X.toD7 T, P.HK = qb T.fr.ι (hilbertField X.B.host.d δ.jField) ∧ P.rcf = qb T.fr.ι δ.ray ∧ P.M = qb T.fr.ι δ.M ∧ P.MDel = qb T.fr.ι δ.M' ∧ P.KPs = qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) := by
  first | exact @GlobalTheory.SmallFieldPieces.exists_pieces | exact GlobalTheory.SmallFieldPieces.exists_pieces | (intros; apply GlobalTheory.SmallFieldPieces.exists_pieces <;> assumption)
end
end
