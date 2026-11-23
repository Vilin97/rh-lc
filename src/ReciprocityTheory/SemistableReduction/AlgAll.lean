module

public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
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
public import ReciprocityTheory.SemistableReduction.DetSubtypeCompAssociatedProd
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.SemistableReduction.GaussIndepOfLeTrdeg
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.SemistableReduction.ExistsDualDerivations
public import ReciprocityTheory.SemistableReduction.IntegralClosureRankAndResidueTrdegLe
public import ReciprocityTheory.SemistableReduction.NormValuationEqFactorization

-- Source module: ReciprocityTheory.SemistableReduction.GaussValExists

section

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

noncomputable def gaussRed {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    MvPolynomial σ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) :=
  ∑ α ∈ p.support, monomial α (IsLocalRing.residue _ ⟨p.coeff α, hc α⟩)

theorem gaussRed_coeff {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) (α : σ →₀ ℕ) :
    (gaussRed V p hc).coeff α = IsLocalRing.residue _ ⟨p.coeff α, hc α⟩ := by
  classical
  unfold gaussRed
  rw [MvPolynomial.coeff_sum]
  by_cases h : α ∈ p.support
  · rw [Finset.sum_eq_single α]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg hb]
    · intro h'
      exact absurd h h'
  · have h0 : p.coeff α = 0 := by simpa [MvPolynomial.mem_support_iff] using h
    have hz : (⟨p.coeff α, hc α⟩ : V.comap (algebraMap Ω U)) = 0 := Subtype.ext h0
    rw [Finset.sum_eq_zero, hz, map_zero]
    intro b hb
    rw [MvPolynomial.coeff_monomial, if_neg]
    rintro rfl
    exact h hb

theorem gaussRed_eval {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    letI := residueAlgebra V (algebraMap Ω U)
    ∃ h : aeval t p ∈ V, IsLocalRing.residue V ⟨aeval t p, h⟩ =
      aeval (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) (gaussRed V p hc) := by
  try dsimp only
  letI := residueAlgebra V (algebraMap Ω U)
  classical
  obtain ⟨y, hydef⟩ : ∃ y : V, y = ∑ α ∈ p.support,
      comapInclusion V (algebraMap Ω U) ⟨p.coeff α, hc α⟩ *
        ∏ s ∈ α.support, (⟨t s, ht s⟩ : V) ^ α s := ⟨_, rfl⟩
  have hy : (y : U) = aeval t p := by
    change V.subtype y = _
    rw [hydef, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]

    simp only [map_sum, map_mul, map_prod, map_pow]
    rfl
  have hmem : aeval t p ∈ V := by
    rw [← hy]
    exact y.2
  refine ⟨hmem, ?_⟩
  have hyy : (⟨aeval t p, hmem⟩ : V) = y := Subtype.ext hy.symm

  rw [hyy, hydef, map_sum]
  unfold gaussRed

  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.aeval_monomial]
  simp only [map_mul, map_prod, map_pow]
  congr 1

end ReciprocityTheory.MultiplicativeHeights
end
end

-- Source module: ReciprocityTheory.SemistableReduction.GaussExtensionAndResidueTrdegEq

section

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

theorem residueTrdeg_holds (hTR : TRStatement) : ResidueTrdegStatement := by
  intro K Ω U _ _ _ _ _ D hD σ _ t V ht τ _ u p hp hcard hpu hind
  letI _iW := residueAlgebra V (algebraMap Ω U)
  letI _io := residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
  letI : Algebra (IsLocalRing.ResidueField
      ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (IsLocalRing.ResidueField V) :=
    ((algebraMap _ (IsLocalRing.ResidueField V)).comp
      (algebraMap _ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
  have hTRW := hTR K Ω (V.comap (algebraMap Ω U))
  rw [hD] at hTRW
  have hST : IsScalarTower
      (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) (IsLocalRing.ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hres : ∀ j, IsLocalRing.residue V (u j) =
      aeval (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) (gaussRed V (p j) (hp j)) := by
    intro j
    obtain ⟨h, he⟩ := gaussRed_eval t V ht (p j) (hp j)
    have : u j = ⟨aeval t (p j), h⟩ := Subtype.ext (hpu j).symm
    rw [this, he]
  have hcardc : Cardinal.mk τ = ((Fintype.card σ + D : ℕ) : Cardinal) := by
    rw [Cardinal.mk_fintype, hcard]
  have hσ := Cardinal.mk_fintype σ
  have hmemW : ∀ j, IsLocalRing.residue V (u j) ∈
      Algebra.adjoin (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (Set.range fun s => IsLocalRing.residue V ⟨t s, ht s⟩) := by
    intro j
    rw [hres j]
    exact gauss_aeval_mem _ _ (Algebra.adjoin _ _).toSubring
      (fun α => Subalgebra.algebraMap_mem _ _) (fun s => Algebra.subset_adjoin ⟨s, rfl⟩)
  have hW := gauss_card_le_trdeg_add _ _ hind hmemW
  rw [hcardc] at hW
  obtain ⟨h2, h3⟩ := gauss_card_arith hW hTRW (hσ ▸ gauss_trdeg_adjoin_le _)
  refine ⟨?_, h2, gauss_indep_of_le_trdeg _ (hσ.trans h3.symm).le⟩
  intro k₁ hk₁
  letI : Algebra k₁ (IsLocalRing.ResidueField V) :=
    ((algebraMap (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
      (IsLocalRing.ResidueField V)).comp (algebraMap k₁ _)).toAlgebra
  have hST1 : IsScalarTower
      (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      k₁ (IsLocalRing.ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmem1 : ∀ j, IsLocalRing.residue V (u j) ∈
      Algebra.adjoin k₁ (Set.range fun s => IsLocalRing.residue V ⟨t s, ht s⟩) := by
    intro j
    rw [hres j]
    refine gauss_aeval_mem _ _ (Algebra.adjoin k₁ _).toSubring (fun α => ?_)
      (fun s => Algebra.subset_adjoin ⟨s, rfl⟩)
    have hc : (gaussRed V (p j) (hp j)).coeff α ∈ k₁ := by
      rw [gaussRed_coeff]; exact hk₁ j α
    exact Subalgebra.algebraMap_mem (Algebra.adjoin k₁ _) (⟨_, hc⟩ : k₁)
  have h1 := @gauss_card_le_trdeg_add _ _ _ _ _ _ _ _ _ hST1 _ _ _ _ hind hmem1
  rw [hcardc] at h1
  have hk : Algebra.trdeg _ k₁ ≤ (D : Cardinal) :=
    (trdeg_le_of_injective k₁.val Subtype.val_injective).trans hTRW
  exact (gauss_card_arith h1 hk (hσ ▸ gauss_trdeg_adjoin_le _)).1

end ReciprocityTheory.MultiplicativeHeights
end
end

-- Source module: ReciprocityTheory.SemistableReduction.GenericImageFinite

section

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial DerivationAlgebraicIndependence

theorem trdeg_sField {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ) :
    Algebra.trdeg K (SField Ω D m) = Algebra.trdeg K Ω + ((1 + (D + 1) * m : ℕ) : Cardinal) := by
  classical
  haveI : FaithfulSMul K Ω :=
    (faithfulSMul_iff_algebraMap_injective K Ω).2 (algebraMap K Ω).injective
  haveI : FaithfulSMul Ω (MvPolynomial (SVars D m) Ω) :=
    (faithfulSMul_iff_algebraMap_injective Ω _).2 (MvPolynomial.C_injective _ _)
  haveI : FaithfulSMul (MvPolynomial (SVars D m) Ω) (SField Ω D m) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (IsFractionRing.injective (MvPolynomial (SVars D m) Ω) (SField Ω D m))
  have h1 := trdeg_add_eq K (MvPolynomial (SVars D m) Ω) (A := SField Ω D m)
  have h2 := trdeg_add_eq K Ω (A := MvPolynomial (SVars D m) Ω)
  have h3 : Algebra.trdeg (MvPolynomial (SVars D m) Ω) (SField Ω D m) = 0 :=
    trdeg_eq_zero_iff.2
      (IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (SVars D m) Ω)))
  have h4 : Algebra.trdeg Ω (MvPolynomial (SVars D m) Ω) =
      ((1 + (D + 1) * m : ℕ) : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
    congr 1
    simp [SVars, Fintype.card_sum, Fintype.card_prod]
  rw [← h1, h3, add_zero, ← h2, h4]

theorem genericImageFinite : FieldOfSStatement := by
  classical
  unfold FieldOfSStatement
  intro K Ω _ _ _ _ D m x hfg htr hJ
  obtain ⟨J, hJ⟩ := hJ
  set v : Fin D → KaehlerDifferential K Ω := fun a => KaehlerDifferential.D K Ω (x (J a)) with hv
  have hli : LinearIndependent Ω v := hJ
  have hφ : ∀ a : Fin D, ∃ φ : KaehlerDifferential K Ω →ₗ[Ω] Ω,
      ∀ b, φ (v b) = if a = b then 1 else 0 := by
    intro a
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply a).comp hli.repr)
    refine ⟨g, fun b => ?_⟩
    have hb : v b ∈ Submodule.span Ω (Set.range v) := Submodule.subset_span ⟨b, rfl⟩
    have h := congrArg (fun f => f ⟨v b, hb⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h, Finsupp.lapply_apply, hli.repr_eq_single b ⟨v b, hb⟩ rfl, Finsupp.single_apply]
    simp [eq_comm]
  choose φ hφ using hφ
  let δ : Fin D → Derivation K Ω Ω := fun a => (φ a).compDer (KaehlerDifferential.D K Ω)
  have hδ : ∀ a b, δ a (x (J b)) = if a = b then 1 else 0 := fun a b => hφ a b
  have hg := DerivationAlgebraicIndependence.gFam_indep (K := K) x J δ hδ
  have hind : AlgebraicIndependent K (sImage (D := D) x) := by
    have h1 := hg.comp _ (DerivationAlgebraicIndependence.eIdx_injective D m)
    have h2 := h1.map'
      (f := IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m))
      (IsFractionRing.injective _ _)
    convert h2 using 1
    funext p
    simp [DerivationAlgebraicIndependence.sImage_eq]
  refine ⟨hind, ?_⟩
  have htrS : Algebra.trdeg K (SField Ω D m) = (((D + 1) * (m + 1) : ℕ) : Cardinal) := by
    rw [trdeg_sField, htr, ← Nat.cast_add]
    congr 1
    ring
  have hTB : IsTranscendenceBasis K (sImage (D := D) x) := by
    refine hind.isTranscendenceBasis_of_lift_trdeg_le ?_ ?_
    · rw [htrS]
      exact Cardinal.natCast_lt_aleph0
    · rw [htrS]
      simp
  have halg := hTB.isAlgebraic_field
  set E := IntermediateField.adjoin K (Set.range (sImage (D := D) x))
  obtain ⟨s, hs⟩ := hfg
  let f : Ω →ₐ[K] SField Ω D m :=
    (IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m)).comp
      (IsScalarTower.toAlgHom K Ω (MvPolynomial (SVars D m) Ω))
  let S : Set (SField Ω D m) := f '' (s : Set Ω) ∪
    Set.range (fun i => algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) (MvPolynomial.X i))
  have hSfin : S.Finite := (s.finite_toSet.image _).union (Set.finite_range _)
  haveI : Finite S := hSfin.to_subtype
  let L := IntermediateField.adjoin E S
  have hK : IntermediateField.adjoin K (f '' (s : Set Ω)) ≤ L.restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact IntermediateField.subset_adjoin E S (Or.inl hz)
  have hω : ∀ ω : Ω, f ω ∈ L := by
    intro ω
    have h1 : f ω ∈ (IntermediateField.adjoin K (s : Set Ω)).map f :=
      (IntermediateField.mem_map _).2 ⟨ω, by rw [hs]; trivial, rfl⟩
    rw [IntermediateField.adjoin_map] at h1
    exact hK h1
  have hP : ∀ p : MvPolynomial (SVars D m) Ω,
      algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) p ∈ L := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h := hω a
      simpa [f, MvPolynomial.algebraMap_eq] using h
    | add p q hp hq =>
      rw [map_add (f := _)]
      exact L.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact L.mul_mem hp (IntermediateField.subset_adjoin E S (Or.inr ⟨i, rfl⟩))
  have htop : L = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (SVars D m) Ω) z
    exact L.div_mem (hP a) (hP b)
  have hfd : FiniteDimensional E L :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end ReciprocityTheory.MultiplicativeHeights
end
end

-- Source module: ReciprocityTheory.SemistableReduction.AlgAll

section

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem fieldOfS : FieldOfSStatement := genericImageFinite

theorem dedekindRank : DedekindRankStatement := integralClosureRank_and_residueTrdegLe.1

theorem residueTrdeg : ResidueTrdegStatement := residueTrdeg_holds residueTrdegLe

theorem normLength : NormLengthStatement := gaugeSplitting_holds

theorem normOrd : NormOrdStatement := normValuation_eq_factorization normLength

end ReciprocityTheory.MultiplicativeHeights.Closed
end
end
