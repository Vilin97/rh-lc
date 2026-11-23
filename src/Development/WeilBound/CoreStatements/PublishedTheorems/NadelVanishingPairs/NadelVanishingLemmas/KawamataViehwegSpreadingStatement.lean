module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenPreimageBasicOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingSpecializes
public import Mathlib.RingTheory.FiniteType
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.RingTheory.Jacobson.Ring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumberFieldToModPSquared
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegModPSquared
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeToNumberField

section

@[expose] public section

open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem exists_numberField_of_finiteType_rat (R : Type) [CommRing R] [Nontrivial R] [Algebra ℚ R]
    [Algebra.FiniteType ℚ R] : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (φ : R →+* K), True := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℚ (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m) Ideal.Quotient.mk_surjective
  haveI : Module.Finite ℚ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (R ⧸ m)
  haveI : CharZero (R ⧸ m) := algebraRat.charZero _
  have hfin := (inferInstance : Module.Finite ℚ (R ⧸ m))
  haveI : @FiniteDimensional ℚ (R ⧸ m) _ _ (@Algebra.toModule ℚ (R ⧸ m) _ _ DivisionRing.toRatAlgebra) := by
    have e : (Ideal.Quotient.algebra ℚ : Algebra ℚ (R ⧸ m)) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
    convert hfin
    first
      | exact (congrArg (@Algebra.toModule ℚ (R ⧸ m) _ _) e).symm
      | (rw [← e]; rfl)
  haveI : NumberField (R ⧸ m) := ⟨⟩
  exact ⟨R ⧸ m, inferInstance, inferInstance, Ideal.Quotient.mk m, trivial⟩

theorem exists_numberField_point_ne_zero :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A →
      ∀ a : A, a ≠ 0 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (χ : A →+* K), χ a ≠ 0 := by
  intro A _ _ _ hA a ha
  classical
  obtain ⟨s, hs⟩ := hA.out
  let F := FractionRing A
  let f : A →+* F := algebraMap A F
  let B : Subalgebra ℚ F := Algebra.adjoin ℚ (insert (f a)⁻¹ ((s.image f : Finset F) : Set F))
  have hmem : ∀ x : A, f x ∈ B := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (by simpa using ⟨x, hx, rfl⟩))
    | algebraMap n =>
      have : f (algebraMap ℤ A n) = algebraMap ℚ F (n : ℚ) := by simp [f]
      rw [this]; exact B.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact B.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact B.mul_mem hx hy
  have hinv : (f a)⁻¹ ∈ B := Algebra.subset_adjoin (Set.mem_insert _ _)
  haveI hBft : Algebra.FiniteType ℚ B := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact ⟨insert (f a)⁻¹ (s.image f), by simp [B]⟩
  have hfa : f a ≠ 0 := by
    simpa [f] using (IsFractionRing.injective A F).ne ha
  let ψ : A →+* B := f.codRestrict B hmem
  have hu : IsUnit (ψ a) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(f a)⁻¹, hinv⟩, Subtype.ext ?_⟩
    show f a * (f a)⁻¹ = 1
    exact mul_inv_cancel₀ hfa
  obtain ⟨K, _, _, φ, -⟩ := exists_numberField_of_finiteType_rat B
  exact ⟨K, inferInstance, inferInstance, φ.comp ψ, (hu.map φ).ne_zero⟩

end GlobalTheory
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FiniteTypeToNumberField

section

@[expose] public section

open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.finite_type_to_number_field : ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A → ∀ a : A, a ≠ 0 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (χ : A →+* K), χ a ≠ 0 := by
  first | exact @_root_.GlobalTheory.exists_numberField_point_ne_zero | exact _root_.GlobalTheory.exists_numberField_point_ne_zero | (intros; apply _root_.GlobalTheory.exists_numberField_point_ne_zero <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NumberFieldToModPSquared

section

@[expose] public section

open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.number_field_to_mod_p_squared : ∀ (K : Type) [Field K] [NumberField K] (S : Finset K) (n : ℕ), ∃ p : ℕ, p.Prime ∧ n < p ∧ Nonempty (Subring.closure (S : Set K) →+* ZMod (p ^ 2)) := by
  first | exact @_root_.GlobalTheory.exists_prime_sq_ringHom_of_closure | exact _root_.GlobalTheory.exists_prime_sq_ringHom_of_closure | (intros; apply _root_.GlobalTheory.exists_prime_sq_ringHom_of_closure <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FiniteTypeToModPSquared

section

@[expose] public section

open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem exists_ringHom_zmod_prime_sq_isUnit_of_finiteType :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A → ∀ a : A, a ≠ 0 → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ χ : A →+* ZMod (p ^ 2), IsUnit (χ a) := by
  intro A _ _ _ hA a ha n
  classical
  obtain ⟨K, _, _, χ₀, hχ⟩ := GlobalTheory.T.finite_type_to_number_field A hA a ha
  obtain ⟨s, hs⟩ := hA.out
  obtain ⟨p, hp, hn, ⟨ψ⟩⟩ := GlobalTheory.T.number_field_to_mod_p_squared K (insert (χ₀ a)⁻¹ (s.image χ₀)) n
  set R := Subring.closure ((insert (χ₀ a)⁻¹ (s.image χ₀) : Finset K) : Set K) with hR
  have hmem : ∀ x : A, χ₀ x ∈ R := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      apply Subring.subset_closure
      simp only [Finset.coe_insert, Finset.coe_image]
      exact Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact R.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact R.mul_mem hx hy
  have hinv : (χ₀ a)⁻¹ ∈ R := by
    apply Subring.subset_closure
    simp
  refine ⟨p, hp, hn, ψ.comp (χ₀.codRestrict R hmem), ?_⟩
  rw [RingHom.comp_apply]
  apply IsUnit.map
  refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ ?_
  apply Subtype.ext
  simp [hχ]

end GlobalTheory
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncBaseChange

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem relSnc_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → RelSnc f d L σ → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) := by
  intro R R' _ _ φ X X' f f' π d s L σ hpb h
  refine ⟨fun i => ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull (h.isLB i) π, fun x => ?_⟩
  obtain ⟨C, hC⟩ := h.chart (π.base x)
  obtain ⟨C', hC'⟩ := sncChart_baseChange R R' φ X X' f f' π d s L σ C hpb
  exact ⟨C', by rw [hC']; exact hC⟩

end GlobalTheory.LogPair
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegSpreading

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem vanishing_charZero_fibre_of_finiteType : ∀ (R k : Type) [CommRing R] [Field k] [CharZero k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f], Algebra.FiniteType ℤ R → Function.Injective φ → IsPullback π f' f (spMap φ) → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : A.IsLB) (r : ℕ) (b : Fin s → ℕ), IsAmpleLB (A.pull π) → 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (M.pull π)) q) := by
  intro R k _ _ _ φ X X' f f' π d _ _ hR hφ hpb s L σ h K M A hM hA r b hAmp hr hb hrel q hq
  haveI : IsDomain R := Function.Injective.isDomain φ hφ
  haveI : CharZero R := (RingHom.charZero_iff hφ).mpr inferInstance
  haveI := hR
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  haveI hstab := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  haveI : Smooth f := SmoothOfRelativeDimension.smooth d f
  haveI : Flat f := inferInstance
  let KR := FractionRing R
  let ι : KR →+* k := IsFractionRing.lift hφ
  have hφι : φ = ι.comp (algebraMap R KR) := by
    ext x
    simp [ι, IsFractionRing.lift_algebraMap]
  have hsp : spMap φ = spMap ι ≫ spMap (algebraMap R KR) := by
    rw [hφι]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) hpb ‹IsProper f›
  have hAπ : (A.pull π).IsLB := LB.isLB_pull hA π
  have hrelK' : Out.RelAmple (Over.mk f') (A.pull π) :=
    haveI : IsProper (Over.mk f').hom := (inferInstance : IsProper f')
    (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f') hAπ).mpr hAmp
  have hgenPb := IsPullback.of_hasPullback f (spMap (algebraMap R KR))
  have hA1 : (A.pull (pullback.fst f (spMap (algebraMap R KR)))).IsLB := LB.isLB_pull hA _
  have hgen : Out.RelAmple (Over.mk (pullback.snd f (spMap (algebraMap R KR))))
      (A.pull (pullback.fst f (spMap (algebraMap R KR)))) :=
    FibreAmple.relAmple_of_fieldExtension hA ι hgenPb (hsp ▸ hpb) hA1 ((cls_eq_iff hA1 hA1).mp rfl) hrelK'
  obtain ⟨a, ha, hspread⟩ := AmpleSpread.relAmple_spread R KR (Over.mk f) A ‹IsProper f› hA hgen
  obtain ⟨p, hp, hdp, χ, hχ⟩ := exists_ringHom_zmod_prime_sq_isUnit_of_finiteType R hR a ha d
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let c : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
  have hY := IsPullback.of_hasPullback f (spMap χ)
  haveI : SmoothOfRelativeDimension d (pullback.snd f (spMap χ)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) hY inferInstance
  have h1 := IsPullback.of_hasPullback (pullback.snd f (spMap χ)) (spMap c)
  haveI : SmoothOfRelativeDimension d (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) h1 inferInstance
  haveI : IsProper (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) := inferInstance
  have hsp2 : spMap c ≫ spMap χ = spMap (c.comp χ) := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hρ : IsPullback (pullback.fst (pullback.snd f (spMap χ)) (spMap c) ≫ pullback.fst f (spMap χ))
      (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) f (spMap (c.comp χ)) :=
    hsp2 ▸ h1.paste_horiz hY
  set ρ := pullback.fst (pullback.snd f (spMap χ)) (spMap c) ≫ pullback.fst f (spMap χ) with hρdef
  set f₁ := pullback.snd (pullback.snd f (spMap χ)) (spMap c) with hf₁
  have hspec := hspread (ZMod p) (c.comp χ) (hχ.map c)
  have hid : spMap (RingHom.id (ZMod p)) ≫ spMap (c.comp χ) = spMap (c.comp χ) := by
    simp [spMap]
  have hAρ : (A.pull ρ).IsLB := LB.isLB_pull hA ρ
  have hamp1 : Out.RelAmple (Over.mk f₁) (A.pull ρ) :=
    FibreAmple.relAmple_of_fieldExtension hA (RingHom.id (ZMod p)) hρ
      (hid.symm ▸ IsPullback.of_hasPullback f (spMap (c.comp χ))) hAρ ((cls_eq_iff hAρ hAρ).mp rfl) hspec
  haveI : IsProper (Over.mk f₁).hom := (inferInstance : IsProper f₁)
  have hampX : IsAmpleLB (A.pull ρ) := (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f₁) hAρ).mp hamp1
  have hproj : IsProjOver f₁ := (isProjOver_iff_isProper_and_exists_isAmpleLB f₁).mpr ⟨inferInstance, _, hampX⟩
  have hL := LogPair.relSnc_baseChange R (ZMod (p ^ 2)) χ X _ f _ _ d s L σ hY h
  let K₁ : CanonLB f₁ d := CanonLB.baseChange hρ K
  have hMρ : (M.pull ρ).IsLB := LB.isLB_pull hM ρ
  have hrel1 : r • cls (M.pull ρ) hMρ = r • cls K₁.bundle K₁.isLB +
      ∑ i, b i • pull (pullback.fst (pullback.snd f (spMap χ)) (spMap c))
        (cls ((L i).pull (pullback.fst f (spMap χ))) (LB.isLB_pull (h.isLB i) _)) + cls (A.pull ρ) hAρ := by
    have e := congrArg (pull ρ) hrel

    simp only [map_add (f := _), map_nsmul, map_sum] at e
    have eK : cls K₁.bundle K₁.isLB = pull ρ (cls K.bundle K.isLB) := cls_pull K.isLB ρ K₁.isLB
    rw [cls_pull hM ρ, eK, cls_pull hA ρ]
    convert e using 4
    rw [cls_pull (h.isLB _) _, ← pull_comp]
  have hvan := charp_vanishing_liftable p _ _ (pullback.snd f (spMap χ)) f₁
    (pullback.fst (pullback.snd f (spMap χ)) (spMap c)) d h1 hproj hdp s
    (fun i => (L i).pull (pullback.fst f (spMap χ))) (fun i => Cartier.secPull (σ i) _) hL K₁
    (M.pull ρ) (A.pull ρ) hMρ hampX r b hr hb hrel1 q hq
  have hker : RingHom.ker φ ≤ RingHom.ker (c.comp χ) := by
    rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ]
    exact bot_le
  exact SemicontLB.subsingleton_coh_pull_of_ker_le R X f M hM (ZMod p) k (c.comp χ) φ _ X' f₁ f' ρ π hρ hpb hker q hvan

end GlobalTheory
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegSpreadingStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.kawamata_viehweg_spreading : ∀ (R k : Type) [CommRing R] [Field k] [CharZero k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f], Algebra.FiniteType ℤ R → Function.Injective φ → IsPullback π f' f (spMap φ) → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : A.IsLB) (r : ℕ) (b : Fin s → ℕ), IsAmpleLB (A.pull π) → 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (M.pull π)) q) := by
  first | exact @_root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType | exact _root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType | (intros; apply _root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType <;> assumption)
end
end
