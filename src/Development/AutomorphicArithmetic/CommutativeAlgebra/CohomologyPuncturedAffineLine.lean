module

public import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
import Development.EtaleCohomology.EtaleSheaves.LineOneCut
import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
public import Development.EtaleCohomology.EtaleSheaves.LineOneCut
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsGoodRootOfHenselianSepClosedResidue
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsNearRootOfUnityProductDecomposition
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsAffineIsDomainPullbackStandardOpens
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AutomorphicArithmetic.CommutativeAlgebra.RootsOfUnityEqLocallyConstantPowersSpectrum
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ClosedFiberAffineSurjectiveKerMaximalIdeal

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

theorem UpperTheory.closed_fiber_affine_surjective_ker_maximalIdeal :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] {X F : Scheme.{0}} [IsAffine X] (p : X ⟶ Spec (CommRingCat.of A)) (r : F ⟶ X) (c : F ⟶ Spec (CommRingCat.of (ResidueField A))),
      IsPullback r c p (cpt A) → IsAffine F ∧ Function.Surjective r.appTop.hom ∧ RingHom.ker r.appTop.hom = (maximalIdeal A).map (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (p).appTop).hom) := by
  intro A _ _ X F _ p r c h
  have hcpt : IsClosedImmersion (cpt A) :=
    IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective)
  have hr : IsClosedImmersion r := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hcpt
  obtain ⟨hF, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine r
  refine ⟨hF, hsurj, ?_⟩
  have hinv : X.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    simp
  have key : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ r.appTop =
      CommRingCat.ofHom (residue A) ≫ (Scheme.ΓSpecIso _).inv ≫ c.appTop := by
    rw [← Scheme.Hom.comp_appTop, h.w, Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  set φ := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop).hom with hφ
  set I := (maximalIdeal A).map φ with hI
  apply le_antisymm
  · intro b hb
    rw [RingHom.mem_ker] at hb
    let π : Γ(X, ⊤) ⟶ CommRingCat.of (Γ(X, ⊤) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
    let χ0 : A ⧸ maximalIdeal A →+* Γ(X, ⊤) ⧸ I :=
      Ideal.Quotient.lift (maximalIdeal A) ((Ideal.Quotient.mk I).comp φ)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem φ ha))
    let χ : CommRingCat.of (ResidueField A) ⟶ CommRingCat.of (Γ(X, ⊤) ⧸ I) := CommRingCat.ofHom χ0
    let z : Spec (CommRingCat.of (Γ(X, ⊤) ⧸ I)) ⟶ X := Spec.map π ≫ X.isoSpec.inv
    have hz : z ≫ p = Spec.map χ ≫ cpt A := by
      apply ext_of_isAffine
      rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of A)).inv,
        ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) ⧸ I))).hom]
      simp only [z, cpt, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
        Scheme.ΓSpecIso_naturality_assoc, reassoc_of% hinv, Iso.inv_hom_id_assoc, Category.id_comp]
      ext a
      rfl
    let u := h.lift z (Spec.map χ) hz
    have hu : u ≫ r = z := h.lift_fst _ _ _
    have hzt : z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) ⧸ I))).hom = π := by
      simp only [z, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
        reassoc_of% hinv, Category.id_comp]
    have e1 : z.appTop = r.appTop ≫ u.appTop := by
      rw [← Scheme.Hom.comp_appTop, hu]
    have e2 := congrArg (fun f => f.hom b) hzt
    rw [e1] at e2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, hb, map_zero] at e2
    exact Ideal.Quotient.eq_zero_iff_mem.1 e2.symm
  · refine Ideal.map_le_iff_le_comap.2 (fun a ha => ?_)
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e := congrArg (fun f => f.hom a) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    rw [hφ, CommRingCat.hom_comp, RingHom.comp_apply, e, (IsLocalRing.residue_eq_zero_iff a).2 ha, map_zero, map_zero]

end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiberPullbackSquareOfOpenImmersions

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

theorem UpperTheory.exists_fiber_pullback_square_of_open_immersions :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
      ∃ (r : pullback (fibMap p ι₁) (fibMap p ι₂) ⟶ pullback ι₁ ι₂) (c : pullback (fibMap p ι₁) (fibMap p ι₂) ⟶ Spec (CommRingCat.of (ResidueField A))),
        IsPullback r c (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) (cpt A) ∧
        r ≫ pullback.fst ι₁ ι₂ = pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ∧
        r ≫ pullback.snd ι₁ ι₂ = pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) := by
  intro A _ _ Z U V p ι₁ ι₂
  have m1 : ∀ {Y : Scheme.{0}} (ι : Y ⟶ Z), fibMap p ι ≫ pullback.fst p (cpt A) = pullback.fst (ι ≫ p) (cpt A) ≫ ι := by
    intro Y ι
    exact pullback.lift_fst _ _ _
  have m2 : ∀ {Y : Scheme.{0}} (ι : Y ⟶ Z), fibMap p ι ≫ pullback.snd p (cpt A) = pullback.snd (ι ≫ p) (cpt A) := by
    intro Y ι
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have m1' : ∀ {Y W : Scheme.{0}} (ι : Y ⟶ Z) (k : Z ⟶ W), fibMap p ι ≫ pullback.fst p (cpt A) ≫ k = pullback.fst (ι ≫ p) (cpt A) ≫ ι ≫ k := by
    intro Y W ι k
    rw [← Category.assoc, m1, Category.assoc]
  have m2' : ∀ {Y W : Scheme.{0}} (ι : Y ⟶ Z) (k : _ ⟶ W), fibMap p ι ≫ pullback.snd p (cpt A) ≫ k = pullback.snd (ι ≫ p) (cpt A) ≫ k := by
    intro Y W ι k
    rw [← Category.assoc, m2]
  have hr1 : (pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A)) ≫ ι₁ =
      (pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A)) ≫ ι₂ := by
    rw [Category.assoc, Category.assoc, ← m1, ← m1, ← Category.assoc, pullback.condition, Category.assoc]
  let r := pullback.lift _ _ hr1
  let c := pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.snd (ι₁ ≫ p) (cpt A)
  refine ⟨r, c, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have cond : pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ ≫ p = pullback.snd (ι₁ ≫ p) (cpt A) ≫ cpt A := by
    exact pullback.condition
  have w : r ≫ pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p = c ≫ cpt A := by
    simp only [r, c, pullback.lift_fst_assoc, Category.assoc, cond]
  have cond2 : pullback.fst ι₁ ι₂ ≫ ι₁ = pullback.snd ι₁ ι₂ ≫ ι₂ := pullback.condition
  have L : ∀ (s : PullbackCone (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) (cpt A)),
      ∃ l : s.pt ⟶ pullback (fibMap p ι₁) (fibMap p ι₂), l ≫ r = s.fst ∧ l ≫ c = s.snd ∧
        ∀ m : s.pt ⟶ pullback (fibMap p ι₁) (fibMap p ι₂), m ≫ r = s.fst → m ≫ c = s.snd → m = l := by
    intro s
    have hs : s.fst ≫ pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p = s.snd ≫ cpt A := s.condition
    have hs1 : (s.fst ≫ pullback.fst ι₁ ι₂) ≫ ι₁ ≫ p = s.snd ≫ cpt A := by
      rw [Category.assoc]
      exact hs
    have hs2 : (s.fst ≫ pullback.snd ι₁ ι₂) ≫ ι₂ ≫ p = s.snd ≫ cpt A := by
      rw [Category.assoc, ← Category.assoc (pullback.snd ι₁ ι₂), ← cond2, Category.assoc]
      exact hs
    let x₁ := pullback.lift _ _ hs1
    let x₂ := pullback.lift _ _ hs2
    have hx : x₁ ≫ fibMap p ι₁ = x₂ ≫ fibMap p ι₂ := by
      apply pullback.hom_ext
      · simp only [x₁, x₂, Category.assoc, m1, pullback.lift_fst_assoc, cond2]
      · simp only [x₁, x₂, Category.assoc, m2, pullback.lift_snd]
    refine ⟨pullback.lift x₁ x₂ hx, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp only [r, x₁, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [r, x₂, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst]
    · simp only [c, x₁, pullback.lift_fst_assoc, pullback.lift_snd]
    · intro m hm1 hm2
      have e1 : m ≫ pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) = s.fst ≫ pullback.fst ι₁ ι₂ := by
        rw [← hm1, Category.assoc, pullback.lift_fst]
      have e2 : m ≫ pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) = s.fst ≫ pullback.snd ι₁ ι₂ := by
        rw [← hm1, Category.assoc, pullback.lift_snd]
      have e3 : m ≫ pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.snd (ι₁ ≫ p) (cpt A) = s.snd := hm2
      have e4 : m ≫ pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.snd (ι₂ ≫ p) (cpt A) = s.snd := by
        rw [← m2 ι₂, ← pullback.condition_assoc, m2 ι₁]
        exact e3
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, x₁, e1]
        · simp only [Category.assoc, pullback.lift_fst, x₁, e3, pullback.lift_snd]
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_snd, x₂, e2, pullback.lift_fst]
        · simp only [Category.assoc, pullback.lift_snd, x₂, e4]
  choose l hl1 hl2 hl3 using L
  exact IsPullback.of_isLimit (c := PullbackCone.mk r c w)
    (PullbackCone.IsLimit.mk w l hl1 hl2 (fun s m h1 h2 => hl3 s m h1 h2))

end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.SchemeRootsOfUnityEqLocallyConstantPowers

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

theorem UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers :
    ∀ (X : Scheme.{0}) [IsAffine X] (q : ℕ) [NeZero q] (ζ : Γ(X, ⊤)), GoodRoot q ζ →
      (∀ g : LocallyConstant X (ZMod q), ∃ w : Γ(X, ⊤), w ^ q = 1 ∧ ∀ x : X, x ∉ X.basicOpen (w - ζ ^ (g x).val)) ∧
      (∀ w : Γ(X, ⊤), w ^ q = 1 → ∃ g : LocallyConstant X (ZMod q), ∀ x : X, x ∉ X.basicOpen (w - ζ ^ (g x).val)) ∧
      (∀ (a b : ZMod q) (x : X), x ∉ X.basicOpen (ζ ^ a.val - ζ ^ b.val) → a = b) ∧
      ∀ x : X, ∃ P : Ideal Γ(X, ⊤), ∀ f, f ∈ P ↔ x ∉ X.basicOpen f := by
  intro X _ q _ ζ hζ
  have hb : ∀ (x : X) (f : Γ(X, ⊤)), x ∉ X.basicOpen f ↔ f ∈ (X.toSpecΓ x).asIdeal := by
    intro x f
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact not_not
  let h := X.isoSpec.hom.homeomorph
  obtain ⟨h1, h2, h3⟩ := UpperTheory.roots_of_unity_eq_locallyConstant_powers_spectrum Γ(X, ⊤) q ζ hζ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨w, hwq, hw⟩ := h1 (LocallyConstant.comap ⟨h.symm, h.symm.continuous⟩ g)
    refine ⟨w, hwq, fun x => ?_⟩
    rw [hb]
    have hx := hw (h x)
    change w - ζ ^ (g (h.symm (h x))).val ∈ (h x).asIdeal at hx
    rw [h.symm_apply_apply] at hx
    exact hx
  · intro w hw
    obtain ⟨g, hg⟩ := h2 w hw
    refine ⟨LocallyConstant.comap ⟨h, h.continuous⟩ g, fun x => ?_⟩
    rw [hb]
    exact hg (h x)
  · intro a b x hx
    rw [hb] at hx
    exact h3 a b _ hx
  · intro x
    exact ⟨(X.toSpecΓ x).asIdeal, fun f => (hb x f).symm⟩

end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyPuncturedAffineLine

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

private theorem appTop_comp_apply {X Y W : Scheme.{0}} (h : Y ⟶ X) (f : X ⟶ W) (s : Γ(W, ⊤)) :
    h.appTop.hom (f.appTop.hom s) = (h ≫ f).appTop.hom s := by
  rw [Scheme.Hom.comp_appTop]
  rfl

private abbrev st {A : Type} [CommRing A] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom

private theorem st_comp {A : Type} [CommRing A] {X Y : Scheme.{0}} (h : Y ⟶ X) (f : X ⟶ Spec (CommRingCat.of A)) (a : A) :
    h.appTop.hom (st f a) = st (h ≫ f) a := by
  exact appTop_comp_apply h f _

private theorem goodRoot_map_ringHom {S S₂ : Type} [CommRing S] [CommRing S₂] (φ : S →+* S₂) {q : ℕ} {ζ : S}
    (h : GoodRoot q ζ) : GoodRoot q (φ ζ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [← map_pow, h1, map_one], fun a b hab => ?_, fun S' _ ψ x => ?_⟩
  · have := (h2 a b hab).map φ
    simpa only [map_sub, map_pow] using this
  · simpa using h3 S' (ψ.comp φ) x

private theorem notMem_basicOpen_pullback_iff_base_notMem_basicOpen {X Y : Scheme.{0}} (h : Y ⟶ X) (s : Γ(X, ⊤)) (y : Y) :
    y ∉ Y.basicOpen (h.appTop.hom s) ↔ h.base y ∉ X.basicOpen s := by
  rw [← Scheme.preimage_basicOpen_top]
  rfl

private theorem exists_preimage_map_eq_zero_of_mem_mm {A D E F : Type} [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D]
    [CommRing E] [CommRing F] (B : Subalgebra A D) (φ : E →+* D) (ψ : E →+* F) (σ : A →+* E)
    (hσ : ∀ a, algebraMap A D a = φ (σ a)) (hB : (B : Set D) = Set.range φ)
    (hψ : ∀ a ∈ maximalIdeal A, ψ (σ a) = 0) (y : D) (hy : y ∈ mm B) :
    ∃ y₀, φ y₀ = y ∧ ψ y₀ = 0 := by
  unfold mm at hy
  refine Submodule.smul_induction_on (p := fun y => ∃ y₀, φ y₀ = y ∧ ψ y₀ = 0) hy ?_ ?_
  · intro a ha b hb
    have hb' : b ∈ (B : Set D) := (Subalgebra.mem_toSubmodule B).1 hb
    rw [hB] at hb'
    obtain ⟨b₀, rfl⟩ := hb'
    exact ⟨σ a * b₀, by rw [map_mul, ← hσ, Algebra.smul_def], by rw [map_mul, hψ a ha, zero_mul]⟩
  · rintro x y ⟨x₀, rfl, hx0⟩ ⟨y₀, rfl, hy0⟩
    exact ⟨x₀ + y₀, map_add _ _ _, by rw [map_add (f := _), hx0, hy0, add_zero]⟩

private theorem pow_mod_eq_pow_of_pow_eq_one_commutative_algebra {S : Type} [CommRing S] {ζ : S} {q : ℕ} (h : ζ ^ q = 1) (n : ℕ) :
    ζ ^ (n % q) = ζ ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, h, one_pow, mul_one]

theorem UpperTheory.cohomology_punctured_affine_line : LateralTheory.E.StandardEtaleChartsMultivariableHensel.Heart := by
  unfold LateralTheory.E.StandardEtaleChartsMultivariableHensel.Heart
  intro q A _ _ hSH hq Z U V p hIL hZ ι₁ ι₂ h1 h2 hUa hVa hcov hs g
  obtain ⟨hHens, hsep⟩ := hSH
  letI := hHens
  haveI : NeZero q := ⟨fun h0 => by subst h0; simp at hq⟩
  obtain ⟨ζ, hζ⟩ := UpperTheory.exists_goodRoot_of_henselian_sepClosed_residue A q hq
  by_cases hW : Nonempty ↥(pullback (fibMap p ι₁) (fibMap p ι₂))
  swap
  · refine ⟨0, 0, ?_⟩
    ext x
    exact (hW ⟨x⟩).elim
  haveI := h1
  haveI := h2
  obtain ⟨r, c, hrc, hr1, hr2⟩ := UpperTheory.exists_fiber_pullback_square_of_open_immersions A p ι₁ ι₂
  obtain ⟨hPaff, hP⟩ := UpperTheory.isAffine_isDomain_pullback_standard_opens A p hZ ι₁ ι₂ hs
  haveI := hPaff
  obtain ⟨hWaff, hrsurj, hrker⟩ := UpperTheory.closed_fiber_affine_surjective_ker_maximalIdeal A (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) r c hrc
  haveI := hWaff
  obtain ⟨hdom, hinj1, hinj2, T, hTint, hTB, hTC, hB, hC⟩ := hP ⟨r.base hW.some⟩
  obtain ⟨hFUaff, -, hFUker⟩ := UpperTheory.closed_fiber_affine_surjective_ker_maximalIdeal A (ι₁ ≫ p) (pullback.fst (ι₁ ≫ p) (cpt A))
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  obtain ⟨hFVaff, -, hFVker⟩ := UpperTheory.closed_fiber_affine_surjective_ker_maximalIdeal A (ι₂ ≫ p) (pullback.fst (ι₂ ≫ p) (cpt A))
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  haveI := hFUaff
  haveI := hFVaff
  obtain ⟨ζW, hζW⟩ : ∃ z, st (r ≫ pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) ζ = z := ⟨_, rfl⟩
  have hgW : GoodRoot q ζW := hζW ▸ goodRoot_map_ringHom _ hζ
  have eqU : (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
      (st (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ ≫ p) ζ) = ζW := by
    rw [← hζW, st_comp, reassoc_of% hr1]
  have eqV : (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
      (st (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ ≫ p) ζ) = ζW := by
    rw [← hζW, st_comp, ← reassoc_of% hr2, pullback.condition_assoc]
  obtain ⟨w, hwq, hw⟩ := (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q ζW hgW).1 g
  obtain ⟨w', rfl⟩ := hrsurj w
  letI : Algebra A Γ(pullback ι₁ ι₂, ⊤) := (st (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p)).toAlgebra
  haveI := hdom
  have toKer : ∀ y, y ∈ mm (⊤ : Subalgebra A Γ(pullback ι₁ ι₂, ⊤)) → r.appTop.hom y = 0 := by
    intro y hy
    unfold mm at hy
    rw [Algebra.top_toSubmodule, Ideal.smul_top_eq_map] at hy
    rw [← RingHom.mem_ker, hrker]
    exact hy
  have hmem : w' ^ q - 1 ∈ mm (⊤ : Subalgebra A Γ(pullback ι₁ ι₂, ⊤)) := by
    have hk : w' ^ q - 1 ∈ RingHom.ker r.appTop.hom := by
      rw [RingHom.mem_ker, RingHom.map_sub, map_pow, hwq, map_one, sub_self]
    rw [hrker] at hk
    unfold mm
    rw [Algebra.top_toSubmodule, Ideal.smul_top_eq_map]
    exact hk
  obtain ⟨u, hu, v, hv, huq, hvq, hwuv⟩ := UpperTheory.exists_near_root_of_unity_product_decomposition A Γ(pullback ι₁ ι₂, ⊤) T hTint hTB hTC q hq w' hmem
  have hu' : u ∈ (T.B : Set _) := hu
  rw [hB] at hu'
  obtain ⟨u₀, rfl⟩ := hu'
  have hv' : v ∈ (T.C : Set _) := hv
  rw [hC] at hv'
  obtain ⟨v₀, rfl⟩ := hv'
  obtain ⟨e₁, he₁, he₁0⟩ := exists_preimage_map_eq_zero_of_mem_mm T.B (pullback.fst ι₁ ι₂).appTop.hom
    (pullback.fst (ι₁ ≫ p) (cpt A)).appTop.hom (st (ι₁ ≫ p)) (fun a => (st_comp _ _ a).symm) hB
    (fun a ha => by rw [← RingHom.mem_ker, hFUker]; exact Ideal.mem_map_of_mem _ ha) _ huq
  have hcomp2 : ∀ a, algebraMap A Γ(pullback ι₁ ι₂, ⊤) a = (pullback.snd ι₁ ι₂).appTop.hom (st (ι₂ ≫ p) a) := by
    intro a
    rw [st_comp]
    show st (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) a = _
    rw [pullback.condition_assoc]
  obtain ⟨e₂, he₂, he₂0⟩ := exists_preimage_map_eq_zero_of_mem_mm T.C (pullback.snd ι₁ ι₂).appTop.hom
    (pullback.fst (ι₂ ≫ p) (cpt A)).appTop.hom (st (ι₂ ≫ p)) hcomp2 hC
    (fun a ha => by rw [← RingHom.mem_ker, hFVker]; exact Ideal.mem_map_of_mem _ ha) _ hvq
  have hu1 : ((pullback.fst (ι₁ ≫ p) (cpt A)).appTop.hom u₀) ^ q = 1 := by
    have : e₁ = u₀ ^ q - 1 := hinj1 (by rw [he₁, map_sub, map_pow, map_one])
    rw [this, map_sub, map_pow, map_one, sub_eq_zero] at he₁0
    exact he₁0
  have hv1 : ((pullback.fst (ι₂ ≫ p) (cpt A)).appTop.hom v₀) ^ q = 1 := by
    have : e₂ = v₀ ^ q - 1 := hinj2 (by rw [he₂, map_sub, map_pow, map_one])
    rw [this, map_sub, map_pow, map_one, sub_eq_zero] at he₂0
    exact he₂0
  obtain ⟨a', ha'⟩ := (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q _ (goodRoot_map_ringHom (st (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ ≫ p)) hζ)).2.1 _ hu1
  obtain ⟨b', hb'⟩ := (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q _ (goodRoot_map_ringHom (st (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ ≫ p)) hζ)).2.1 _ hv1
  refine ⟨a', -b', ?_⟩
  ext x
  have key : g x = a' ((pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base x)
      + b' ((pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base x) := by
    obtain ⟨Px, hPx⟩ := (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q ζW hgW).2.2.2 x
    have hx1 : Ideal.Quotient.mk Px (r.appTop.hom w') = Ideal.Quotient.mk Px (ζW ^ (g x).val) :=
      Ideal.Quotient.eq.2 ((hPx _).2 (hw x))
    have hx2 : r.appTop.hom w' = (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
        ((pullback.fst (ι₁ ≫ p) (cpt A)).appTop.hom u₀) *
        (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
        ((pullback.fst (ι₂ ≫ p) (cpt A)).appTop.hom v₀) := by
      have h0 := toKer _ hwuv
      rw [map_sub, sub_eq_zero, map_mul] at h0
      rw [h0]
      simp only [appTop_comp_apply, hr1, hr2]
    have hx3 : Ideal.Quotient.mk Px ((pullback.fst (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
        ((pullback.fst (ι₁ ≫ p) (cpt A)).appTop.hom u₀)) =
        Ideal.Quotient.mk Px (ζW ^ (a' ((pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base x)).val) := by
      refine Ideal.Quotient.eq.2 ((hPx _).2 ?_)
      rw [← eqU, ← map_pow, ← map_sub, notMem_basicOpen_pullback_iff_base_notMem_basicOpen]
      exact ha' _
    have hx4 : Ideal.Quotient.mk Px ((pullback.snd (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
        ((pullback.fst (ι₂ ≫ p) (cpt A)).appTop.hom v₀)) =
        Ideal.Quotient.mk Px (ζW ^ (b' ((pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base x)).val) := by
      refine Ideal.Quotient.eq.2 ((hPx _).2 ?_)
      rw [← eqV, ← map_pow, ← map_sub, notMem_basicOpen_pullback_iff_base_notMem_basicOpen]
      exact hb' _
    have hfin : Ideal.Quotient.mk Px (ζW ^ (g x).val) = Ideal.Quotient.mk Px (ζW ^ (a' ((pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base x)
        + b' ((pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base x)).val) := by
      rw [← hx1, hx2, map_mul, hx3, hx4, ← map_mul, ← pow_add, ZMod.val_add, pow_mod_eq_pow_of_pow_eq_one_commutative_algebra hgW.1]
    exact (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q ζW hgW).2.2.1 _ _ x ((hPx _).1 (Ideal.Quotient.eq.1 hfin))
  simp only [LocallyConstant.sub_apply, LocallyConstant.neg_apply, LocallyConstant.coe_comap,
    Function.comp_apply, key, sub_neg_eq_add]

end
end
end
