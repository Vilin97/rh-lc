module

public import ReciprocityTheory.DualLattices.TowerZeroSurjective
public import ReciprocityTheory.DualLattices.LinPairStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.SubMemOfCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.DualLattices.SqZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextValAxioms
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawCommutativityValue
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawProduct
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsBXOfFactorSystems
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCompatibleBasis
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GrpPullbackSquareProductLift
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantGeneratorDescendsMulN
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ModPToValuationResidueFieldSurjective
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MulEqZeroOfSqZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NonemptyIsBiextOfCubeGen
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PairingNondegenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsDivisibleAndTorsionOfValuationIntegers
public import ReciprocityTheory.DualLattices.SqZeroOfSpan
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ProdCocycleMul
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorsionInvariantDescendsFibre
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TransportRightSmulFrame
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextPairingNondegenerateGeometricFibre

section

@[expose] public section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem biext_pairing_nondegenerate_geometric_fibre :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (X : Scheme.{0}) (M : ReciprocityTheory.ChartRestriction.G.Semi.LB X), M.IsLB → ∀ (ψ : (G ⊗ Over.mk f).left ⟶ X)
      (σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb M (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ ψ) (fun _ => 1))), σ.IsGen →
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ X) → M.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good M z J →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) → ∃ t : (M.pull ψ).Gen, t.IsGen) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ) (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (x : Over.mk f ⟶ G), x ^ N = 1 →
    ∃ σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left) (fun _ => 1)), σ.IsGen ∧
      ∀ y : Over.mk f ⟶ G, y ^ N = 1 → (∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
        ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom →
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    (∀ x : Over.mk f ⟶ G, (∃ t : (P.pull (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : Over.mk f ⟶ G, x ^ N = 1 → (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
      ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) → x = 1) := by
  intro hD hS S G _ _ P β K _ _ f N hN hsm hfin hfl hsur hpr x hx hxy
  obtain ⟨σ, hσ, hinv⟩ := hS S G K f N P β x hx
  exact hpr x (hD S G K f N hN hsm hfin hfl hsur _ P β.isLB _ σ hσ
    (fun y hy => hinv y hy (hxy y hy)))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsFibreProduct

section

@[expose] public section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem bxFibre_exists_chart {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {P : Type}
    [CommRing P] [IsLocalRing P] (x : Spec (CommRingCat.of P) ⟶ Y)
    (h : x (closedPoint P) ∈ U) :
    ∃ φ : Γ(Y, U) →+* P, x = Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec := by
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
    have hsp : (p : PrimeSpectrum P) ⤳ closedPoint P :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum P).isPrime.ne_top)
    exact hsp.mem_open (x ⁻¹ᵁ U).isOpen h
  refine ⟨(x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU
    (isAffineOpen_top (Spec (CommRingCat.of P))) hx
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem bxFibre_closed {Y : Scheme.{0}} {P Q : Type} [CommRing P] [IsLocalRing P] [CommRing Q]
    [IsLocalRing Q] (f : P →+* Q) [IsLocalHom f] (x : Spec (CommRingCat.of P) ⟶ Y) :
    (Spec.map (CommRingCat.ofHom f) ≫ x) (closedPoint Q) = x (closedPoint P) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun y => x y) ?_)
  exact IsLocalRing.comap_closedPoint f

theorem bxFibre_comp {Y : Scheme.{0}} {A P Q : Type} [CommRing A] [CommRing P] [CommRing Q]
    (φ : A →+* P) (f : P →+* Q) (g : Spec (CommRingCat.of A) ⟶ Y) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom φ) ≫ g =
      Spec.map (CommRingCat.ofHom (f.comp φ)) ≫ g := by
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem bxFibre_inj {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {P : Type}
    [CommRing P] {φ ψ : Γ(Y, U) →+* P}
    (h : Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) : φ = ψ := by
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem bxFibre_affine {Y : Scheme.{0}} (y : Y) : ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  exact ⟨U, hU, hmem⟩

theorem bxFibre_unique {Y : Scheme.{0}} {F P Q : Type} [CommRing F] [IsLocalRing F] [CommRing P]
    [IsLocalRing P] [CommRing Q] (p : F →+* P) [IsLocalHom p] (q : F →+* Q)
    (hinj : ∀ s t, p s = p t → q s = q t → s = t) (c c' : Spec (CommRingCat.of F) ⟶ Y)
    (hp : Spec.map (CommRingCat.ofHom p) ≫ c = Spec.map (CommRingCat.ofHom p) ≫ c')
    (hq : Spec.map (CommRingCat.ofHom q) ≫ c = Spec.map (CommRingCat.ofHom q) ≫ c') :
    c = c' := by
  obtain ⟨U, hU, hmem⟩ := bxFibre_affine (c (closedPoint F))
  have hmem' : c' (closedPoint F) ∈ U := by
    rw [← bxFibre_closed p c', ← hp, bxFibre_closed p c]
    exact hmem
  obtain ⟨φ, hφ⟩ := bxFibre_exists_chart hU c hmem
  obtain ⟨ψ, hψ⟩ := bxFibre_exists_chart hU c' hmem'
  rw [hφ, hψ] at hp hq ⊢
  have h1 : p.comp φ = p.comp ψ := bxFibre_inj hU
    ((bxFibre_comp φ p hU.fromSpec).symm.trans (hp.trans (bxFibre_comp ψ p hU.fromSpec)))
  have h2 : q.comp φ = q.comp ψ := bxFibre_inj hU
    ((bxFibre_comp φ q hU.fromSpec).symm.trans (hq.trans (bxFibre_comp ψ q hU.fromSpec)))
  have : φ = ψ := RingHom.ext fun s =>
    hinj _ _ (RingHom.congr_fun h1 s) (RingHom.congr_fun h2 s)
  rw [this]

theorem bxFibre_exists {Y : Scheme.{0}} {F P Q R : Type} [CommRing F] [CommRing P]
    [IsLocalRing P] [CommRing Q] [IsLocalRing Q] [CommRing R] [IsLocalRing R]
    (p : F →+* P) (q : F →+* Q) (f : P →+* R) [IsLocalHom f] (g : Q →+* R) [IsLocalHom g]
    (hex : ∀ a b, f a = g b → ∃! c, p c = a ∧ q c = b)
    (hinj : ∀ s t, p s = p t → q s = q t → s = t)
    (a : Spec (CommRingCat.of P) ⟶ Y) (b : Spec (CommRingCat.of Q) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom f) ≫ a = Spec.map (CommRingCat.ofHom g) ≫ b) :
    ∃ c : Spec (CommRingCat.of F) ⟶ Y, Spec.map (CommRingCat.ofHom p) ≫ c = a ∧
      Spec.map (CommRingCat.ofHom q) ≫ c = b := by
  obtain ⟨U, hU, hmem⟩ := bxFibre_affine (a (closedPoint P))
  have hmem' : b (closedPoint Q) ∈ U := by
    rw [← bxFibre_closed g b, ← h, bxFibre_closed f a]
    exact hmem
  obtain ⟨φ, hφ⟩ := bxFibre_exists_chart hU a hmem
  obtain ⟨ψ, hψ⟩ := bxFibre_exists_chart hU b hmem'
  rw [hφ, hψ] at h ⊢
  erw [bxFibre_comp, bxFibre_comp] at h
  have h1 := bxFibre_inj hU h
  have h2 : ∀ s, ∃ c, p c = φ s ∧ q c = ψ s := fun s =>
    (hex _ _ (RingHom.congr_fun h1 s)).exists
  choose k hk hk' using h2
  let χ : Γ(Y, U) →+* F :=
    { toFun := k
      map_one' := hinj _ _ (by simp [hk]) (by simp [hk'])
      map_mul' := fun s t => hinj _ _ (by simp [hk]) (by simp [hk'])
      map_zero' := hinj _ _ (by simp [hk]) (by simp [hk'])
      map_add' := fun s t => hinj _ _ (by simp [hk]) (by simp [hk']) }
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec, ?_, ?_⟩
  · erw [bxFibre_comp]
    have : p.comp χ = φ := RingHom.ext hk
    rw [this]
  · erw [bxFibre_comp]
    have : q.comp χ = ψ := RingHom.ext hk'
    rw [this]

theorem points_fibre_product :
  (∀ {R₀ : Type} [CommRing R₀] (X : Over (Spec (CommRingCat.of R₀))) {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R) (f₂ : LHom R₂ R),
    IsFibreSq p₁ p₂ f₁ f₂ → ∀ (a : sp (R₀ := R₀) (R₁ : Type) ⟶ X) (b : sp (R₀ := R₀) (R₂ : Type) ⟶ X), spMap f₁.1 ≫ a = spMap f₂.1 ≫ b →
    ∃! c : sp (R₀ := R₀) (F : Type) ⟶ X, spMap p₁.1 ≫ c = a ∧ spMap p₂.1 ≫ c = b) := by
  intro R₀ _ X F R₁ R₂ R p₁ p₂ f₁ f₂ hsq a b hab
  obtain ⟨hc, -, -, hex⟩ := hsq
  haveI : IsLocalHom p₁.1.toRingHom := p₁.2
  haveI : IsLocalHom f₁.1.toRingHom := f₁.2
  haveI : IsLocalHom f₂.1.toRingHom := f₂.2
  have hinj : ∀ s t, p₁.1.toRingHom s = p₁.1.toRingHom t → p₂.1.toRingHom s = p₂.1.toRingHom t →
      s = t := fun s t h1 h2 =>
    (hex (p₁.1 t) (p₂.1 t) (AlgHom.congr_fun hc t)).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩
  obtain ⟨c, h1, h2⟩ := bxFibre_exists (Y := X.left) p₁.1.toRingHom p₂.1.toRingHom
    f₁.1.toRingHom f₂.1.toRingHom hex hinj a.left b.left (congrArg (·.left) hab)
  have hw : c ≫ X.hom = (sp (R₀ := R₀) (F : Type)).hom := by
    refine bxFibre_unique p₁.1.toRingHom p₂.1.toRingHom hinj _ _ ?_ ?_
    · rw [← Category.assoc, h1]
      exact (Over.w a).trans (Over.w (spMap p₁.1)).symm
    · rw [← Category.assoc, h2]
      exact (Over.w b).trans (Over.w (spMap p₂.1)).symm
  refine ⟨Over.homMk c hw, ⟨Over.OverMorphism.ext h1, Over.OverMorphism.ext h2⟩, ?_⟩
  rintro c' ⟨k1, k2⟩
  apply Over.OverMorphism.ext
  exact bxFibre_unique (Y := X.left) p₁.1.toRingHom p₂.1.toRingHom hinj _ _
    ((congrArg (·.left) k1).trans h1.symm) ((congrArg (·.left) k2).trans h2.symm)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPeriodTowerDatumOfAbelianSchemeSymmetricBu

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianPeriodDatum

section SlopeTestRemainingChoices

variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {B : BX R₀}
  {e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)}

private theorem e_zero (hm : ∀ R x y, e R (x + y) = e R x * e R y) (R : LAlg R₀) : e R 0 = 1 := by
  have h := hm R 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

private theorem e_nsmul (hm : ∀ R x y, e R (x + y) = e R x * e R y) (R : LAlg R₀) (n : ℕ) (x : B.G R) :
    e R (n • x) = e R x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, e_zero hm]
  | succ n ih => rw [succ_nsmul, hm, ih, pow_succ]

private theorem divisible_and_card [IsCommMonObj G] (hb : ∀ R, Function.Bijective (e R))
    (hm : ∀ R x y, e R (x + y) = e R x * e R y) (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ)
    (hv : v.Integers (O : Type)) (hf : IsFinite ((𝟙 G) ^ p : G ⟶ G).left) (hs : Surjective ((𝟙 G) ^ p : G ⟶ G).left) :
    (∀ x : B.G O, ∃ y, p • y = x) ∧
      Nat.card {x : B.G O // p • x = 0} = Nat.card {z : sp (R₀ := R₀) C ⟶ G // z ^ p = 1} := by
  obtain ⟨h₁, h₂⟩ := GlobalTheory.points_divisible_and_torsion_of_valuation_integers G O C v p hv hf hs
  have tors : ∀ x : B.G O, p • x = 0 ↔ e O x ^ p = 1 := fun x => by
    rw [← e_nsmul hm, ← e_zero hm O]
    exact (hb O).1.eq_iff.symm
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := h₁ (e O x)
    obtain ⟨y, rfl⟩ := (hb O).2 y
    exact ⟨y, (hb O).1 ((e_nsmul hm O p y).trans hy)⟩
  · refine Nat.card_congr (Equiv.ofBijective
      (fun x => ⟨spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ e O x.1, ?_⟩) ⟨fun x y hxy => ?_, fun z => ?_⟩)
    · rw [← MonObj.comp_pow, (tors _).1 x.2, MonObj.comp_one]
    · have hxy' : spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ e O x.1 =
          spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ e O y.1 := congrArg Subtype.val hxy
      have hz : (spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ e O y.1) ^ p = 1 := by
        rw [← MonObj.comp_pow, (tors _).1 y.2, MonObj.comp_one]
      exact Subtype.ext ((hb O).1 ((h₂ _ hz).unique ⟨(tors _).1 x.2, hxy'⟩ ⟨(tors _).1 y.2, rfl⟩))
    · obtain ⟨y, ⟨hy, hy'⟩, -⟩ := h₂ z.1 z.2
      obtain ⟨y, rfl⟩ := (hb O).2 y
      exact ⟨⟨y, (tors y).2 hy⟩, Subtype.ext hy'⟩

private theorem ring_laws (hb : ∀ R, Function.Bijective (e R))
    (hm : ∀ R x y, e R (x + y) = e R x * e R y) (O : LAlg R₀)
    (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left)
    (gp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ)
    (O₀ : Type) [CommRing O₀] (cj : O₀ → O₀) (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct G' O₀) (Ad : O₀ → OAdj B O)
    (ha : ∀ a {R : LAlg R₀} (s : LHom O R) (x : B.G R)
      (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ ρ.act a).left ≫ φ = (e R ((Ad a).a.f s x)).left)
    (hab : ∀ a {R : LAlg R₀} (s : LHom O R) (x : B.G R)
      (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ ρ.act (cj a)).left ≫ φ = (e R ((Ad a).ab.f s x)).left) :
    (∀ a, (Ad a).ab = (Ad (cj a)).a) ∧
    (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (Ad 1).a.f s x = x ∧
      ∀ a b, (Ad (a + b)).a.f s x = (Ad a).a.f s x + (Ad b).a.f s x ∧
        (Ad (a * b)).a.f s x = (Ad a).a.f s ((Ad b).a.f s x)) := by
  choose E hE using fun (R : LAlg R₀) (s : LHom O R) => GlobalTheory.adjPoints gp _ _ (GlobalTheory.adjBase s)
  have hl : ∀ R s x, ((E R s).symm (e R x)).left ≫ φ = (e R x).left := fun R s x =>
    (hE R s _).symm.trans (congrArg (fun q => q.left) ((E R s).apply_symm_apply _))
  have inj : ∀ R (x y : B.G R), (e R x).left = (e R y).left → x = y := fun R x y h =>
    (hb R).1 (Over.OverMorphism.ext h)
  refine ⟨fun a => ?_, fun {R} s x => ⟨?_, fun a b => ⟨?_, ?_⟩⟩⟩
  · have h : ∀ {R : LAlg R₀} (s : LHom O R), (Ad a).ab.f s = (Ad (cj a)).a.f s := fun {R} s =>
      AddMonoidHom.ext fun x => inj R _ _ ((hab a s x _ (hl R s x)).symm.trans (ha (cj a) s x _ (hl R s x)))
    generalize (Ad a).ab = u at h
    generalize (Ad (cj a)).a = w at h
    obtain ⟨u, hu⟩ := u
    obtain ⟨w, hw⟩ := w
    obtain rfl : @u = @w := funext fun R => funext fun s => h s
    rfl
  · refine inj R _ _ ((ha 1 s x _ (hl R s x)).symm.trans ?_)
    rw [ρ.map_one, Category.comp_id]
    exact hl R s x
  · refine inj R _ _ ((ha (a + b) s x _ (hl R s x)).symm.trans ?_)
    have h₁ : e R ((Ad a).a.f s x) = E R s ((E R s).symm (e R x) ≫ ρ.act a) :=
      Over.OverMorphism.ext ((ha a s x _ (hl R s x)).symm.trans (hE R s _).symm)
    have h₂ : e R ((Ad b).a.f s x) = E R s ((E R s).symm (e R x) ≫ ρ.act b) :=
      Over.OverMorphism.ext ((ha b s x _ (hl R s x)).symm.trans (hE R s _).symm)
    have h₃ : (E R s).symm (e R x) ≫ ρ.act (a + b) =
        ((E R s).symm (e R x) ≫ ρ.act a) * ((E R s).symm (e R x) ≫ ρ.act b) := by
      rw [ρ.map_add]
      exact MonObj.comp_mul _ _ _
    rw [hm, h₁, h₂, h₃]
    exact (hE R s _).symm.trans (congrArg (fun q => q.left) (map_mul (E R s) _ _))
  · refine inj R _ _ ((ha (a * b) s x _ (hl R s x)).symm.trans ?_)
    rw [ρ.map_mul, ← Category.assoc]
    exact ha a s _ _ (ha b s x _ (hl R s x))

end SlopeTestRemainingChoices

theorem main : (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (g : ℕ) (G : Over (Spec (CommRingCat.of (Ainf.R0 p O ε)))) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left), ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → P.IsLB → (∃ θ : LB.Gen (Theta (G ⊗ G) P), θ.IsGen) → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso P (P.pull (lift (snd G G) (fst G G)).left) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left → ∀ [Algebra ((Ainf.ainfTowerL p O hv ε hε).O : Type) C] [Algebra (Ainf.R0 p O ε) C] [IsScalarTower (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type) C], v.Integers ((Ainf.ainfTowerL p O hv ε hε).O : Type) → (∀ x : sp (R₀ := (Ainf.R0 p O ε)) C ⟶ G, (∃ t : (P.pull (lift (snd G (sp (R₀ := (Ainf.R0 p O ε)) C) ≫ x) (fst G (sp (R₀ := (Ainf.R0 p O ε)) C))).left).Gen, t.IsGen) → x = 1) → Nat.card {z : sp (R₀ := (Ainf.R0 p O ε)) C ⟶ G // z ^ p = 1} = p ^ (2 * g) → ∀ (G' : Over (Spec (CommRingCat.of ((Ainf.ainfTowerL p O hv ε hε).O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left), ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme G' → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type)))) φ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ φ₂ → ∀ [Algebra ℤ_[p] ((Ainf.ainfTowerL p O hv ε hε).O : Type)] (O₀ : Type) [CommRing O₀] (cj : O₀ ≃ₐ[ℤ] O₀) (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct G' O₀), (∀ a, cj (cj a) = a) → (∀ a, (∃ t : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := Fin 2) ![(lift (fst G' G' ≫ ρ.act a) (snd G' G')).left ≫ φ₂, (lift (fst G' G') (snd G' G' ≫ ρ.act (cj a))).left ≫ φ₂] ![1, -1]), t.IsGen)) → ∃ (B : BX (Ainf.R0 p O ε)) (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)) (Ad : O₀ → OAdj B (Ainf.ainfTowerL p O hv ε hε).O), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧ (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) ∧ (∀ a, (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ ρ.act a).left ≫ φ = (e R ((Ad a).a.f s x)).left)) ∧ ∃ (Dt : DualTower (Ainf.ainfTowerL p O hv ε hε)) (D : Dat p g B (Ainf.ainfTowerL p O hv ε hε) Dt (ℤ_[p] ⊗[ℤ] O₀) (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) (Ainf.ainfTowerL p O hv ε hε).c), D.H.P = 0 ∧ D.H.PL = 0 ∧ (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) → (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧ ∀ a j n, (Ad a).a.f (LHom.id (Ainf.ainfTowerL p O hv ε hε).O) (D.L.τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k n) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε g G _ _ P hA hsm hP hθ h1 h2 hsym hf hfl hsu _ _ _ hvi hnd hcard
    G' _ _ φ φ₂ hA' gp sq _ O₀ _ cj ρ hcj hros
  haveI : IsLocalRing (Ainf.R0 p O ε) := GlobalTheory.WdAinf.ainf_thetaQuotRing_isLocalRing p O hv ε hε
  obtain ⟨β⟩ := GlobalTheory.nonempty_isBiext_of_cube_gen _ G hA P hP hθ h1 h2
  obtain ⟨s, hs⟩ := GlobalTheory.BiextSym.main GlobalTheory.globalFns_holds _ G hA P β hsym
  obtain ⟨B, e, hb, hm, hn, b, J, hJ, ha1, ha2⟩ := @GlobalTheory.BXOf.main
    (@GlobalTheory.GroupPointsBX.main (@GlobalTheory.NilCoord.nilpotent_coordinates) (@GlobalTheory.points_fibre_product))
    (@GlobalTheory.exists_BX_of_factorSystems) _ _ G _ _ _ g hsm P β s hs
  have hAd := fun a : O₀ => @GlobalTheory.exists_oAdj_of_rosatiAdjoint (@GlobalTheory.bx_frame_pairing_adj) GlobalTheory.biext_val_axioms
    GlobalTheory.globalFns_holds _ _ G _ _ P β B e b J hb hm hn hJ ha1 ha2 (Ainf.ainfTowerL p O hv ε hε).O G' _ _ φ φ₂ hA' gp sq
    (ρ.act a) (ρ.act (cj a)) (ρ.hom a) (ρ.hom (cj a)) (hros a)
  choose Ad ha hab using hAd
  obtain ⟨hadj, hring⟩ := ring_laws hb hm _ G' φ gp O₀ cj ρ Ad ha hab
  obtain ⟨hdiv, hc⟩ := divisible_and_card hb hm (Ainf.ainfTowerL p O hv ε hε).O C v p hvi hf hsu
  have hsmooth : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  have hpair := @GlobalTheory.pairing_nondegenerate_integral_torsion (@GlobalTheory.bx_frame_pairing_adj)
    (GlobalTheory.biext_pairing_nondegenerate_geometric_fibre
      (GlobalTheory.invariantGenerator_descends_mulN GlobalTheory.torsion_invariant_descends_fibre)
      (GlobalTheory.TorsionGen.main GlobalTheory.biext_val_axioms))
    (@GlobalTheory.points_divisible_and_torsion_of_valuation_integers) GlobalTheory.biext_val_axioms
    _ _ G _ _ P β B e b J hb hm hn hJ ha1 ha2 (Ainf.ainfTowerL p O hv ε hε).O C _ _ _ v _ _ _ p
    (Fact.out : p.Prime).ne_zero hvi hsmooth hf hfl hsu hnd
  exact ⟨B, e, Ad, hb, hm, hn, ha, GlobalTheory.PeriodDatum.main p O hv ε hε g G B e hb hm hn hsm hf hfl hdiv
    (hc.trans hcard) hpair O₀ cj Ad hadj hcj hring⟩

end GlobalTheory.AbelianPeriodDatum
end
end
