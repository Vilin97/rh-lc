module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalOneCochainsBaseChangeBijectiveFiniteCategor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalTwoCochainsFiniteCategoryBaseChangeBijectivStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamTotalDifferentialOneFunctionPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiPiBijective

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestSide

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerFlat

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (Z : Type) [AddCommGroup Z] [Module R Z] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (Z' : Type) [AddCommGroup Z'] [Module R' Z'] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M') (fN : N →ₛₗ[algebraMap R R'] N'), Function.Injective i → Function.Exact i d → Function.Injective i' → Function.Exact i' d' → (∀ z, i' (fZ z) = fM (i z)) → (∀ x, d' (fM x) = fN (d x)) → Function.Bijective (liftSemi fM) → Function.Injective (liftSemi fN) → Function.Bijective (liftSemi fZ) := by
  intro R R' _ _ _ _ Z _ _ M _ _ N _ _ Z' _ _ M' _ _ N' _ _ i d i' d' fZ fM fN hi hid hi' hid' ci cd hM hN
  have c1 : ∀ x : R' ⊗[R] Z, i' (liftSemi fZ x) = liftSemi fM (LinearMap.lTensor R' i x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r z => simp only [liftSemi_tmul, LinearMap.lTensor_tmul, map_smul, ci]
  have c2 : ∀ x : R' ⊗[R] M, d' (liftSemi fM x) = liftSemi fN (LinearMap.lTensor R' d x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r m => simp only [liftSemi_tmul, LinearMap.lTensor_tmul, map_smul, cd]
  have hiB : Function.Injective (LinearMap.lTensor R' i) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hex : Function.Exact (LinearMap.lTensor R' i) (LinearMap.lTensor R' d) :=
    Module.Flat.lTensor_exact R' hid
  refine ⟨fun x y hxy => hiB (hM.1 ?_), fun z' => ?_⟩
  · rw [← c1, ← c1, hxy]
  · obtain ⟨y, hy⟩ := hM.2 (i' z')
    have h0 : LinearMap.lTensor R' d y = 0 := by
      apply hN
      rw [← c2, hy, map_zero]
      exact (hid' (i' z')).2 ⟨z', rfl⟩
    obtain ⟨x, rfl⟩ := (hex y).1 h0
    exact ⟨x, hi' (by rw [c1, hy])⟩

end GlobalTheory.KerFlat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiBijectiveOfExactCokernel

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_bijective_of_exact_cokernel : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (N : Type) [AddCommGroup N] [Module R N] (Z : Type) [AddCommGroup Z] [Module R Z] (Q : Type) [AddCommGroup Q] [Module R Q] (N' : Type) [AddCommGroup N'] [Module R' N'] (Z' : Type) [AddCommGroup Z'] [Module R' Z'] (Q' : Type) [AddCommGroup Q'] [Module R' Q'] (d : N →ₗ[R] Z) (p : Z →ₗ[R] Q) (d' : N' →ₗ[R'] Z') (p' : Z' →ₗ[R'] Q') (fN : N →ₛₗ[algebraMap R R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fQ : Q →ₛₗ[algebraMap R R'] Q'), Function.Exact d p → Function.Surjective p → Function.Exact d' p' → Function.Surjective p' → (∀ x, d' (fN x) = fZ (d x)) → (∀ z, p' (fZ z) = fQ (p z)) → Function.Surjective (liftSemi fN) → Function.Bijective (liftSemi fZ) → Function.Bijective (liftSemi fQ) := by
  intro R R' _ _ _ N _ _ Z _ _ Q _ _ N' _ _ Z' _ _ Q' _ _ d p d' p' fN fZ fQ hdp hp hdp' hp' sN sZ hN hZ
  have sqN : ∀ x, liftSemi fZ (d.lTensor R' x) = d' (liftSemi fN x) := by
    intro x
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r n => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, sN]
  have sqZ : ∀ z, liftSemi fQ (p.lTensor R' z) = p' (liftSemi fZ z) := by
    intro z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r n => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, sZ]
  have ex : Function.Exact (d.lTensor R') (p.lTensor R') := lTensor_exact R' hdp hp
  have ps : Function.Surjective (p.lTensor R') := LinearMap.lTensor_surjective R' hp
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := ps y
    rw [sqZ] at hy
    obtain ⟨x', hx'⟩ := (hdp' (liftSemi fZ z)).1 hy
    obtain ⟨x, rfl⟩ := hN x'
    have : d.lTensor R' x = z := hZ.1 (by rw [sqN, hx'])
    rw [← this]
    exact (ex _).2 ⟨x, rfl⟩
  · intro q'
    obtain ⟨z', rfl⟩ := hp' q'
    obtain ⟨z, rfl⟩ := hZ.2 z'
    exact ⟨p.lTensor R' z, sqZ z⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalOneCochainsBaseChangeBijectiveFiniteCategorStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.totalOneCochains_baseChange_bijective_finiteCategory : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  first | exact @GlobalTheory.liftSemi_pullTot1_bijective | exact GlobalTheory.liftSemi_pullTot1_bijective | (intros; apply GlobalTheory.liftSemi_pullTot1_bijective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalZeroCochainsFiniteCategoryBaseChangeBijecti

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem totalZeroCochains_finiteCategory_baseChange_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → ∀ g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F', (∀ x T, g x T = α T (x T)) → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ C _ _ _ F F' α _ hs hb g hg
  let f : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T =>
    { toFun := α T
      map_add' := fun a b => map_add (α T) a b
      map_smul' := fun r b => hs T r b }
  exact liftSemi_pi_bijective R R' C (fun T => F.obj T) (fun T => F'.obj T) f g
    (fun x T => hg x T) (fun T => hb T (f T) (fun _ => rfl))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalZeroCochainsFiniteCategoryBaseChangeBijectiStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.bijective_liftSemi_tot0_of_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → ∀ g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F', (∀ x T, g x T = α T (x T)) → Function.Bijective (liftSemi g) := by
  first | exact @GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective | exact GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective | (intros; apply GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHypercohomologyOneBaseChangeFlatBijective

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_pullHyp1_bijective_of_finite : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullHyp1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ _ C _ _ _ F F' α hn hs hb
  let m : CoefMap (algebraMap R R') F F' := ⟨𝟭 C, α, hn, hs⟩
  let g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F' :=
    { toFun := fun x T ↦ α T (x T)
      map_add' := fun x y ↦ funext fun T ↦ map_add (α T) (x T) (y T)
      map_smul' := fun r x ↦ funext fun T ↦ hs T r (x T) }
  have h0 : Function.Bijective (liftSemi g) :=
    GlobalTheory.T.bijective_liftSemi_tot0_of_bijective R R' C F F' α hn hs hb g fun _ _ ↦ rfl
  have h1 : Function.Bijective (liftSemi (pullTot1 m)) := GlobalTheory.T.totalOneCochains_baseChange_bijective_finiteCategory R R' C F F' α hn hs hb
  have h2 : Function.Bijective (liftSemi (pullTot2 m)) := GlobalTheory.T.totalTwoCochains_finiteCategory_baseChange_bijective R R' C F F' α hn hs hb
  have hZ : Function.Bijective (liftSemi (pullZZ1 m)) :=
    GlobalTheory.KerFlat.main R R' (cechDeRhamTotalCocyclesOne F) (Tot1 F) (Tot2 F) (cechDeRhamTotalCocyclesOne F') (Tot1 F') (Tot2 F')
      (cechDeRhamTotalCocyclesOne F).subtype (dTot1 F) (cechDeRhamTotalCocyclesOne F').subtype (dTot1 F') (pullZZ1 m) (pullTot1 m) (pullTot2 m)
      (cechDeRhamTotalCocyclesOne F).injective_subtype (LinearMap.exact_subtype_ker_map (dTot1 F))
      (cechDeRhamTotalCocyclesOne F').injective_subtype (LinearMap.exact_subtype_ker_map (dTot1 F'))
      (fun _ ↦ rfl) (fun x ↦ (pullTot2_dTot1 m x).symm) h1 h2.1
  exact GlobalTheory.liftSemi_bijective_of_exact_cokernel R R' (Tot0 F) (cechDeRhamTotalCocyclesOne F) (Hyp1 F) (Tot0 F') (cechDeRhamTotalCocyclesOne F') (Hyp1 F')
    ((dTot0 F).codRestrict (cechDeRhamTotalCocyclesOne F) (dTot0_mem F)) (Hyp1.mk F)
    ((dTot0 F').codRestrict (cechDeRhamTotalCocyclesOne F') (dTot0_mem F')) (Hyp1.mk F') g (pullZZ1 m) (pullHyp1 m)
    (LinearMap.exact_map_mkQ_range _) (Hyp1.mk_surjective F)
    (LinearMap.exact_map_mkQ_range _) (Hyp1.mk_surjective F')
    (fun x ↦ Subtype.ext (pullTot1_dTot0 m x).symm) (fun z ↦ (pullHyp1_mk m z).symm) h0.2 hZ

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHypercohomologyOneBaseChangeFlatBijectiveStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deRhamHypercohomologyOne_baseChange_flat_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullHyp1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  first | exact @GlobalTheory.liftSemi_pullHyp1_bijective_of_finite | exact GlobalTheory.liftSemi_pullHyp1_bijective_of_finite | (intros; apply GlobalTheory.liftSemi_pullHyp1_bijective_of_finite <;> assumption)
end
end
